module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.GermCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IdempotentGluingCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineEtaleDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberNode
public import StacksFrontier.AlgebraicGeometry.Limits.GermOpensLimit
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiberSupplement
public import StacksFrontier.RingTheory.Etale.IndEtaleSeparablyClosed

/-!
# Cohomology over a separably closed point of a strict henselization: Tag 0EZV corrected

Let `f : X ⟶ S` be a morphism of schemes, let `x̄` be a geometric point of `X` with image `s̄` in
`S`, and let `k : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` be a point of the strict henselization of `S` at
`s̄` with `K` separably closed. For an abelian sheaf `ℱ` on the small étale site of `Spec K` and
`q ≥ 0`, Tag 0EZV asserts the equivalence of

1. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ)`,
2. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K, ℱ) = H^q(Spec K, ℱ)`,

each equality read as bijectivity of the canonical restriction map. The fibre products and the
morphism between them are set up in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiber`.

The two conditions do not have the same scope. The scheme `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is the
spectrum of a ring ind-étale over `K`, a profinite set of `K`-points, and these points are the
lifts `k' : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` of the composite `Spec K ⟶ S`, of which `k` is only one.
Condition (1) sees the fibres of `Spec(𝒪^{sh}_{X,x̄}) ⟶ Spec(𝒪^{sh}_{S,s̄})` over all of them,
condition (2) only the fibre over `k`, and the argument of the source shows that (1) holds if and
only if (2) holds at every lift `k'`. When the fibres over different lifts differ, (2) can hold
while (1) fails. This file proves that the equivalence fails as stated, by the following example.
Over an algebraically closed field of characteristic zero let `S` be the nodal cubic, `s̄` its
geometric point at the node and `X = Spec(𝒪^{sh}_{S,s̄}/(e))` for one of the two branches
`e = y - x √(1 + x)` of the node in its strict henselization. Two `K`-points of
`Spec(𝒪^{sh}_{S,s̄})` over the same point of `S`, one on the branch and one off it, have fibres
`Spec K` and `∅`; at the first, condition (2) holds for `q = 0` and `ℱ = ℤ` while condition (1)
fails.

## Main definitions

* `Stacks.EtaleCohomology.strictHenselizationBaseFiberIsoSpecFieldTensor`: the identification of
  `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` with `Spec(K ⊗_{𝒪_{S,s}} 𝒪^{sh}_{S,s̄})`, the field being the
  left factor as in `Stacks.EtaleCohomology.indEtale_strictHenselizationBaseFiberRing`.
* `Stacks.EtaleCohomology.strictHenselizationFiberCohomologyPullback`,
  `Stacks.EtaleCohomology.strictHenselizationPointCohomologyPullback`: the restriction maps of
  conditions (1) and (2), as `Stacks.EtaleCohomology.etaleCohomologyPullback` on abelian sheaves
  of the universe above that of the schemes.

## Main results

* `Stacks.EtaleCohomology.not_injective_strictHenselizationFiberCohomologyPullback_of_isEmpty`:
  the restriction map of condition (1) is not injective as soon as some `K`-point of
  `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` has empty fibre.
* `Stacks.EtaleCohomology.exists_bijective_pointRestriction_and_not_bijective_fiberRestriction`:
  the example above; condition (2) does not imply condition (1).
* `Stacks.EtaleCohomology.bijective_strictHenselizationFiberCohomologyPullback_iff`: **the
  corrected form of Tag 0EZV**, condition (1) holds if and only if condition (2) holds at every
  lift `k'` of `Spec K ⟶ S` to the strict henselization. The proof is the source's: the base
  fibre is the spectrum of a ring ind-étale over `K`, its points are the lifts `k'`, the
  cohomology of the base fibre and of `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K` is glued over the clopens
  cut out by idempotents, and the germs at a point are computed by Theorem 09YQ.

## Implementation notes

An equality of cohomology groups of the source is read as bijectivity of the canonical
restriction map `Stacks.EtaleCohomology.etaleCohomologyPullback` on the cohomology
`CategoryTheory.Sheaf.H` of the small étale site, with coefficients in abelian groups of the
universe above that of the schemes. The coefficient sheaf upstairs is accordingly the inverse
image along the comparison morphism of the coefficient sheaf downstairs, which is itself the
inverse image of `ℱ` along the projection to `Spec K`; the source writes `ℱ` for all four groups.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct

universe u v w

namespace Stacks.EtaleCohomology

/-! ### Fibre products over a monomorphism -/

section Mono

/-- A cartesian square over a composite with a monomorphism is cartesian over the original
maps: the monomorphism may be cancelled from the compatibility condition of a competing cone. -/
public theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y Z W : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {a : X ⟶ W} {b : Y ⟶ W} (sq : IsPullback fst snd a b) {a' : X ⟶ Z}
    {b' : Y ⟶ Z} (m : Z ⟶ W) [Mono m] (ha : a' ≫ m = a) (hb : b' ≫ m = b) :
    IsPullback fst snd a' b' where
  w := (cancel_mono m).mp (by rw [Category.assoc, Category.assoc, ha, hb, sq.w])
  isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => sq.lift s.fst s.snd
      (by rw [← ha, ← hb, ← Category.assoc, s.condition, Category.assoc]))
    (fun s => sq.lift_fst _ _ _) (fun s => sq.lift_snd _ _ _)
    (fun s t hfst hsnd => sq.hom_ext (by simpa using hfst) (by simpa using hsnd))⟩

end Mono

/-! ### The base fibre as the spectrum of a tensor product -/

section Fibers

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- The structure morphism of the point to the local scheme at `s` is the spectrum of the
`𝒪_{S,s}`-algebra structure of `K`. -/
public theorem specMap_algebraMap_sepClosedPoint :
    letI := sepClosedPointAlgebra B hS f x k
    Spec.map (CommRingCat.ofHom (algebraMap (stalkRingAtImage f x) K)) =
      k ≫ strictHenselizationToStalk B hS f x := by
  let := sepClosedPointAlgebra B hS f x k
  have halg : algebraMap (stalkRingAtImage f x) K =
      (Spec.preimage (k ≫ strictHenselizationToStalk B hS f x)).hom :=
    RingHom.algebraMap_toAlgebra _
  rw [halg, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The fibre product `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is the fibre product over the local scheme
at `s`. -/
public theorem isPullback_strictHenselizationBaseFiber_toStalk :
    IsPullback (pullback.fst (strictHenselizationToBase B S hS (x.map f))
        (sepClosedPointToBase B hS f x k))
      (pullback.snd (strictHenselizationToBase B S hS (x.map f)) (sepClosedPointToBase B hS f x k))
      (strictHenselizationToStalk B hS f x) (k ≫ strictHenselizationToStalk B hS f x) :=
  isPullback_of_comp_mono (IsPullback.of_hasPullback _ _)
    (S.fromSpecStalk ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))
    (strictHenselizationToStalk_comp B hS f x)
    (by rw [Category.assoc, strictHenselizationToStalk_comp])

/-- The spectrum of `K ⊗_{𝒪_{S,s}} 𝒪^{sh}_{S,s̄}` is the fibre product of `Spec K` and
`Spec(𝒪^{sh}_{S,s̄})` over the local scheme at `s`. -/
public theorem isPullback_spec_tensorProduct_toStalk :
    letI := sepClosedPointAlgebra B hS f x k
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (S := K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f)))
        Algebra.TensorProduct.includeRight.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (S := K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f)))
        Algebra.TensorProduct.includeLeftRingHom))
      (strictHenselizationToStalk B hS f x) (k ≫ strictHenselizationToStalk B hS f x) := by
  let := sepClosedPointAlgebra B hS f x k
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct
    (stalkRingAtImage f x) K ↥(etaleLocalRing B S hS (x.map f)))).flip
  rw [specMap_algebraMap_sepClosedPoint] at h
  exact h

/-- **`Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is the spectrum of `K ⊗_{𝒪_{S,s}} 𝒪^{sh}_{S,s̄}`.** By
`Stacks.EtaleCohomology.isAffine_strictHenselizationBaseFiber` the fibre product over `S` is the
fibre product over the affine local scheme at `s`, and a fibre product of affine schemes over an
affine scheme is the spectrum of the tensor product of their coordinate rings. -/
public def strictHenselizationBaseFiberIsoSpecFieldTensor :
    letI := sepClosedPointAlgebra B hS f x k
    strictHenselizationBaseFiber B hS f x k ≅
      Spec (CommRingCat.of (K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f)))) :=
  (isPullback_strictHenselizationBaseFiber_toStalk B hS f x k).isoIsPullback _ _
    (isPullback_spec_tensorProduct_toStalk B hS f x k)

/-- Under `Stacks.EtaleCohomology.strictHenselizationBaseFiberIsoSpecFieldTensor` the projection to
`Spec K` is the spectrum of the `K`-algebra structure. -/
@[reassoc]
public theorem strictHenselizationBaseFiberIsoSpecFieldTensor_hom_snd :
    letI := sepClosedPointAlgebra B hS f x k
    (strictHenselizationBaseFiberIsoSpecFieldTensor B hS f x k).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K
          (K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f))))) =
      pullback.snd (strictHenselizationToBase B S hS (x.map f))
        (sepClosedPointToBase B hS f x k) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end Fibers

/-! ### The two restriction maps on cohomology -/

section Restriction

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- The coefficient sheaf on `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`: the inverse image of an abelian
sheaf on the small étale site of `Spec K` along the projection. -/
public abbrev strictHenselizationBaseFiberCoeffAb
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) :
    Sheaf (strictHenselizationBaseFiber B hS f x k).smallEtaleTopology Ab.{u + 1} :=
  (smallEtalePullbackAb (pullback.snd (strictHenselizationToBase B S hS (x.map f))
    (sepClosedPointToBase B hS f x k))).obj F

/-- The canonical restriction map
`H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ)`, whose
bijectivity is condition (1) of Tag 0EZV. -/
public abbrev strictHenselizationFiberCohomologyPullback
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1} (strictHenselizationBaseFiberCoeffAb B hS f x k F) q →+
      Sheaf.H.{u + 1} ((smallEtalePullbackAb (strictHenselizationFiberMap B hX hS f x k)).obj
        (strictHenselizationBaseFiberCoeffAb B hS f x k F)) q :=
  etaleCohomologyPullback (strictHenselizationFiberMap B hX hS f x k) (𝟙 _) q

/-- The canonical restriction map
`H^q(Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K, ℱ)`, whose bijectivity
is condition (2) of Tag 0EZV. -/
public abbrev strictHenselizationPointCohomologyPullback
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1} F q →+
      Sheaf.H.{u + 1} ((smallEtalePullbackAb
        (pullback.snd (strictHenselizationSquareMap B hX hS f x) k)).obj F) q :=
  etaleCohomologyPullback (pullback.snd (strictHenselizationSquareMap B hX hS f x) k) (𝟙 _) q

end Restriction

/-! ### Sections of the base fibre and lifts of the point -/

section Lifts

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- **The fibre of `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K` over a section `t` of the base fibre is the
fibre of the morphism of strict henselizations over the point `t ≫ pr₁`.** -/
public theorem isPullback_strictHenselizationFiberMap_section
    (t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k) :
    IsPullback
      (pullback.fst (strictHenselizationFiberMap B hX hS f x k) t ≫
        pullback.fst (strictHenselizationToBase B X hX x ≫ f) (sepClosedPointToBase B hS f x k))
      (pullback.snd (strictHenselizationFiberMap B hX hS f x k) t)
      (strictHenselizationSquareMap B hX hS f x)
      (t ≫ pullback.fst (strictHenselizationToBase B S hS (x.map f))
        (sepClosedPointToBase B hS f x k)) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback _ t)
    (isPullback_strictHenselizationFiberMap B hX hS f x k)

/-- **Condition (2) at the point `t ≫ pr₁` read on the base fibre.** For a section `t` of the
projection `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K ⟶ Spec K`, condition (2) at the lift `t ≫ pr₁` of the
point is bijectivity of the restriction map to the fibre over `t` of
`Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`. -/
public theorem bijective_strictHenselizationPointCohomologyPullback_iff_of_section
    (t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k)
    (ht : t ≫ pullback.snd (strictHenselizationToBase B S hS (x.map f))
      (sepClosedPointToBase B hS f x k) = 𝟙 _)
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (strictHenselizationPointCohomologyPullback B hX hS f x
        (t ≫ pullback.fst (strictHenselizationToBase B S hS (x.map f))
          (sepClosedPointToBase B hS f x k)) F q) ↔
      Function.Bijective (etaleCohomologyPullback
        (pullback.snd (strictHenselizationFiberMap B hX hS f x k) t)
        (𝟙 ((smallEtalePullbackAb (pullback.snd (strictHenselizationFiberMap B hX hS f x k) t)).obj
          ((smallEtalePullbackAb t).obj
            (strictHenselizationBaseFiberCoeffAb B hS f x k F)))) q) := by
  have hP := isPullback_strictHenselizationFiberMap_section B hX hS f x k t
  exact bijective_etaleCohomologyPullback_iff_of_isIso _ _ hP.isoPullback.hom (𝟙 _)
    (by rw [IsPullback.isoPullback_hom_snd, Category.comp_id]) F
    ((smallEtalePullbackAbComp' t _ (𝟙 _) ht.symm).inv.app F) q

end Lifts

/-! ### The points of the base fibre -/

section Points

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- The coordinate ring `K ⊗_{𝒪_{S,s}} 𝒪^{sh}_{S,s̄}` of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`. -/
public abbrev baseFiberRing : Type u :=
  letI := sepClosedPointAlgebra B hS f x k
  K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f))

/-- The coordinate ring of the base fibre is a commutative ring, as a tensor product. -/
public instance : CommRing (baseFiberRing B hS f x k) :=
  letI := sepClosedPointAlgebra B hS f x k
  inferInstanceAs (CommRing (K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f))))

/-- The coordinate ring of the base fibre is a `K`-algebra through its left factor. -/
public instance : Algebra K (baseFiberRing B hS f x k) :=
  letI := sepClosedPointAlgebra B hS f x k
  inferInstanceAs (Algebra K (K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f))))

/-- The coordinate ring of the base fibre is ind-étale over `K`. -/
public theorem indEtale_baseFiberRing : StacksDraft.IndEtale K (baseFiberRing B hS f x k) :=
  indEtale_strictHenselizationBaseFiberRing B hS f x k

/-- The identification of the base fibre with the spectrum of its coordinate ring. -/
public abbrev baseFiberToSpec :
    strictHenselizationBaseFiber B hS f x k ⟶ Spec (CommRingCat.of (baseFiberRing B hS f x k)) :=
  (strictHenselizationBaseFiberIsoSpecFieldTensor B hS f x k).hom

/-- The identification of the base fibre with the spectrum of its coordinate ring, followed by
the structure map to `Spec K`, is the projection to `Spec K`. -/
@[reassoc]
public theorem baseFiberToSpec_algebraMap :
    baseFiberToSpec B hS f x k ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (baseFiberRing B hS f x k))) =
      pullback.snd (strictHenselizationToBase B S hS (x.map f))
        (sepClosedPointToBase B hS f x k) :=
  strictHenselizationBaseFiberIsoSpecFieldTensor_hom_snd B hS f x k

/-- The clopen of the base fibre cut out by an idempotent of its coordinate ring. -/
public abbrev baseFiberClopen (e : StacksDraft.IdempotentGluing.Idem (baseFiberRing B hS f x k)) :
    (strictHenselizationBaseFiber B hS f x k).Opens :=
  baseFiberToSpec B hS f x k ⁻¹ᵁ (Spec (CommRingCat.of (baseFiberRing B hS f x k))).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom e)

/-- A point of the base fibre lies in the clopen of an idempotent if and only if the idempotent
is outside the prime of the coordinate ring at that point. -/
public theorem mem_baseFiberClopen
    (e : StacksDraft.IdempotentGluing.Idem (baseFiberRing B hS f x k))
    (z : strictHenselizationBaseFiber B hS f x k) :
    z ∈ baseFiberClopen B hS f x k e ↔
      (e : baseFiberRing B hS f x k) ∉ ((baseFiberToSpec B hS f x k).base z).asIdeal := by
  change (baseFiberToSpec B hS f x k).base z ∈
    (Spec (CommRingCat.of (baseFiberRing B hS f x k))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv e) ↔ _
  rw [basicOpen_eq_of_affine]
  rfl

open StacksDraft.IdempotentGluing in
/-- The clopen cut out by an idempotent is monotone in the idempotent. -/
public theorem monotone_baseFiberClopen : Monotone (baseFiberClopen B hS f x k) :=
  IdempotentGluing.monotone_preimage (baseFiberToSpec B hS f x k)
    (IdempotentGluing.basicOpen_idemMap_mono
      (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom)

open StacksDraft.IdempotentGluing in
/-- The clopen cut out by the idempotent `0` is empty. -/
public theorem baseFiberClopen_bot : baseFiberClopen B hS f x k ⊥ = ⊥ :=
  (congrArg (baseFiberToSpec B hS f x k ⁻¹ᵁ ·) (IdempotentGluing.basicOpen_idemMap_bot
    (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom)).trans rfl

open StacksDraft.IdempotentGluing in
/-- The clopen cut out by the idempotent `1` is the whole base fibre. -/
public theorem baseFiberClopen_top : baseFiberClopen B hS f x k ⊤ = ⊤ :=
  (congrArg (baseFiberToSpec B hS f x k ⁻¹ᵁ ·) (IdempotentGluing.basicOpen_idemMap_top
    (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom)).trans rfl

open StacksDraft.IdempotentGluing in
/-- The clopens cut out by disjoint idempotents are disjoint. -/
public theorem baseFiberClopen_inf (e e' : Idem (baseFiberRing B hS f x k)) (h : Disjoint e e') :
    baseFiberClopen B hS f x k e ⊓ baseFiberClopen B hS f x k e' = ⊥ :=
  IdempotentGluing.preimage_inf (baseFiberToSpec B hS f x k)
    (IdempotentGluing.basicOpen_idemMap_inf
      (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom) e e' h

open StacksDraft.IdempotentGluing in
/-- The clopen cut out by the sum `e ⊔ e'` of disjoint idempotents is the union of the clopens
cut out by `e` and by `e'`. -/
public theorem baseFiberClopen_sup (e e' : Idem (baseFiberRing B hS f x k)) (h : Disjoint e e') :
    baseFiberClopen B hS f x k (e ⊔ e') =
      baseFiberClopen B hS f x k e ⊔ baseFiberClopen B hS f x k e' :=
  IdempotentGluing.preimage_sup (baseFiberToSpec B hS f x k)
    (U := fun e : Idem (baseFiberRing B hS f x k) =>
      (Spec (CommRingCat.of (baseFiberRing B hS f x k))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom e))
    (fun e e' _ => IdempotentGluing.basicOpen_idemMap_sup
      (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom e e') e e' h

variable [IsSepClosed K]

/-- **The `K`-point of the base fibre at a prime of its coordinate ring**, the coordinate ring
being ind-étale over the separably closed field `K`. -/
public noncomputable def baseFiberPoint (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] :
    Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k :=
  Spec.map (CommRingCat.ofHom
      ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose.toRingHom) ≫
    inv (baseFiberToSpec B hS f x k)

/-- The point of the base fibre at a prime, read on the spectrum of the coordinate ring, is the
spectrum of the chosen `K`-algebra map with kernel that prime. -/
public theorem baseFiberPoint_comp_baseFiberToSpec (P : Ideal (baseFiberRing B hS f x k))
    [P.IsPrime] :
    baseFiberPoint B hS f x k P ≫ baseFiberToSpec B hS f x k =
      Spec.map (CommRingCat.ofHom
        ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose.toRingHom) := by
  simp [baseFiberPoint]

/-- The point of the base fibre at a prime is a section of the projection to `Spec K`. -/
public theorem baseFiberPoint_snd (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] :
    baseFiberPoint B hS f x k P ≫ pullback.snd (strictHenselizationToBase B S hS (x.map f))
      (sepClosedPointToBase B hS f x k) = 𝟙 _ := by
  rw [← baseFiberToSpec_algebraMap, ← Category.assoc, baseFiberPoint_comp_baseFiberToSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose.toRingHom.comp
      (algebraMap K (baseFiberRing B hS f x k)) = RingHom.id K from
    RingHom.ext fun c =>
      ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose.commutes c]
  exact Spec.map_id _

omit [IsSepClosed K] in
/-- The image in `Spec` of the coordinate ring of a `K`-point of the spectrum given by a ring map
is its kernel. -/
public theorem specMap_base_asIdeal_eq_ker {R : Type u} [CommRing R] (χ : R →+* K)
    (p : Spec (CommRingCat.of K)) :
    ((Spec.map (CommRingCat.ofHom χ)).base p).asIdeal = RingHom.ker χ := by
  rw [Spec.map_base]
  change Ideal.comap χ (p : PrimeSpectrum K).asIdeal = _
  have := (p : PrimeSpectrum K).isPrime
  rw [Ideal.eq_bot_of_prime (p : PrimeSpectrum K).asIdeal]
  rfl

/-- The point of the base fibre at a prime lies over that prime. -/
public theorem baseFiberPoint_asIdeal (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime]
    (p : Spec (CommRingCat.of K)) :
    ((baseFiberToSpec B hS f x k).base ((baseFiberPoint B hS f x k P).base p)).asIdeal = P := by
  rw [← Scheme.Hom.comp_apply, baseFiberPoint_comp_baseFiberToSpec, specMap_base_asIdeal_eq_ker]
  exact ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose_spec

/-- **Every section of the projection to `Spec K` is the point at a prime**, namely at the image
of the closed point. -/
public theorem eq_baseFiberPoint
    (t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k)
    (ht : t ≫ pullback.snd (strictHenselizationToBase B S hS (x.map f))
      (sepClosedPointToBase B hS f x k) = 𝟙 _) (p : Spec (CommRingCat.of K)) :
    haveI := ((baseFiberToSpec B hS f x k).base (t.base p)).isPrime
    t = baseFiberPoint B hS f x k ((baseFiberToSpec B hS f x k).base (t.base p)).asIdeal := by
  have := ((baseFiberToSpec B hS f x k).base (t.base p)).isPrime
  set P := ((baseFiberToSpec B hS f x k).base (t.base p)).asIdeal
  rw [← cancel_mono (baseFiberToSpec B hS f x k), baseFiberPoint_comp_baseFiberToSpec]
  set χ := ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose
  have hχ := ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose_spec
  obtain ⟨ψ, hψ⟩ : ∃ ψ, t ≫ baseFiberToSpec B hS f x k = Spec.map ψ :=
    ⟨Spec.preimage _, (Spec.map_preimage _).symm⟩
  rw [hψ]
  have hψK : ψ.hom.comp (algebraMap K (baseFiberRing B hS f x k)) = RingHom.id K := by
    have h := congrArg (fun g => t ≫ g) (baseFiberToSpec_algebraMap B hS f x k)
    simp only [← Category.assoc, hψ, ht, ← Spec.map_comp] at h
    have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
    exact congrArg CommRingCat.Hom.hom h'
  have hker : RingHom.ker ψ.hom = P := by
    rw [← specMap_base_asIdeal_eq_ker ψ.hom p, CommRingCat.ofHom_hom, ← hψ, Scheme.Hom.comp_apply]
  congr 1
  ext r
  change ψ.hom r = χ r
  have hr : r - algebraMap K _ (ψ.hom r) ∈ RingHom.ker ψ.hom := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ψ.hom, hψK, RingHom.id_apply, sub_self]
  rw [hker, ← hχ, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hr
  exact hr.symm

omit [IsSepClosed K] in
/-- The clopen cut out by an idempotent is the basic open of the base fibre at its image in the
global sections. -/
public theorem baseFiberClopen_eq
    (e : StacksDraft.IdempotentGluing.Idem (baseFiberRing B hS f x k)) :
    baseFiberClopen B hS f x k e = (strictHenselizationBaseFiber B hS f x k).basicOpen
      ((baseFiberToSpec B hS f x k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv e)) :=
  Scheme.preimage_basicOpen_top _ _

omit [IsSepClosed K] in
/-- The image of an idempotent of the coordinate ring in the global sections of the base fibre is
idempotent. -/
public theorem isIdempotentElem_baseFiberClopen
    (e : StacksDraft.IdempotentGluing.Idem (baseFiberRing B hS f x k)) :
    IsIdempotentElem ((baseFiberToSpec B hS f x k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv e)) :=
  (e.2.map (Scheme.ΓSpecIso (CommRingCat.of (baseFiberRing B hS f x k))).inv.hom).map
    (baseFiberToSpec B hS f x k).appTop.hom

/-- The clopen of the base fibre cut out by an idempotent is affine. -/
public instance isAffine_baseFiberClopen
    (e : StacksDraft.IdempotentGluing.Idem (baseFiberRing B hS f x k)) :
    IsAffine (baseFiberClopen B hS f x k e) :=
  IsAffineOpen.preimage_of_isIso
    ((isAffineOpen_top (Spec (CommRingCat.of (baseFiberRing B hS f x k)))).basicOpen _) _

/-- The point of the base fibre at a prime lies in the clopen of every idempotent outside it. -/
public theorem range_baseFiberPoint_subset (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime]
    (e : StacksDraft.IdempotentGluing.GermIdx P) :
    Set.range (baseFiberPoint B hS f x k P).base ⊆
      baseFiberClopen B hS f x k (OrderDual.ofDual e.1) := by
  rintro _ ⟨p, rfl⟩
  exact (mem_baseFiberClopen B hS f x k _ _).mpr (by rw [baseFiberPoint_asIdeal]; exact e.2)

/-- **The point of the base fibre at a prime is the limit of its clopen neighbourhoods.** -/
public theorem isLimit_baseFiberPointCone (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] :
    Nonempty (IsLimit (germOpensCone (monotone_baseFiberClopen B hS f x k) P
      (baseFiberPoint B hS f x k P) (range_baseFiberPoint_subset B hS f x k P))) := by
  set ψ := baseFiberToSpec B hS f x k
  set R := baseFiberRing B hS f x k
  set χ := ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose
  have hχ := ((indEtale_baseFiberRing B hS f x k).exists_algHom_ker_eq P).choose_spec
  have hpt : baseFiberPoint B hS f x k P = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ inv ψ := rfl
  have hψψ : ∀ a : Γ(strictHenselizationBaseFiber B hS f x k, ⊤), ψ.appTop ((inv ψ).appTop a) = a :=
    fun a => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.hom_inv_id]
      rfl
  have hψψ' : ∀ b : Γ(Spec (CommRingCat.of R), ⊤), (inv ψ).appTop (ψ.appTop b) = b :=
    fun b => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id]
      rfl
  have htapp : ∀ r : R, (baseFiberPoint B hS f x k P).appTop
      (ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv (χ r) := by
    intro r
    rw [hpt, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hψψ', ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  refine isLimit_germOpensCone _ P _ _ (fun z => ?_) (fun e y => ?_) (fun a ha => ?_)
  · refine ⟨ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
      (algebraMap K R ((Scheme.ΓSpecIso (CommRingCat.of K)).hom z))), ?_⟩
    rw [htapp, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      ← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  · have := isAffine_strictHenselizationBaseFiber B hS f x k
    have h := Scheme.surjective_appTop_basicOpen_ι
      (X := strictHenselizationBaseFiber B hS f x k)
      (isIdempotentElem_baseFiberClopen B hS f x k (OrderDual.ofDual e.1))
    rw [← baseFiberClopen_eq] at h
    exact h y
  · obtain ⟨r, hr⟩ : ∃ r : R, ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = a :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom ((inv ψ).appTop a), by
        rw [← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.hom_inv_id]
        exact hψψ a⟩
    subst hr
    rw [htapp] at ha
    have hrP : r ∈ P := by
      rw [← hχ, RingHom.mem_ker]
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom ha
      rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, map_zero] at this
    obtain ⟨g, hg, hgP, hrg⟩ :=
      (indEtale_baseFiberRing B hS f x k).exists_idempotent_not_mem_mul_eq_zero P hrP
    refine ⟨⟨OrderDual.toDual ⟨g, hg⟩, hgP⟩, ?_⟩
    have h := Scheme.appTop_basicOpen_ι_eq_zero
      (X := strictHenselizationBaseFiber B hS f x k)
      (g := ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv g))
      (a := ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
      (by rw [← map_mul, ← map_mul, hrg, map_zero, map_zero])
    rw [← baseFiberClopen_eq B hS f x k ⟨g, hg⟩] at h
    exact h

end Points

/-! ### Condition (1) and condition (2) at all lifts -/

section Gluing

open StacksDraft.IdempotentGluing

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K] [IsSepClosed K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- **Condition (1) holds if and only if condition (2) holds at every lift of the point, given the
cohomology of the points of the base fibre as colimits.** Condition (1) is glued over the clopens
of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` cut out by idempotents, the germs at a point being the
cohomology at that `K`-point, and every `K`-point `t` of the base fibre is the section given by
the lift `t ≫ pr₁` of `Spec K ⟶ S`. The hypotheses are the conclusion of Theorem 09YQ for the
clopen neighbourhoods of a point, on the base fibre and on
`Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K`. -/
public theorem bijective_strictHenselizationFiberCohomologyPullback_iff_of_colimit
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ)
    (hsurj : ∀ (P : Ideal (baseFiberRing B hS f x k)) (hP : P.IsPrime), Function.Surjective
      (etaleCohomologyPullback (@baseFiberPoint B _ _ hS f x _ _ k _ P hP)
        (𝟙 ((smallEtalePullbackAb (@baseFiberPoint B _ _ hS f x _ _ k _ P hP)).obj
          (strictHenselizationBaseFiberCoeffAb B hS f x k F))) q))
    (hloc : ∀ (P : Ideal (baseFiberRing B hS f x k)) (hP : P.IsPrime) y,
      etaleCohomologyPullback (@baseFiberPoint B _ _ hS f x _ _ k _ P hP)
        (𝟙 ((smallEtalePullbackAb (@baseFiberPoint B _ _ hS f x _ _ k _ P hP)).obj
          (strictHenselizationBaseFiberCoeffAb B hS f x k F))) q y = 0 →
        ∃ e : Idem (baseFiberRing B hS f x k), (e : baseFiberRing B hS f x k) ∉ P ∧
          etaleCohomologyPullback (baseFiberClopen B hS f x k e).ι (𝟙 _) q y = 0)
    (hsurj' : ∀ (P : Ideal (baseFiberRing B hS f x k)) (hP : P.IsPrime), Function.Surjective
      (etaleCohomologyPullback (pullback.fst (strictHenselizationFiberMap B hX hS f x k)
          (@baseFiberPoint B _ _ hS f x _ _ k _ P hP))
        (𝟙 ((smallEtalePullbackAb (pullback.fst (strictHenselizationFiberMap B hX hS f x k)
          (@baseFiberPoint B _ _ hS f x _ _ k _ P hP))).obj
          ((smallEtalePullbackAb (strictHenselizationFiberMap B hX hS f x k)).obj
            (strictHenselizationBaseFiberCoeffAb B hS f x k F)))) q))
    (hloc' : ∀ (P : Ideal (baseFiberRing B hS f x k)) (hP : P.IsPrime) y,
      etaleCohomologyPullback (pullback.fst (strictHenselizationFiberMap B hX hS f x k)
          (@baseFiberPoint B _ _ hS f x _ _ k _ P hP))
        (𝟙 ((smallEtalePullbackAb (pullback.fst (strictHenselizationFiberMap B hX hS f x k)
          (@baseFiberPoint B _ _ hS f x _ _ k _ P hP))).obj
          ((smallEtalePullbackAb (strictHenselizationFiberMap B hX hS f x k)).obj
            (strictHenselizationBaseFiberCoeffAb B hS f x k F)))) q y = 0 →
        ∃ e : Idem (baseFiberRing B hS f x k), (e : baseFiberRing B hS f x k) ∉ P ∧
          etaleCohomologyPullback
            (strictHenselizationFiberMap B hX hS f x k ⁻¹ᵁ baseFiberClopen B hS f x k e).ι
            (𝟙 _) q y = 0) :
    Function.Bijective (strictHenselizationFiberCohomologyPullback B hX hS f x k F q) ↔
      ∀ k' : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f),
        k' ≫ strictHenselizationToBase B S hS (x.map f) =
            k ≫ strictHenselizationToBase B S hS (x.map f) →
          Function.Bijective (strictHenselizationPointCohomologyPullback B hX hS f x k' F q) := by
  have key := IdempotentGluing.bijective_etaleCohomologyPullback_iff_points
    (strictHenselizationFiberMap B hX hS f x k) (strictHenselizationBaseFiberCoeffAb B hS f x k F) q
    (monotone_baseFiberClopen B hS f x k) (baseFiberClopen_bot B hS f x k)
    (baseFiberClopen_top B hS f x k) (baseFiberClopen_inf B hS f x k)
    (baseFiberClopen_sup B hS f x k)
    (fun P hP => @baseFiberPoint B _ _ hS f x _ _ k _ P hP)
    (fun P hP e he => by
      rintro _ ⟨p, rfl⟩
      exact (mem_baseFiberClopen B hS f x k e _).mpr (by rwa [baseFiberPoint_asIdeal]))
    hsurj hloc hsurj' hloc'
  refine key.trans ⟨fun h k' hk' => ?_, fun h P hP => ?_⟩
  · let t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k :=
      pullback.lift k' (𝟙 _) (by rw [Category.id_comp]; exact hk')
    have ht : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hk'' : k' = t ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have htP := eq_baseFiberPoint B hS f x k t ht p
    rw [hk'',
      bijective_strictHenselizationPointCohomologyPullback_iff_of_section B hX hS f x k t ht]
    rw [htP]
    exact h _ _
  · have hk : (@baseFiberPoint B _ _ hS f x _ _ k _ P hP ≫ pullback.fst _ _) ≫
        strictHenselizationToBase B S hS (x.map f) =
          k ≫ strictHenselizationToBase B S hS (x.map f) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, baseFiberPoint_snd,
        Category.id_comp]
    have := h _ hk
    rwa [bijective_strictHenselizationPointCohomologyPullback_iff_of_section B hX hS f x k _
      (baseFiberPoint_snd B hS f x k P)] at this

end Gluing

/-! ### The corrected statement -/

section Corrected

open StacksDraft.IdempotentGluing OrderDual

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K] [IsSepClosed K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- On the base fibre, pulling back to the point at a prime is surjective: the point is a
section of the projection to `Spec K`. -/
public theorem surjective_etaleCohomologyPullback_baseFiberPoint
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ)
    (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] :
    Function.Surjective (etaleCohomologyPullback (baseFiberPoint B hS f x k P)
      (𝟙 ((smallEtalePullbackAb (baseFiberPoint B hS f x k P)).obj
        (strictHenselizationBaseFiberCoeffAb B hS f x k F))) q) := by
  have h := baseFiberPoint_snd B hS f x k P
  have hb := bijective_etaleCohomologyPullback_of_isIso (𝟙 (Spec (CommRingCat.of K)))
    ((smallEtalePullbackAbComp' (baseFiberPoint B hS f x k P) _ (𝟙 _) h.symm).inv.app F ≫
      (smallEtalePullbackAb (baseFiberPoint B hS f x k P)).map (𝟙 _) ≫ 𝟙 _) q
  intro z
  obtain ⟨w, hw⟩ := hb.2 z
  refine ⟨etaleCohomologyPullback _ (𝟙 _) q w, ?_⟩
  rw [etaleCohomologyPullback_comp _ _ (𝟙 _) h.symm]
  exact hw

omit [IsSepClosed K] in
/-- On the base fibre `T`, for `π : W ⟶ T`, restriction to the preimage of a clopen cut out by an
idempotent is surjective on cohomology. -/
public theorem surjective_etaleCohomologyPullback_preimage_baseFiberClopen {W : Scheme.{u}}
    (π : W ⟶ strictHenselizationBaseFiber B hS f x k) (G : Sheaf (smallEtaleTopology W) Ab.{u + 1})
    (q : ℕ) (e : Idem (baseFiberRing B hS f x k)) :
    Function.Surjective (etaleCohomologyPullback (π ⁻¹ᵁ baseFiberClopen B hS f x k e).ι
      (𝟙 ((smallEtalePullbackAb (π ⁻¹ᵁ baseFiberClopen B hS f x k e).ι).obj G)) q) := by
  have hc : Disjoint e eᶜ := disjoint_compl_right
  have hp := IdempotentGluing.bijective_pullback_pair (π ⁻¹ᵁ baseFiberClopen B hS f x k e).ι
    (π ⁻¹ᵁ baseFiberClopen B hS f x k eᶜ).ι
    (by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, Set.disjoint_iff_inter_eq_empty]
      have h := congrArg (fun V => ((π ⁻¹ᵁ V : W.Opens) : Set W))
        (baseFiberClopen_inf B hS f x k e eᶜ hc)
      exact h)
    (by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      have h := congrArg (fun V => ((π ⁻¹ᵁ V : W.Opens) : Set W))
        (baseFiberClopen_sup B hS f x k e eᶜ hc)
      simp only [sup_compl_eq_top, baseFiberClopen_top] at h
      exact h.symm) G (𝟙 _) (𝟙 _) q
  intro y
  obtain ⟨z, hz⟩ := hp.2 (y, 0)
  exact ⟨z, congrArg Prod.fst hz⟩

/-- **[Stacks, Tag 0EZV], corrected.** Let `f : X ⟶ S` be a morphism of schemes, `x̄` a geometric
point of `X` with image `s̄`, `k : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` with `K` separably closed, `ℱ` an
abelian sheaf on `Spec K` and `q ≥ 0`. Then
`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ)` if and only if
`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄}), k'} Spec K, ℱ) = H^q(Spec K, ℱ)` for every lift
`k'` of the composite `Spec K ⟶ S` to the strict henselization, each equality read as
bijectivity of the restriction map. -/
@[stacks 0EZV "corrected: condition (1) is equivalent to condition (2) at every lift `k'` of
`Spec K ⟶ S` to the strict henselization, not only at the given point; that (2) at the given
point does not imply (1) is
`Stacks.EtaleCohomology.exists_bijective_pointRestriction_and_not_bijective_fiberRestriction`"]
public theorem bijective_strictHenselizationFiberCohomologyPullback_iff
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (strictHenselizationFiberCohomologyPullback B hX hS f x k F q) ↔
      ∀ k' : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f),
        k' ≫ strictHenselizationToBase B S hS (x.map f) =
            k ≫ strictHenselizationToBase B S hS (x.map f) →
          Function.Bijective (strictHenselizationPointCohomologyPullback B hX hS f x k' F q) := by
  have := isAffine_strictHenselizationBaseFiber B hS f x k
  have := isAffine_strictHenselizationSourceFiber B hX hS f x k
  set π := strictHenselizationFiberMap B hX hS f x k
  set G := strictHenselizationBaseFiberCoeffAb B hS f x k F
  have hmono' : Monotone fun e => π ⁻¹ᵁ baseFiberClopen B hS f x k e :=
    IdempotentGluing.monotone_preimage π (monotone_baseFiberClopen B hS f x k)
  have ht' : ∀ (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] (e : GermIdx P),
      Set.range (pullback.fst π (baseFiberPoint B hS f x k P)).base ⊆
        π ⁻¹ᵁ baseFiberClopen B hS f x k (ofDual e.1) := by
    intro P _ e
    rintro _ ⟨z, rfl⟩
    change π.base ((pullback.fst π _).base z) ∈ (baseFiberClopen B hS f x k (ofDual e.1) :
      Set (strictHenselizationBaseFiber B hS f x k))
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact range_baseFiberPoint_subset B hS f x k P e ⟨_, rfl⟩
  have hW : ∀ e : Idem (baseFiberRing B hS f x k),
      IsAffine (π ⁻¹ᵁ baseFiberClopen B hS f x k e) := fun e =>
    IsAffineOpen.preimage (isAffine_baseFiberClopen B hS f x k e) π
  have hcol := fun (P : Ideal (baseFiberRing B hS f x k)) [P.IsPrime] =>
    isGermCohomologyColimit hmono' P _ (ht' P) ((smallEtalePullbackAb π).obj G) q
      (isLimit_germOpensCone_preimage _ P _ _
        (isLimit_baseFiberPointCone B hS f x k P).some π hmono' (ht' P)).some
  refine bijective_strictHenselizationFiberCohomologyPullback_iff_of_colimit B hX hS f x k F q
    (fun P hP => @surjective_etaleCohomologyPullback_baseFiberPoint B _ _ hS f x _ _ _ k F q P hP)
    (fun P hP y hy => ?_) (fun P hP => ?_) (fun P hP y hy => ?_)
  · exact (isGermCohomologyColimit (monotone_baseFiberClopen B hS f x k) P _
      (range_baseFiberPoint_subset B hS f x k P) G q
      (isLimit_baseFiberPointCone B hS f x k P).some).exists_eq_zero y hy
  · exact (hcol P).surjective
      (surjective_etaleCohomologyPullback_preimage_baseFiberClopen B hS f x k π _ q)
  · exact (hcol P).exists_eq_zero y hy

end Corrected

/-! ### Nonvanishing and separation -/

section Separation

/-- **The degree zero cohomology of the constant sheaf `ℤ` is nonzero on a scheme with a
geometric point**: the identity of the constant sheaf is a nonzero class, the constant sheaf
having fibre `ℤ` at the point. -/
public theorem nontrivial_sheafH_zero_of_iso {Z : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (z : Spec (CommRingCat.of Ω) ⟶ Z) {A : Sheaf (smallEtaleTopology Z) Ab.{u + 1}}
    (e : (constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ≅ A) :
    Nontrivial (Sheaf.H.{u + 1} A 0) := by
  refine ⟨⟨Abelian.Ext.mk₀ e.hom, 0, fun h => ?_⟩⟩
  rw [Abelian.Ext.mk₀_eq_zero_iff] at h
  refine GrothendieckTopology.Point.not_isZero_constantSheaf (Scheme.pointSmallEtale z) ?_
    ((IsZero.iff_id_eq_zero _).mpr (by rw [← e.hom_inv_id, h, zero_comp]))
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  intro hs
  exact absurd (congrArg ULift.down (hs.elim (⟨0⟩ : ULift ℤ) ⟨1⟩)) (by decide)

/-- **On the spectrum of an ind-étale algebra over a separably closed field, a point and a
quasi-compact set not containing it are separated by a decomposition into two disjoint opens.**
The two opens are `D(e)` and `D(1 - e)` for an idempotent `e` given by
`StacksDraft.IndEtale.exists_isIdempotentElem_separating`. -/
public theorem exists_opens_separating_of_indEtale {K R : Type u} [Field K] [IsSepClosed K]
    [CommRing R] [Algebra K R] (hR : StacksDraft.IndEtale K R) {Z : Set (PrimeSpectrum R)}
    (hZ : IsCompact Z) {t : PrimeSpectrum R} (ht : t ∉ Z) :
    ∃ V V' : TopologicalSpace.Opens (PrimeSpectrum R),
      V ⊓ V' = ⊥ ∧ V ⊔ V' = ⊤ ∧ t ∈ V ∧ Z ⊆ V' := by
  obtain ⟨e, he, het, heZ⟩ := hR.exists_isIdempotentElem_separating hZ ht
  refine ⟨PrimeSpectrum.basicOpen e, PrimeSpectrum.basicOpen (1 - e), ?_, ?_, het,
    fun Q hQ hQ' => ?_⟩
  · rw [← PrimeSpectrum.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self,
      PrimeSpectrum.basicOpen_zero]
  · rw [eq_top_iff]
    intro P _
    by_contra h
    simp only [TopologicalSpace.Opens.mem_sup, PrimeSpectrum.mem_basicOpen, not_or,
      not_not] at h
    exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem
      (by simpa using P.asIdeal.add_mem h.1 h.2) isUnit_one)
  · exact Q.isPrime.ne_top (Q.asIdeal.eq_top_of_isUnit_mem
      (by simpa using Q.asIdeal.add_mem (heZ Q hQ) hQ') isUnit_one)

end Separation

/-! ### The tag: condition (1) is condition (2) at every lift -/

section Counterexample

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K] [IsSepClosed K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- **Condition (1) fails as soon as some point of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` has empty
fibre.** If a `K`-point `t` of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is not hit by
`Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K`, a clopen neighbourhood of `t` missed by the latter carries a
nonzero class of `H⁰(-, ℤ)` which extends by zero and dies on `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K`. -/
public theorem not_injective_strictHenselizationFiberCohomologyPullback_of_isEmpty
    (t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k)
    (ht : IsEmpty ↥(pullback (strictHenselizationFiberMap B hX hS f x k) t)) :
    ¬ Function.Injective
      (strictHenselizationFiberCohomologyPullback B hX hS f x k
        (constantZ (Spec (CommRingCat.of K))) 0) := by
  let T := strictHenselizationBaseFiber B hS f x k
  let π := strictHenselizationFiberMap B hX hS f x k
  let G := strictHenselizationBaseFiberCoeffAb B hS f x k (constantZ (Spec (CommRingCat.of K)))
  let := sepClosedPointAlgebra B hS f x k
  let R₀ := stalkRingAtImage f x
  let O := ↥(etaleLocalRing B S hS (x.map f))
  let e : T ≅ Spec (CommRingCat.of (K ⊗[R₀] O)) :=
    strictHenselizationBaseFiberIsoSpecFieldTensor B hS f x k
  have hR : StacksDraft.IndEtale K (K ⊗[R₀] O) :=
    indEtale_strictHenselizationBaseFiberRing B hS f x k
  have : IsAffine (strictHenselizationSourceFiber B hX hS f x k) :=
    isAffine_strictHenselizationSourceFiber B hX hS f x k
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hbij : Function.Bijective e.hom.base := ConcreteCategory.bijective_of_isIso e.hom.base
  have hZ : IsCompact (e.hom.base '' Set.range π.base) :=
    (isCompact_range π.continuous).image e.hom.continuous
  have htZ : e.hom.base (t.base p) ∉ e.hom.base '' Set.range π.base := by
    rintro ⟨_, ⟨w, rfl⟩, hw⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := t) w p
      (hbij.1 hw)
    exact ht.false z
  obtain ⟨V₀, V₀', hdisj, hcov, htV, hZV⟩ := exists_opens_separating_of_indEtale hR hZ htZ
  let V : T.Opens := e.hom ⁻¹ᵁ V₀
  let V' : T.Opens := e.hom ⁻¹ᵁ V₀'
  have htV' : t.base p ∈ V := htV
  let l := IsOpenImmersion.lift V.ι t (by
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p' p]
    exact htV')
  have : Nontrivial (Sheaf.H.{u + 1} ((smallEtalePullbackAb V.ι).obj G) 0) :=
    nontrivial_sheafH_zero_of_iso l
      (((smallEtalePullbackAbConstantIso V.ι).app (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
        (smallEtalePullbackAb V.ι).mapIso
          (((smallEtalePullbackAbConstantIso _).app (AddCommGrpCat.of (ULift ℤ))).symm))
  exact IdempotentGluing.not_injective_etaleCohomologyPullback_of_range_subset π G 0 V V'
    (by
      change e.hom ⁻¹ᵁ (V₀ ⊓ V₀') = ⊥
      exact (congrArg (fun U => e.hom ⁻¹ᵁ U) hdisj).trans rfl)
    (by
      change e.hom ⁻¹ᵁ (V₀ ⊔ V₀') = ⊤
      exact (congrArg (fun U => e.hom ⁻¹ᵁ U) hcov).trans rfl)
    (by
      rintro _ ⟨w, rfl⟩
      exact hZV ⟨_, ⟨w, rfl⟩, rfl⟩)

open NodeCounterexample in
/-- **Tag 0EZV fails as stated: condition (2) at the given point does not imply condition (1).**
Let `S` be the nodal cubic over an algebraically closed field of characteristic zero, `s̄` its
geometric point at the node, and `X = Spec(𝒪^{sh}_{S,s̄}/(e))` for the branch
`e = y - x √(1 + x)` of the node in the strict henselization, with `x̄` its geometric point over
`s̄`. For two `K`-points `κ`, `τ` of `Spec(𝒪^{sh}_{S,s̄})` over the same point of `S`, with `κ` on
the branch and `τ` off it, take the point `κ` and `q = 0`, `ℱ = ℤ`. The fibre of `X` over `κ` is
`Spec K` itself, so condition (2) holds; the fibre over `τ` is empty, so the restriction map of
condition (1) kills the class of the constant function `1` on a clopen neighbourhood of `τ`, and
condition (1) fails. -/
@[stacks 0EZV "the statement as given fails: condition (2) at the given point does not imply
condition (1). Condition (1) is equivalent to condition (2) at every lift of `Spec K ⟶ S` to the
strict henselization."]
public theorem exists_bijective_pointRestriction_and_not_bijective_fiberRestriction :
    ∃ (B : BigEtaleSite.{u}) (X S : Scheme.{u}) (hX : B.Contains X) (hS : B.Contains S)
      (f : X ⟶ S) (x : GeometricPoint X) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f)),
      Function.Bijective
          (strictHenselizationPointCohomologyPullback B hX hS f x k
            (constantZ (Spec (CommRingCat.of K))) 0) ∧
        ¬ Function.Bijective
          (strictHenselizationFiberCohomologyPullback B hX hS f x k
            (constantZ (Spec (CommRingCat.of K))) 0) := by
  let k₀ := AlgebraicClosure (ULift.{u} ℚ)
  have h2 : (2 : k₀) ≠ 0 := by
    rw [← map_ofNat (algebraMap (ULift.{u} ℚ) k₀) 2, map_ne_zero]
    intro h
    have := congrArg ULift.down h
    norm_num at this
  let B₀ := BigEtaleSite.containing (nodeScheme k₀)
  have hS₀ : B₀.Contains (nodeScheme k₀) := BigEtaleSite.contains_containing _
  have hs := nodePoint_hom_closedPoint k₀
  let X := branchScheme B₀ hS₀ (nodePoint k₀) hs h2
  let B := BigEtaleSite.ofSet ({nodeScheme k₀, X} : Set Scheme.{u})
  have hS : B.Contains (nodeScheme k₀) := BigEtaleSite.contains_ofSet _ (Set.mem_insert _ _)
  have hX : B.Contains X := BigEtaleSite.contains_ofSet _ (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, _, _, κ, τ, hκτ, hκ, hτ⟩ := exists_two_points B₀ hS₀ hs h2
  let f := branchToNode B₀ hS₀ (nodePoint k₀) hs h2
  let x := branchPoint B₀ hS₀ (nodePoint k₀) hs h2
  let kκ := pointAtImage B₀ hS₀ (nodePoint k₀) hs h2 B hS κ
  refine ⟨B, X, nodeScheme k₀, hX, hS, f, x, K, inferInstance, inferInstance, kκ, ?_, fun hb => ?_⟩
  · have := isIso_pullback_snd_of_branch B₀ hS₀ (nodePoint k₀) hs h2 B hS hX κ hκ
    exact bijective_etaleCohomologyPullback_of_isIso _ _ 0
  · have hτκ := pointAtImage_comp_toBase B₀ hS₀ (nodePoint k₀) hs h2 B hS κ τ hκτ
    let t : Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x kκ :=
      pullback.lift (pointAtImage B₀ hS₀ (nodePoint k₀) hs h2 B hS τ) (𝟙 _)
        (by rw [Category.id_comp]; exact hτκ)
    refine not_injective_strictHenselizationFiberCohomologyPullback_of_isEmpty B hX hS f x kκ t
      ⟨fun z => (isEmpty_pullback_of_not_branch B₀ hS₀ (nodePoint k₀) hs h2 B hS hX τ hτ).false
        ((pullback.lift (pullback.fst _ t ≫ pullback.fst (strictHenselizationToBase B X hX x ≫ f)
          (sepClosedPointToBase B hS f x kκ)) (pullback.snd _ t) ?_).base z)⟩ hb.1
    rw [Category.assoc, ← strictHenselizationFiberMap_comp_fst, ← Category.assoc,
      pullback.condition, Category.assoc, pullback.lift_fst]

end Counterexample

end Stacks.EtaleCohomology

end
