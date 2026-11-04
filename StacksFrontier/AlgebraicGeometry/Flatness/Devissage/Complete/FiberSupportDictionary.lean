module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraDictionaryAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineFiber
public import StacksFrontier.RingTheory.RelativeDimension.Basic

/-!
# The fibre-module conditions of a one-step dévissage, read on rings

A one-step dévissage `(Z, Y, i, π, 𝒢, z, y)` of `ℱ/X/S` at a point `x` (Stacks 05H5) carries two
conditions that mention the fibre module: the point `x` lies in the support of the fibre of `ℱ`
over `f x`, and the local dimension of that support at `x` is maximal. Translated into algebra
these are the two conditions of Stacks 05HZ that
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionaryAt.lean` leaves
open, namely the two remaining fields of `Module.DevissageStageData.Pointed`:

* `lowerPrime_mem_fiberSupport`: the prime `qᵢ` of `Γ(Y, ⊤)` lies in the support of the fibre
  module over the fibre ring `κ(r) ⊗_R Γ(Y, ⊤)`;
* `relativeDimension_eq_support`: `R → Γ(Y, ⊤)` has relative dimension the local dimension of
  that support at `qᵢ`, which is Stacks 05HZ (4).

Both come from the same chain. The support of the fibre module over the fibre ring is, by
`Module.fiberSupportHomeomorph`, the part of `Supp_{Γ(Y, ⊤)}(Γ(𝒢, ⊤))` lying over `r`; that part
is compared with the corresponding part upstairs on `Z` along the *finite* morphism `π`, whose
fibre over `y` is the single point `z`, and then with the corresponding part on `X` along the
*closed immersion* `i`, whose map on functions is surjective. Both comparisons are
`Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`. On `X` the part of the support
lying over `r` is the support of the fibre of `ℱ`, by
`AlgebraicGeometry.suppFiberHomeomorph`, and the local dimension there is the dimension of the
whole fibre support by the field `AlgebraicGeometry.OneStepDevissageAt.dimension`. That
dimension is the relative dimension of `R → Γ(Y, ⊤)` because every fibre of `Spec Γ(Y, ⊤) → Spec R`
has it, which is the field `AlgebraicGeometry.OneStepDevissage.fiber_dimension`.

## Main results

* `AlgebraicGeometry.OneStepDevissage.relativeDimension_eq_topologicalKrullDim_supp`: **the
  relative dimension of the functions on the smooth scheme of a one-step dévissage is the
  dimension of the support of the fibre module.**
* `AlgebraicGeometry.OneStepDevissage.mem_fiberSupport_lowerPrime` and
  `AlgebraicGeometry.OneStepDevissage.topologicalKrullDimAt_fiberSupport_lowerPrime`: the chosen
  prime of `Γ(Y, ⊤)` lies in the part of `Supp(Γ(𝒢, ⊤))` over `r`, and the local dimension
  there is the local dimension of the support of the fibre of `ℱ` at `x`.
* `AlgebraicGeometry.OneStepDevissageAt.lowerPrime_mem_fiberSupport` and
  `AlgebraicGeometry.OneStepDevissageAt.relativeDimension_eq_support`: **the two conditions of
  `Module.DevissageStageData.Pointed` that mention the fibre module**, in the exact shape that
  structure records them.

## Implementation notes

The direction proved here is geometry ⇒ algebra; the converse, which Stacks 05I0 (2) also
asserts, is `Module.DevissageStage.lowerPrimeMem` and `Module.DevissageStage.fiberDim` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecDevissageAt.lean`. Both
directions pair `AlgebraicGeometry.OneStepDevissage.fiber_dimension`, which constrains *every*
fibre of the smooth morphism as Stacks 05H4 (5) does, with the fibrewise form of the relative
dimension condition of Stacks 05HZ (4),
`Module.DevissageStageData.Pointed.topologicalKrullDim_fiber_eq_support`. The single supremum of
Definition 00QD, `Module.DevissageStageData.Pointed.relativeDimension_eq_support`, is the weaker
condition, and it does not suffice: see the `## Stacks 05I0 (2)` section of
`StacksFrontier/RingTheory/RelativeDimension/UnequalFibreDimension.lean`.

The results are stated for a `AlgebraicGeometry.OneStepDevissage` together with the two chosen
points and the conditions relating them, rather than for a
`AlgebraicGeometry.OneStepDevissageAt`, so that the names of the four rings are
`Γ(D.Y, ⊤)`, `Γ(D.Z, ⊤)`, `Γ(X, ⊤)` and `Γ(S, ⊤)` rather than projections of a dévissage at a
point; the two fields are then one-line consequences.

Primes are passed as variables with an equation identifying them with
`(X.isoSpec.hom x).asIdeal`, as in `AlgebraDictionaryAt`, and the `Ideal.IsPrime` instance of a
prime read off a point is supplied by hand, since instance synthesis does not unfold the carrier
of `Spec` to `PrimeSpectrum`.

The algebra structures on the four rings are the ones induced by the morphisms themselves,
through `RingHom.toAlgebra`, as in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionary.lean`; the two that
`AlgebraComparison` does not already provide are
`AlgebraicGeometry.OneStepDevissage.algebraFinite` and
`AlgebraicGeometry.OneStepDevissage.algebraClosedImmersion`. With those the three scalar towers
and the four finiteness statements that the ring-theoretic lemmas ask for are each a one-liner,
and they are repeated in the proofs that need them rather than packaged: a package would have
to be a structure over all four rings, and every consumer would have to destructure it before
instance synthesis could see its fields.

## References

* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

namespace OneStepDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- The finite morphism of a one-step dévissage, as an algebra structure on the functions of
the closed subscheme over those of the smooth scheme. -/
public abbrev algebraFinite {s : S} (D : OneStepDevissage f F s) :
    Algebra Γ(D.Y, ⊤) Γ(D.Z, ⊤) := D.π.appTop.hom.toAlgebra

/-- The closed immersion of a one-step dévissage, as an algebra structure on the functions of
the closed subscheme over those of the scheme being dévissed. -/
public abbrev algebraClosedImmersion {s : S} (D : OneStepDevissage f F s) :
    Algebra Γ(X, ⊤) Γ(D.Z, ⊤) := D.i.appTop.hom.toAlgebra

/-! ### The relative dimension of the smooth algebra -/

/-- **Every fibre of `Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` has the dimension of the support of the fibre
module**, which is `AlgebraicGeometry.OneStepDevissage.fiber_dimension` read on rings: the fibre
of `Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` over a prime is homeomorphic to the scheme-theoretic fibre of
`g` over the corresponding point of `S`. -/
public theorem topologicalKrullDim_fiber_eq_topologicalKrullDim_supp {s : S}
    (D : OneStepDevissage f F s) (p : PrimeSpectrum Γ(S, ⊤)) :
    letI := D.algebraSmooth
    topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) ⁻¹' {p}) =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
  let _ := D.affine_S
  let _ := D.affine_Y
  let _ := D.algebraSmooth
  have hsp : S.isoSpec.hom (S.isoSpec.inv p) = p :=
    (Scheme.homeoOfIso S.isoSpec).apply_symm_apply p
  exact (D.g.topologicalKrullDim_fiber_eq (RingHom.algebraMap_toAlgebra _)
    (S.isoSpec.inv p) p.asIdeal (congrArg PrimeSpectrum.asIdeal hsp)).symm.trans
    (D.fiber_dimension _)

/-- **The relative dimension of the functions on the smooth scheme of a one-step dévissage is
the dimension of the support of the fibre module**, the relative dimension being the single
supremum of Definition 00QD. Every fibre of `Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` has that dimension,
by `AlgebraicGeometry.OneStepDevissage.fiber_dimension`, and an algebra all of whose fibres have
one dimension has that relative dimension. -/
public theorem relativeDimension_eq_topologicalKrullDim_supp {s : S}
    (D : OneStepDevissage f F s) :
    letI := D.algebraSmooth
    Algebra.relativeDimension Γ(S, ⊤) Γ(D.Y, ⊤) =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
  let _ := D.affine_S
  let _ := D.affine_Y
  let _ := D.algebraSmooth
  exact @Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber Γ(S, ⊤) Γ(D.Y, ⊤)
    _ _ _ ⟨S.isoSpec.hom s⟩ _ (fun p => D.topologicalKrullDim_fiber_eq_topologicalKrullDim_supp p)

/-! ### The fibre support at the chosen primes -/

variable (D : OneStepDevissage f F (f x)) (z : D.Z) (y : D.Y)

/-- Membership of the prime of `Γ(Y, ⊤)` in the fibre support, together with the local dimension
comparison when `π` has the single point `z` over `y`. -/
private theorem mem_and_topologicalKrullDimAt_fiberSupport_lowerPrime (hiz : D.i z = x)
    (hπz : D.π z = y)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.affine_S; (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.affine_Y; (D.Y.isoSpec.hom y).asIdeal = qY) :
    letI := D.algebraSmooth
    letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
    ∃ hmem : (⟨qY, hqYp⟩ : PrimeSpectrum Γ(D.Y, ⊤)) ∈
        Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r,
      D.π ⁻¹' {y} = {z} →
        topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r)
            ⟨⟨qY, hqYp⟩, hmem⟩ =
          topologicalKrullDimAt ↥(SheafOfModules.supp
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ⟨f.asFiber x, hx⟩ := by
  let _ := D.affine_X
  let _ := D.affine_S
  let _ := D.affine_Y
  let _ := D.affine_Z
  let _ := algebraSource (f := f)
  let _ := D.algebraClosed
  let _ := D.algebraSmooth
  let _ := D.algebraFinite
  let _ := D.algebraClosedImmersion
  let _ : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
  let _ : Module Γ(X, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.i.appTop.hom
  have htXZ : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(D.Z, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htYZ : IsScalarTower Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.Z, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(D.Z, ⊤) => φ.hom a) D.appTop_over_base
  have htYG : IsScalarTower Γ(D.Y, ⊤) Γ(D.Z, ⊤) Γ(D.G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htXG : IsScalarTower Γ(X, ⊤) Γ(D.Z, ⊤) Γ(D.G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfinYZ : Module.Finite Γ(D.Y, ⊤) Γ(D.Z, ⊤) := D.finite_π_appTop
  have hfinXZ : Module.Finite Γ(X, ⊤) Γ(D.Z, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap Γ(X, ⊤) Γ(D.Z, ⊤))
      D.surjective_i_appTop
  have hfinYG : Module.Finite Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.Finite.trans Γ(D.Z, ⊤) Γ(D.G, ⊤)
  have hfinXG : Module.Finite Γ(X, ⊤) Γ(D.G, ⊤) := Module.Finite.trans Γ(D.Z, ⊤) Γ(D.G, ⊤)
  have hfinXF : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  have hzp : ((D.Z.isoSpec.hom z).asIdeal).IsPrime := (D.Z.isoSpec.hom z).isPrime
  have hxp : ((X.isoSpec.hom x).asIdeal).IsPrime := (X.isoSpec.hom x).isPrime
  have hintYZ : Algebra.IsIntegral Γ(D.Y, ⊤) Γ(D.Z, ⊤) := Algebra.IsIntegral.of_finite _ _
  have hintXZ : Algebra.IsIntegral Γ(X, ⊤) Γ(D.Z, ⊤) := Algebra.IsIntegral.of_finite _ _
  have hxF : x ∈ SheafOfModules.supp F := by
    rw [Stacks.Modules.supp_pullback] at hx
    simpa using hx
  have hpXF : (⟨(X.isoSpec.hom x).asIdeal, (X.isoSpec.hom x).isPrime⟩ :
      PrimeSpectrum Γ(X, ⊤)) ∈ Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) r := by
    refine ⟨(mem_support_sections_iff_mem_supp_top F x).2 hxF, ?_⟩
    rw [Set.mem_preimage]
    exact (comap_algebraMap_isoSpec_hom f (RingHom.algebraMap_toAlgebra _) x).trans
      (PrimeSpectrum.ext hr)
  have hFG : Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(D.G, ⊤) r =
      Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) r :=
    (Module.fiberSupport_congr Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) r
      (show Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(D.G, ⊤) from D.closedSectionsLinearEquiv)).symm
  have hpXG : (⟨(X.isoSpec.hom x).asIdeal, (X.isoSpec.hom x).isPrime⟩ :
      PrimeSpectrum Γ(X, ⊤)) ∈ Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(D.G, ⊤) r := by
    rw [hFG]; exact hpXF
  have hcZX : PrimeSpectrum.comap (algebraMap Γ(X, ⊤) Γ(D.Z, ⊤))
      (⟨(D.Z.isoSpec.hom z).asIdeal, (D.Z.isoSpec.hom z).isPrime⟩ : PrimeSpectrum Γ(D.Z, ⊤)) =
      ⟨(X.isoSpec.hom x).asIdeal, (X.isoSpec.hom x).isPrime⟩ :=
    PrimeSpectrum.ext (comap_asIdeal_isoSpec_hom D.i z x hiz _ rfl _ rfl)
  have hqZ : (⟨(D.Z.isoSpec.hom z).asIdeal, (D.Z.isoSpec.hom z).isPrime⟩ :
      PrimeSpectrum Γ(D.Z, ⊤)) ∈ Module.fiberSupport Γ(S, ⊤) Γ(D.Z, ⊤) Γ(D.G, ⊤) r :=
    Module.mem_fiberSupport_of_comap_mem_fiberSupport_of_surjective D.surjective_i_appTop r
      (by rw [hcZX]; exact hpXG)
  have hcZY : PrimeSpectrum.comap (algebraMap Γ(D.Y, ⊤) Γ(D.Z, ⊤))
      (⟨(D.Z.isoSpec.hom z).asIdeal, (D.Z.isoSpec.hom z).isPrime⟩ : PrimeSpectrum Γ(D.Z, ⊤)) =
      ⟨qY, hqYp⟩ :=
    PrimeSpectrum.ext (comap_asIdeal_isoSpec_hom D.π z y hπz _ rfl qY hqY)
  have hmem : (⟨qY, hqYp⟩ : PrimeSpectrum Γ(D.Y, ⊤)) ∈
      Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r := by
    rw [← hcZY]
    exact Module.comap_mem_fiberSupport_of_mem r hqZ
  refine ⟨hmem, fun hfib => ?_⟩
  have huniqY : ∀ p' : PrimeSpectrum Γ(D.Z, ⊤),
      PrimeSpectrum.comap (algebraMap Γ(D.Y, ⊤) Γ(D.Z, ⊤)) p' = ⟨qY, hqYp⟩ →
      p' = ⟨(D.Z.isoSpec.hom z).asIdeal, (D.Z.isoSpec.hom z).isPrime⟩ := by
    intro p' hp'
    refine PrimeSpectrum.ext ?_
    exact @eq_of_comap_asIdeal_isoSpec_hom_eq _ _ _ _ D.π z y hfib _ hzp rfl qY hqYp hqY
      p'.asIdeal p'.isPrime (congrArg PrimeSpectrum.asIdeal hp')
  have huniqX : ∀ p' : PrimeSpectrum Γ(D.Z, ⊤),
      PrimeSpectrum.comap (algebraMap Γ(X, ⊤) Γ(D.Z, ⊤)) p' =
        ⟨(X.isoSpec.hom x).asIdeal, (X.isoSpec.hom x).isPrime⟩ →
      p' = ⟨(D.Z.isoSpec.hom z).asIdeal, (D.Z.isoSpec.hom z).isPrime⟩ := by
    intro p' hp'
    refine PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ D.surjective_i_appTop ?_)
    exact (congrArg PrimeSpectrum.asIdeal hp').trans
      (congrArg PrimeSpectrum.asIdeal hcZX).symm
  calc topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r)
          ⟨⟨qY, hqYp⟩, hmem⟩
      = topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(D.Z, ⊤) Γ(D.G, ⊤) r)
          ⟨_, hqZ⟩ :=
        (Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral r hcZY huniqY hqZ hmem).symm
    _ = topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(D.G, ⊤) r)
          ⟨_, hpXG⟩ :=
        Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral r hcZX huniqX hqZ hpXG
    _ = topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) r)
          ⟨_, hpXF⟩ :=
        topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hFG) ⟨_, hpXG⟩
    _ = topologicalKrullDimAt ↥(SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ⟨f.asFiber x, hx⟩ :=
        (topologicalKrullDimAt_supp_fiber f F (RingHom.algebraMap_toAlgebra _) x hx r hr
          ((X.isoSpec.hom x).asIdeal) rfl hpXF).symm

/-- **The prime of `Γ(Y, ⊤)` attached to the chosen point of the smooth scheme lies in the part
of the support of `Γ(𝒢, ⊤)` lying over the base prime.**

The point `x` lies in the support of `ℱ`, so the prime of `Γ(X, ⊤)` attached to it lies in the
support of `Γ(ℱ, ⊤)`; the closed immersion identifies that module with `Γ(𝒢, ⊤)` and its map on
functions is surjective, so the prime attached to `z` lies in the support of `Γ(𝒢, ⊤)` over
`Γ(Z, ⊤)`; and contracting along the finite morphism lands in the support over `Γ(Y, ⊤)`. -/
public theorem mem_fiberSupport_lowerPrime (hiz : D.i z = x) (hπz : D.π z = y)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.affine_S; (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.affine_Y; (D.Y.isoSpec.hom y).asIdeal = qY) :
    letI := D.algebraSmooth
    letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
    (⟨qY, hqYp⟩ : PrimeSpectrum Γ(D.Y, ⊤)) ∈
      Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r :=
  (mem_and_topologicalKrullDimAt_fiberSupport_lowerPrime D z y hiz hπz hx r hr qY
    hqY).elim fun hmem _ => hmem

/-- **The local dimension of the part of `Supp(Γ(𝒢, ⊤))` over the base prime, at the prime
attached to the chosen point of the smooth scheme, is the local dimension of the support of the
fibre of `ℱ` at `x`.**

Along the finite morphism `π` the prime attached to `z` is the unique prime above the prime
attached to `y`, and along the closed immersion `i` contraction of primes is injective; both
comparisons are `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`. -/
public theorem topologicalKrullDimAt_fiberSupport_lowerPrime (hiz : D.i z = x) (hπz : D.π z = y)
    (hfib : D.π ⁻¹' {y} = {z})
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.affine_S; (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.affine_Y; (D.Y.isoSpec.hom y).asIdeal = qY)
    (hmem : letI := D.algebraSmooth
      letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
      (⟨qY, hqYp⟩ : PrimeSpectrum Γ(D.Y, ⊤)) ∈
        Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r) :
    letI := D.algebraSmooth
    letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
    topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(D.Y, ⊤) Γ(D.G, ⊤) r)
          ⟨⟨qY, hqYp⟩, hmem⟩ =
      topologicalKrullDimAt ↥(SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ⟨f.asFiber x, hx⟩ :=
  (mem_and_topologicalKrullDimAt_fiberSupport_lowerPrime D z y hiz hπz hx r hr qY
    hqY).elim fun _ h => h hfib

end OneStepDevissage

/-! ### The two conditions of `Module.DevissageStageData.Pointed` -/

namespace OneStepDevissageAt

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The point of the fibre ring corresponding to the chosen prime of `Γ(Y, ⊤)` belongs to the
support of the fibre module.** This is the field
`Module.DevissageStageData.Pointed.lowerPrime_mem_fiberSupport` for the stage
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds, in the exact shape that structure
records it. -/
public theorem lowerPrime_mem_fiberSupport (D : OneStepDevissageAt f F x)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (hover : letI := D.toOneStepDevissage.algebraSmooth
      qY.LiesOver r) :
    letI := D.toOneStepDevissage.algebraSmooth
    letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
      Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
    letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    (PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
        ⟨qY, hqYp, hover⟩) ∈
      Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
        (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
          (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤)) := by
  let _ := D.toOneStepDevissage.affine_Y
  let _ := D.toOneStepDevissage.affine_Z
  let _ := D.toOneStepDevissage.algebraSmooth
  let _ := D.toOneStepDevissage.algebraFinite
  let _ : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
    Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
  have htYG : IsScalarTower Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.Z, ⊤)
      Γ(D.toOneStepDevissage.G, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfinYZ : Module.Finite Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.Z, ⊤) :=
    D.toOneStepDevissage.finite_π_appTop
  have hfinYG : Module.Finite Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
    Module.Finite.trans Γ(D.toOneStepDevissage.Z, ⊤) Γ(D.toOneStepDevissage.G, ⊤)
  exact (Module.primesOverOrderIsoFiber_mem_support_iff Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤)
      Γ(D.toOneStepDevissage.G, ⊤) r qY hover).2
    (D.toOneStepDevissage.mem_fiberSupport_lowerPrime D.z D.y D.i_z D.π_z
      D.mem_fiber_support r hr qY hqY).1

/-- **The dimension of the support of the fibre module is its local dimension at the chosen
prime of the smooth algebra.**

The one-step dévissage is taken *at* `x`, so the local dimension of the support of `ℱ_s` at `x`
is its dimension; and the support of the fibre module over the fibre ring of `Γ(Y, ⊤)`, at the
point of `qY`, has that same local dimension, by the two comparisons
`AlgebraicGeometry.OneStepDevissage.topologicalKrullDimAt_fiberSupport_lowerPrime` and
`Module.topologicalKrullDimAt_support_fiber`. -/
public theorem topologicalKrullDim_supp_eq_support (D : OneStepDevissageAt f F x)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (hover : letI := D.toOneStepDevissage.algebraSmooth
      qY.LiesOver r)
    (hmem : letI := D.toOneStepDevissage.algebraSmooth
      letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
        Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
      letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
        Algebra.TensorProduct.rightAlgebra
      (PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
          ⟨qY, hqYp, hover⟩) ∈
        Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤))) :
    letI := D.toOneStepDevissage.algebraSmooth
    letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
      Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
    letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) =
      topologicalKrullDimAt
        ↥(Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤)))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
            ⟨qY, hqYp, hover⟩, hmem⟩ := by
  let _ := D.toOneStepDevissage.affine_Y
  let _ := D.toOneStepDevissage.affine_Z
  let _ := D.toOneStepDevissage.algebraSmooth
  let _ := D.toOneStepDevissage.algebraFinite
  let _ : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
    Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
  have htYG : IsScalarTower Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.Z, ⊤)
      Γ(D.toOneStepDevissage.G, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfinYZ : Module.Finite Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.Z, ⊤) :=
    D.toOneStepDevissage.finite_π_appTop
  have hfinYG : Module.Finite Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
    Module.Finite.trans Γ(D.toOneStepDevissage.Z, ⊤) Γ(D.toOneStepDevissage.G, ⊤)
  have hmemY := (D.toOneStepDevissage.mem_fiberSupport_lowerPrime D.z D.y D.i_z D.π_z
    D.mem_fiber_support r hr qY hqY)
  calc topologicalKrullDim (SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
      = topologicalKrullDimAt (SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
          ⟨f.asFiber x, D.mem_fiber_support⟩ := D.dimension.symm
    _ = topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤)
          Γ(D.toOneStepDevissage.G, ⊤) r) ⟨⟨qY, hqYp⟩, hmemY⟩ :=
        (D.toOneStepDevissage.topologicalKrullDimAt_fiberSupport_lowerPrime D.z D.y D.i_z
          D.π_z D.fiber_eq_singleton D.mem_fiber_support r hr qY hqY hmemY).symm
    _ = topologicalKrullDimAt
          ↥(Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
            (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
              (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤)))
          ⟨PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
            ⟨qY, hqYp, hover⟩, hmem⟩ := by
        refine Eq.symm ((Module.topologicalKrullDimAt_support_fiber Γ(S, ⊤)
          Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) r hmem).trans ?_)
        exact congrArg _ (Subtype.ext (PrimeSpectrum.comap_primesOverOrderIsoFiber Γ(S, ⊤)
          Γ(D.toOneStepDevissage.Y, ⊤) r qY hover))

/-- **Stacks 05HZ (4) for one stage.** Every fibre of `Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` has the
local dimension of the support of the fibre module at the chosen prime of `Γ(Y, ⊤)`.

This is `Module.DevissageStageData.Pointed.topologicalKrullDim_fiber_eq_support` for the stage
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds, in the shape that theorem states
it. It is the fibre-dimension condition of Stacks 05H4 (5), which
`AlgebraicGeometry.OneStepDevissage.fiber_dimension` records, read on rings. -/
public theorem topologicalKrullDim_fiber_eq_support (D : OneStepDevissageAt f F x)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (hover : letI := D.toOneStepDevissage.algebraSmooth
      qY.LiesOver r)
    (hmem : letI := D.toOneStepDevissage.algebraSmooth
      letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
        Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
      letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
        Algebra.TensorProduct.rightAlgebra
      (PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
          ⟨qY, hqYp, hover⟩) ∈
        Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤))) :
    letI := D.toOneStepDevissage.algebraSmooth
    letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
      Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
    letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    ∀ p : PrimeSpectrum Γ(S, ⊤),
      topologicalKrullDim ↥(PrimeSpectrum.comap
          (algebraMap Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤)) ⁻¹' {p}) =
        topologicalKrullDimAt
        ↥(Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤)))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
            ⟨qY, hqYp, hover⟩, hmem⟩ :=
  fun p => (D.toOneStepDevissage.topologicalKrullDim_fiber_eq_topologicalKrullDim_supp p).trans
    (D.topologicalKrullDim_supp_eq_support r hr qY hqY hover hmem)

/-- **Stacks 05HZ (4) for one stage, with the relative dimension read as a single supremum.**
The relative dimension of the functions on the smooth scheme over the functions on the base is
the local dimension of the support of the fibre module at the chosen prime of `Γ(Y, ⊤)`.

This is `AlgebraicGeometry.OneStepDevissageAt.topologicalKrullDim_fiber_eq_support` with the
supremum of Definition 00QD taken over the fibres. -/
public theorem relativeDimension_eq_support (D : OneStepDevissageAt f F x)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [hqYp : qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (hover : letI := D.toOneStepDevissage.algebraSmooth
      qY.LiesOver r)
    (hmem : letI := D.toOneStepDevissage.algebraSmooth
      letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
        Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
      letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
        Algebra.TensorProduct.rightAlgebra
      (PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
          ⟨qY, hqYp, hover⟩) ∈
        Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤))) :
    letI := D.toOneStepDevissage.algebraSmooth
    letI : Module Γ(D.toOneStepDevissage.Y, ⊤) Γ(D.toOneStepDevissage.G, ⊤) :=
      Module.compHom Γ(D.toOneStepDevissage.G, ⊤) D.toOneStepDevissage.π.appTop.hom
    letI : Algebra Γ(D.toOneStepDevissage.Y, ⊤) (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    Algebra.relativeDimension Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) =
      topologicalKrullDimAt
        ↥(Module.support (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤))
          (TensorProduct Γ(D.toOneStepDevissage.Y, ⊤)
            (r.Fiber Γ(D.toOneStepDevissage.Y, ⊤)) Γ(D.toOneStepDevissage.G, ⊤)))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber Γ(S, ⊤) Γ(D.toOneStepDevissage.Y, ⊤) r
            ⟨qY, hqYp, hover⟩, hmem⟩ :=
  (D.toOneStepDevissage.relativeDimension_eq_topologicalKrullDim_supp).trans
    (D.topologicalKrullDim_supp_eq_support r hr qY hqY hover hmem)

end OneStepDevissageAt

end AlgebraicGeometry

end
