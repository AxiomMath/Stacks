module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleJacobsonQuotient

/-!
# W-contractibility of a closed subscheme meeting every specialization chain

Let `j : W ⟶ U` be a closed immersion of affine schemes all of whose points specialize into the
closed subscheme, i.e. every point of `U` admits a point of `W` in the closure of its singleton.
Then the ideal cutting out `W` lies in the Jacobson radical of `Γ(U, ⊤)`, and w-contractibility of
`Γ(U, ⊤)` passes to `Γ(W, ⊤)`.

## Main results

* `AlgebraicGeometry.ProEtale.le_ringJacobson_ker_appTop_of_specializes` and
  `AlgebraicGeometry.ProEtale.le_ringJacobson_appTopKer_of_specializes`: the ideal of the closed
  subscheme lies in the Jacobson radical of the ring of global sections of the target, stated for
  schemes and for the objects of a chosen big pro-étale site.
* `AlgebraicGeometry.ProEtale.exists_specializes_of_ker_appTop_le_ringJacobson`: conversely, if
  that ideal lies in the Jacobson radical then every point specializes into the closed
  subscheme.
* `AlgebraicGeometry.ProEtale.isWContractible_appTop_of_specializes` and
  `AlgebraicGeometry.ProEtale.isWContractible_appTop_of_isWContractible_of_specializes`:
  w-contractibility of the ring of global sections passes to the closed subscheme, again stated
  for schemes and for the objects of a chosen big pro-étale site.

## Implementation notes

The Jacobson radical is the infimum of the maximal ideals, so the first result is checked at a
maximal ideal `m` of `A = Γ(U, ⊤)`. The corresponding point of `Spec A` is closed, hence so is the
point `x` of `U` it comes from under `AlgebraicGeometry.Scheme.isoSpec`; a specialization of `x`
into the closed subscheme therefore *is* `x`, exhibiting `x` in the image of the closed immersion.
Reading that image on `Spec A` identifies it with the zero locus of the kernel of `j.appTop`, the
morphism of global sections being surjective because `U` is affine, and so that kernel is
contained in `m`.

The second result then quotes w-contractibility of a quotient by an ideal inside the Jacobson
radical and transports it along the isomorphism between `A` modulo that kernel and `Γ(W, ⊤)`
coming from surjectivity of `j.appTop`.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

/-- Under the affine identifications `isoSpec`, `j` is `Spec.map j.appTop` on underlying points. -/
private theorem isoSpec_hom_base_map {W U : Scheme.{u}} (j : W ⟶ U) [IsAffine U] [IsAffine W]
    (w : W) : U.isoSpec.hom.base (j.base w) = (Spec.map j.appTop).base (W.isoSpec.hom.base w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply]

/-- **The ideal of a closed subscheme swallowing every specialization lies in the Jacobson
radical.** Let `j : W ⟶ U` be a closed immersion of affine schemes such that every point of `U`
specializes to a point of `W`. A maximal ideal `m` of `A = Γ(U, ⊤)` is a closed point of
`Spec A`, hence corresponds to a closed point `x` of `U`; the hypothesis gives a point of `W`
whose image lies in the closure of `{x}`, which is `{x}` itself, so `x` lies in the image of `j`.
That image is the zero locus of `RingHom.ker j.appTop.hom`, because `j.appTop` is surjective, and
so this kernel is contained in `m`. -/
theorem le_ringJacobson_ker_appTop_of_specializes {W U : Scheme.{u}} (j : W ⟶ U)
    [IsAffine U] [IsAffine W] [IsClosedImmersion j]
    (hspec : ∀ x : U, ∃ w : W, x ⤳ j.base w) :
    RingHom.ker j.appTop.hom ≤ Ring.jacobson Γ(U, ⊤) := by
  have hsurj : Function.Surjective j.appTop.hom := surjective_appTop_hom j
  rw [Ring.jacobson_eq_sInf_isMaximal]
  refine le_sInf fun m hm => ?_
  have hmm : m.IsMaximal := hm
  -- The closed point of `Spec Γ(U, ⊤)` cut out by `m`.
  let p : ↥(Spec Γ(U, ⊤)) := ⟨m, hmm.isPrime⟩
  have hclosed : IsClosed ({p} : Set ↥(Spec Γ(U, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 hmm
  obtain ⟨w, hw⟩ := hspec (U.isoSpec.inv.base p)
  have hmap := hw.map (f := U.isoSpec.hom.base) U.isoSpec.hom.base.hom.continuous
  rw [show U.isoSpec.hom.base (U.isoSpec.inv.base p) = p by
    rw [← Scheme.Hom.comp_apply, U.isoSpec.inv_hom_id]; rfl] at hmap
  -- A specialization of a closed point is that point.
  have hmem : (Spec.map j.appTop).base (W.isoSpec.hom.base w) = p := by
    rw [← isoSpec_hom_base_map]
    exact hmap.mem_closed hclosed rfl
  have hrange : (⟨m, hmm.isPrime⟩ : PrimeSpectrum ↥Γ(U, ⊤)) ∈
      Set.range (PrimeSpectrum.comap j.appTop.hom) := ⟨W.isoSpec.hom.base w, hmem⟩
  rwa [_root_.range_comap_of_surjective _ _ hsurj] at hrange

/-- **Every point specializes into a closed subscheme whose ideal lies in the Jacobson
radical.** This is the converse of `le_ringJacobson_ker_appTop_of_specializes`: if the kernel of
the surjection `Γ(U, ⊤) → Γ(W, ⊤)` lies in the Jacobson radical, then the prime corresponding to a
point of `U` lies in a maximal ideal, which contains that kernel and hence is the image of a
point of `W`. -/
theorem exists_specializes_of_ker_appTop_le_ringJacobson {W U : Scheme.{u}} (j : W ⟶ U)
    [IsAffine U] [IsAffine W] [IsClosedImmersion j]
    (hI : RingHom.ker j.appTop.hom ≤ Ring.jacobson Γ(U, ⊤)) (x : U) :
    ∃ w : W, x ⤳ j.base w := by
  have hsurj : Function.Surjective j.appTop.hom := surjective_appTop_hom j
  set p : PrimeSpectrum Γ(U, ⊤) := U.isoSpec.hom.base x with hp
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have hker : RingHom.ker j.appTop.hom ≤ m := by
    refine hI.trans ?_
    rw [Ring.jacobson_eq_sInf_isMaximal]
    exact sInf_le hm
  have hrange : (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(U, ⊤)) ∈
      Set.range (PrimeSpectrum.comap j.appTop.hom) := by
    rwa [_root_.range_comap_of_surjective _ _ hsurj]
  obtain ⟨q, hq⟩ := hrange
  let q' : Spec Γ(W, ⊤) := q
  refine ⟨W.isoSpec.inv.base q', ?_⟩
  have hspec : p ⤳ ⟨m, hm.isPrime⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h1 : U.isoSpec.hom.base (j.base (W.isoSpec.inv.base q')) = ⟨m, hm.isPrime⟩ := by
    rw [isoSpec_hom_base_map, ← Scheme.Hom.comp_apply W.isoSpec.inv, W.isoSpec.inv_hom_id]
    exact hq
  have hmap := hspec.map (f := U.isoSpec.inv.base) U.isoSpec.inv.base.hom.continuous
  rw [← h1, hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, U.isoSpec.hom_inv_id] at hmap
  simpa using hmap

/-- **W-contractibility passes to a closed subscheme swallowing every specialization.** The ideal
`I` cutting out `W` lies in the Jacobson radical of `A = Γ(U, ⊤)`, so `A ⧸ I` is w-contractible;
and `Γ(W, ⊤)` is isomorphic to `A ⧸ I`, the morphism `j.appTop` being surjective with kernel
`I`. -/
theorem isWContractible_appTop_of_specializes {W U : Scheme.{u}} (j : W ⟶ U)
    [IsAffine U] [IsAffine W] [IsClosedImmersion j]
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(U, ⊤))
    (hspec : ∀ x : U, ∃ w : W, x ⤳ j.base w) :
    ProetaleWContractible.IsWContractible.{u, u} Γ(W, ⊤) :=
  isWContractible_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (surjective_appTop_hom j)).symm
    (isWContractible_quotient_of_le_ringJacobson _ hA _
      (le_ringJacobson_ker_appTop_of_specializes j hspec))

variable (B : BigProetaleSite.{u}) {W U : B.Scheme} (j : W ⟶ U)
  [IsAffine U.obj] [IsAffine W.obj] [IsClosedImmersion (B.inclusion.map j)]

private instance isAffine_inclusion_obj (X : B.Scheme) [IsAffine X.obj] :
    IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›

/-- **Stacks 09AC, the Jacobson radical assertion for a big pro-étale site.** For a closed
immersion of affine objects of a chosen big pro-étale site all of whose points specialize into the
closed subobject, the ideal cutting out the closed subobject lies in the Jacobson radical of the
ring of global sections of the target. -/
theorem le_ringJacobson_appTopKer_of_specializes
    (hspec : ∀ x : U.obj, ∃ w : W.obj, x ⤳ (B.inclusion.map j).base w) :
    RingHom.ker (B.inclusion.map j).appTop.hom ≤ Ring.jacobson Γ(U.obj, ⊤) := by
  exact le_ringJacobson_ker_appTop_of_specializes (B.inclusion.map j) hspec

/-- **Stacks 09AC, the w-contractibility assertion for a big pro-étale site.** For a closed
immersion of affine objects of a chosen big pro-étale site all of whose points specialize into the
closed subobject, w-contractibility of the ring of global sections of the target passes to the
ring of global sections of the closed subobject. -/
theorem isWContractible_appTop_of_isWContractible_of_specializes
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(U.obj, ⊤))
    (hspec : ∀ x : U.obj, ∃ w : W.obj, x ⤳ (B.inclusion.map j).base w) :
    ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj, ⊤) := by
  exact isWContractible_appTop_of_specializes (B.inclusion.map j) hA hspec

end AlgebraicGeometry.ProEtale

end
