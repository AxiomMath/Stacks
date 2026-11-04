module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeComputesCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CrystalDeRhamPairs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDoubleComplex

/-!
# The Čech–de Rham double complex of a crystal for a cover by smooth lifts

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `p` nilpotent in
`A = Γ(S, 𝒪_S)` and `X` separated, a family `U_i` of affine opens of `X` and smooth lifts `L_i`
of them (`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`), with objects
`D_i = (U_i, Spec B_i, γ_i)` of `Cris(X/S)`.  Their finite products `D_x = D_{x 0} × ⋯ × D_{x n}`
are the divided power envelopes of `U_x` in `Y_{x 0} ×_S ⋯ ×_S Y_{x n}`
(`CechEnvelope.isLimitFan`); they lie in `Cris(X/S)` and have affine ambient scheme, so they are
products in the full subcategory `AffineCris S` of such objects.

For a quasi-coherent module `N` on `CRIS(X/S)`, every `T` in `AffineCris S` carries the de Rham
complex `N(T) ⊗ Ω^•_{Γ(T)/A,δ}` of the canonical connection of [Stacks, Tag 07J6]
(`...bigCrystalDeRhamPresheaf`), and the **Čech–de Rham double complex**

`B^{a}(⦋n⦌) = ∏_{x : Fin (n + 1) → ι} N(D_x) ⊗ Ω^a_{D_x}`

is the double complex of [Stacks, Proposition 60.21.3, Tag 07LG] for the cover by the `D_i`
(`CechEnvelope.cechDeRhamDoubleComplex`), in the shape `CochainComplex (CosimplicialObject _) ℕ`
consumed by `Crystalline.CosimplicialDoubleComplex.functor`.

## Main definitions

* `CechEnvelope.crisObject`, `CechEnvelope.affineObject` — `D_i` in `Cris(X/S)` and in
  `AffineCris S`.
* `CechEnvelope.cechDeRhamDoubleComplex` — the Čech–de Rham double complex.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

/-- **The object `D_i` of a smooth lift, in `Cris(X/S)`.** -/
def crisObject (i : ι) : CrystallineThickening S :=
  ⟨(L i).object hp, inferInstanceAs (IsOpenImmersion ((L i).object hp).toX)⟩

/-- **The object `D_i` of a smooth lift, in `AffineCris S`.** -/
def affineObject (i : ι) : AffineCris S :=
  ⟨crisObject hp L i, inferInstanceAs (IsAffine ((L i).object hp).thickening.target.scheme)⟩

/-- The envelope object of a tuple of smooth lifts, in `Cris(X/S)`. -/
def crisEnvelopeObject {n : ℕ} (x : Fin (n + 1) → ι) : CrystallineThickening S :=
  ⟨envelopeObject hp (fun a ↦ L (x a)),
    inferInstanceAs (IsOpenImmersion (envelopeObject hp (fun a ↦ L (x a))).toX)⟩

/-- **The envelope object is a product of the `D_{x a}` in `Cris(X/S)`**: the inclusion into
`CRIS(X/S)` is fully faithful and carries the fan to the limit fan `isLimitFan`. -/
def isLimitCrisFan {n : ℕ} (x : Fin (n + 1) → ι) :
    IsLimit (Fan.mk (crisEnvelopeObject hp L x)
      (fun a ↦ ObjectProperty.homMk (proj hp (fun a ↦ L (x a)) a)) :
        Fan fun a ↦ crisObject hp L (x a)) :=
  Fan.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk
      (Fan.IsLimit.lift (isLimitFan hp (fun a ↦ L (x a))) fun a ↦ (s.proj a).hom))
    (fun s a ↦ by
      ext1
      exact Fan.IsLimit.fac (isLimitFan hp (fun a ↦ L (x a))) _ a)
    (fun s m hm ↦ by
      ext1
      refine Fan.IsLimit.hom_ext (isLimitFan hp (fun a ↦ L (x a))) _ _ fun a ↦ ?_
      exact (congrArg (fun g ↦ g.hom) (hm a)).trans
        (Fan.IsLimit.fac (isLimitFan hp (fun a ↦ L (x a))) (fun a ↦ (s.proj a).hom) a).symm)

/-- The objects of the smooth lifts have finite products in `Cris(X/S)`. -/
instance hasProduct_crisObject {n : ℕ} (x : Fin (n + 1) → ι) :
    HasProduct fun a ↦ crisObject hp L (x a) :=
  HasLimit.mk ⟨_, isLimitCrisFan hp L x⟩

/-- The objects of the smooth lifts have finite products in `AffineCris S`: the product in
`Cris(X/S)` is the envelope object, whose ambient scheme is affine. -/
instance hasProduct_affineObject {n : ℕ} (x : Fin (n + 1) → ι) :
    HasProduct fun a ↦ affineObject hp L (x a) :=
  Stacks.CechSite.FinalCover.hasProduct_fullSubcategory_of_isLimit _ (isLimitCrisFan hp L x)
    (inferInstanceAs (IsAffine (envelopeObject hp (fun a ↦ L (x a))).thickening.target.scheme))

/-- **The Čech–de Rham double complex `B^a(⦋n⦌) = ∏_x N(D_x) ⊗ Ω^a_{D_x}`** of a quasi-coherent
module `N` on `CRIS(X/S)` for the cover by the smooth-lift objects `D_i`, in the shape consumed by
`Crystalline.CosimplicialDoubleComplex.functor`. -/
def cechDeRhamDoubleComplex (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (hN : N.IsQuasicoherentOnSite) :
    CochainComplex (CosimplicialObject (ModuleCat.{u} Γ(S.S.scheme, ⊤))) ℕ :=
  Stacks.CechSite.FinalCover.doubleComplex (affineObject hp L) (bigCrystalDeRhamPresheaf hN)

end Crystalline.GlobalCrystallineSituation.CechEnvelope
