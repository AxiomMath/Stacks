module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalFunctionsTransport

/-!
# Transport of embeddings of the function field along a bijection of prime divisors

Let `X` and `Y` be decent algebraic spaces with a bijection `π` of their prime divisors, an
identification `R(Y) ≃+* R(X)` of their rings of rational functions, and identifications of the
total fraction rings at the generic points of corresponding prime divisors. Then a family of
embeddings `R(X) → Q(𝒪^h_{X,ξ_Z})` indexed by the prime divisors of `X` is carried to a family
indexed by the prime divisors of `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_embedding_transport_of_primeDivisorEquiv`: a family of
  embeddings of the function field indexed by the prime divisors of `X` is carried to one indexed
  by the prime divisors of `Y`.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Transport of a family of embeddings along a bijection of prime divisors -/

section EmbeddingTransport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)

/-- Given a bijection `π` of the prime divisors of `X` with those of `Y`, an identification
`R(Y) ≃+* R(X)` of the rings of rational functions, and at every prime divisor `Z` of `X` an
identification `Q(𝒪^h_{Y,ξ_{π Z}}) ≃+* Q(𝒪^h_{X,ξ_Z})` of the total fraction rings at the generic
points, a family of embeddings indexed by the prime divisors of `X` is carried to one indexed by
the prime divisors of `Y`, whose member at `π Z` sends `g` to `(φ Z).symm (emb Z (eR g))`. -/
theorem exists_embedding_transport_of_primeDivisorEquiv
    (π : PrimeDivisor B S hS X ≃ PrimeDivisor B S hS Y)
    (eR : rationalFunctions B S hS hY ≃+* rationalFunctions B S hS hX)
    (φ : ∀ Z : PrimeDivisor B S hS X,
      (π Z).genericTotalFractionRing B S hS hY hYdec ≃+*
        Z.genericTotalFractionRing B S hS hX hXdec)
    (emb : ∀ Z : PrimeDivisor B S hS X,
      rationalFunctions B S hS hX →+* Z.genericTotalFractionRing B S hS hX hXdec) :
    ∃ embY : ∀ Z' : PrimeDivisor B S hS Y,
      rationalFunctions B S hS hY →+* Z'.genericTotalFractionRing B S hS hY hYdec,
      ∀ (Z : PrimeDivisor B S hS X) (g : rationalFunctions B S hS hY),
        embY (π Z) g = (φ Z).symm (emb Z (eR g)) :=
  ⟨Equiv.piCongrLeft _ π fun Z => (φ Z).symm.toRingHom.comp ((emb Z).comp eR.toRingHom),
    fun Z g => DFunLike.congr_fun (Equiv.piCongrLeft_apply_apply
      (fun Z' : PrimeDivisor B S hS Y =>
        rationalFunctions B S hS hY →+* Z'.genericTotalFractionRing B S hS hY hYdec) π _ Z) g⟩

end EmbeddingTransport

end AlgebraicGeometry.Space

end
