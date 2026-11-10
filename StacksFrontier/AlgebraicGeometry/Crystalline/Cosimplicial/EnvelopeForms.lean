module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope

/-!
# The bigraded family `Ω^a_{D(b)}` of the cosimplicial envelope

`Crystalline.CosimplicialDPAlgebra` is the input the bigraded family of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/BigradedForms.lean` is built from.  This
module exhibits the cosimplicial envelope of a polynomial presentation as one, so that the
bigraded family `Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] — with its de Rham
differential in the `a` direction, its wedge product, and its transition maps in the `b`
direction commuting with both — exists for the actual rings `D(b)` of
[Stacks, Equation 60.17.3, Tag 07JF] and not only for a carried family.

The carriers are the *uncompleted* divided power envelopes
`Crystalline.tensorPowerEnvelope`: the `p`-adic completion is what
`Crystalline.CosimplicialDPAlgebra.forms` takes, so the forms come out as the completion of the
exterior power, which is the shape of `Crystalline.completedDividedPowerDeRhamComplex` and hence
of the target complex `M ⊗^∧_D Ω^*_D` of the tag.  The transition maps are
`Crystalline.envelopeReindex`, the same reindexing divided power morphisms
`Crystalline.cosimplicialEnvelopeRing` is the completion of; their functoriality is
`Crystalline.envelopeReindex_id` and `Crystalline.envelopeReindex_comp`.

## Main definitions

* `Crystalline.envelopeDPAlgebra` — **the cosimplicial envelope as a cosimplicial family of
  divided power `A`-algebras.**
* `Crystalline.envelopeForms` — **the bigraded family `Ω^a_{D(b)}`** of the cosimplicial
  envelope, with `Crystalline.envelopeFormsDeRham`,
  `Crystalline.envelopeFormsWedge` and `Crystalline.envelopeFormsMap` naming its three structure
  maps.

## Main results

* `Crystalline.envelopeFormsMap_deRham` — **the de Rham differential in the `a` direction and the
  cosimplicial transition maps in the `b` direction commute**, for the actual `D(*)`.
* `Crystalline.envelopeFormsMap_wedge`, `Crystalline.envelopeFormsMap_id`,
  `Crystalline.envelopeFormsMap_comp` — and the remaining structure of the bigraded family.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
-/

@[expose] public section

open CategoryTheory DividedPowers

universe u v w

namespace Crystalline

section Envelope

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The `A`-algebra structure on the divided power envelope of the `(b + 1)`-fold tensor power
presentation, given by its structure map. -/
public noncomputable abbrev tensorPowerEnvelopeAlgebraInstance (b : ℕ) :
    Algebra (s.A : Type u) (tensorPowerEnvelope s f b).object :=
  (tensorPowerEnvelope s f b).structureMap.toRingHom.toAlgebra

/-- The reindexing divided power morphism `D(m)_env → D(n)_env` read as an `A`-algebra map: it
commutes with the two structure maps from the base, which is the second component of
`Crystalline.envelopeReindex`. -/
public noncomputable def envelopeReindexAlgHomOfSimplex {m n : SimplexCategory} (φ : m ⟶ n) :
    letI := tensorPowerEnvelopeAlgebraInstance s f m.len
    letI := tensorPowerEnvelopeAlgebraInstance s f n.len
    (tensorPowerEnvelope s f m.len).object →ₐ[(s.A : Type u)]
      (tensorPowerEnvelope s f n.len).object :=
  letI := tensorPowerEnvelopeAlgebraInstance s f m.len
  letI := tensorPowerEnvelopeAlgebraInstance s f n.len
  { __ := (envelopeReindex s f φ).1.toRingHom
    commutes' := fun a =>
      congrArg (fun q : DividedPowers.DPMorphism _ _ => q.toRingHom a) (envelopeReindex s f φ).2 }

/-- **The cosimplicial envelope as a cosimplicial family of divided power `A`-algebras.**  Its
degree `b` is the uncompleted divided power envelope of the kernel of
`P ⊗_A ⋯ ⊗_A P → C` on the `(b + 1)`-fold tensor power, and its transition maps are the
reindexing divided power morphisms `Crystalline.envelopeReindex`. -/
public noncomputable def envelopeDPAlgebra :
    CosimplicialDPAlgebra.{u, max u w} (s.A : Type u) where
  carrier b := (tensorPowerEnvelope s f b).object
  commRing _ := inferInstance
  algebra b := tensorPowerEnvelopeAlgebraInstance s f b
  ideal b := (tensorPowerEnvelope s f b).object.ideal
  dividedPowers b := (tensorPowerEnvelope s f b).object.dividedPowers
  map φ := envelopeReindexAlgHomOfSimplex s f φ
  map_isDPMorphism φ := (envelopeReindex s f φ).1.isDPMorphism
  map_id n := AlgHom.toRingHom_injective (RingHom.ext (envelopeReindex_id s f n))
  map_comp φ ψ := AlgHom.toRingHom_injective (RingHom.ext (envelopeReindex_comp s f φ ψ))

/-- **The bigraded family `Ω^a_{D(b)}`** of the cosimplicial envelope: the `p`-adic completion of
the `a`-th exterior power of the divided power differentials of `D(b)`. -/
public noncomputable abbrev envelopeForms (a b : ℕ) : Type (max u w) :=
  (envelopeDPAlgebra s f).forms s.p a b

/-- **The de Rham differential `Ω^a_{D(b)} → Ω^{a+1}_{D(b)}`** of the forms of the cosimplicial
envelope. -/
public noncomputable def envelopeFormsDeRham (b a : ℕ) :
    envelopeForms s f a b →+ envelopeForms s f (a + 1) b :=
  (envelopeDPAlgebra s f).deRham s.p b a

/-- **The wedge product `Ω^a_{D(b)} × Ω^1_{D(b)} → Ω^{a+1}_{D(b)}`** of the forms of the
cosimplicial envelope, in the bidegree the completed de Rham complex is built from. -/
public noncomputable def envelopeFormsWedge (b a : ℕ) :
    envelopeForms s f a b →ₗ[completedDividedPowerRing s.p
        (B := (envelopeDPAlgebra s f).carrier b)]
      envelopeForms s f 1 b →ₗ[completedDividedPowerRing s.p
          (B := (envelopeDPAlgebra s f).carrier b)]
        envelopeForms s f (a + 1) b :=
  (envelopeDPAlgebra s f).wedge s.p b a

/-- **The transition map `Ω^a_{D(m)} → Ω^a_{D(n)}`** of the forms of the cosimplicial envelope. -/
public noncomputable def envelopeFormsMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) :
    envelopeForms s f a m.len →ₛₗ[((envelopeDPAlgebra s f).map φ).toRingHom]
      envelopeForms s f a n.len :=
  (envelopeDPAlgebra s f).formsMap s.p φ a

/-- **The de Rham differential in the `a` direction commutes with the cosimplicial transition
maps in the `b` direction**, for the actual rings `D(*)`.  This is the commutation the double
complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}` of [Stacks, Tag 07LG] rests on. -/
public theorem envelopeFormsMap_deRham {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : envelopeForms s f a m.len) :
    envelopeFormsMap s f φ (a + 1) (envelopeFormsDeRham s f m.len a x) =
      envelopeFormsDeRham s f n.len a (envelopeFormsMap s f φ a x) :=
  (envelopeDPAlgebra s f).formsMap_deRham s.p φ a x

/-- The cosimplicial transition maps respect the wedge product. -/
public theorem envelopeFormsMap_wedge {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : envelopeForms s f a m.len) (y : envelopeForms s f 1 m.len) :
    envelopeFormsMap s f φ (a + 1) (envelopeFormsWedge s f m.len a x y) =
      envelopeFormsWedge s f n.len a (envelopeFormsMap s f φ a x) (envelopeFormsMap s f φ 1 y) :=
  (envelopeDPAlgebra s f).formsMap_wedge s.p φ a x y

/-- The transition map of an identity is the identity. -/
public theorem envelopeFormsMap_id (n : SimplexCategory) (a : ℕ)
    (x : envelopeForms s f a n.len) : envelopeFormsMap s f (𝟙 n) a x = x :=
  (envelopeDPAlgebra s f).formsMap_id s.p n a x

/-- The transition maps compose. -/
public theorem envelopeFormsMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) (a : ℕ)
    (x : envelopeForms s f a m.len) :
    envelopeFormsMap s f (φ ≫ ψ) a x =
      envelopeFormsMap s f ψ a (envelopeFormsMap s f φ a x) :=
  (envelopeDPAlgebra s f).formsMap_comp s.p φ ψ a x

end Envelope

end Crystalline

end
