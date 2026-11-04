module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem

/-!
# Transporting the ring of rational functions along a monomorphism of integral spaces

Let `f : X ⟶ Y` be a morphism of integral algebraic spaces over `S` carrying the generic point
of `X` to the generic point of `Y`. The extension of function fields it induces,
`AlgebraicGeometry.Space.rationalFunctionMap`, is the homomorphism of residue fields at the
generic points read through the identification of Stacks 0END of the ring of rational functions
with that residue field. So it is bijective as soon as that homomorphism of residue fields is,
and by Stacks 0EMX the latter is bijective whenever the morphism from the spectrum of the
residue field of `X` at the generic point to `Y` is a monomorphism — which holds for `f` a
monomorphism, the representative of a point of a decent algebraic space being monomorphic by
Stacks 0EMW.

This file makes that observation into a ring isomorphism `R(Y) ≃+* R(X)`, whose underlying
homomorphism is `AlgebraicGeometry.Space.rationalFunctionMap` itself and not a reconstruction of
it, so that every statement already proved about the extension of function fields — the
naturality of the embedding of Stacks 0ENK along a flat dominant morphism in particular — reads
directly as a statement about the isomorphism.

For an isomorphism `e : X ≅ Y` of integral algebraic spaces nothing further is assumed: the
generic point goes to the generic point by
`AlgebraicGeometry.Space.pointsMap_genericPoint_of_isIso`. This is the space-level counterpart
of `Stacks.Chow.rationalFunctionsRingEquivOfIso`.

## Main definitions

* `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfMono`: the transport `R(Y) ≃+* R(X)` of
  the ring of rational functions of Stacks 0EMP along a monomorphism of integral algebraic
  spaces carrying the generic point to the generic point.
* `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso`: the same for an isomorphism of
  integral algebraic spaces, with the condition on the generic points discharged.

## Main results

* `AlgebraicGeometry.Space.bijective_residueFieldHom_of_mono`: **Stacks 0EMX for a
  monomorphism** — a monomorphism of decent algebraic spaces induces a bijection of residue
  fields at every point of its source.
* `AlgebraicGeometry.Space.bijective_rationalFunctionMap_of_mono`: the extension of function
  fields along such a monomorphism is bijective.
* `AlgebraicGeometry.Space.isDominant_of_isIso`: an isomorphism of algebraic spaces is
  dominant, its map on points being surjective by the base's
  `AlgebraicGeometry.Space.surjective_pointsMap_of_isIso`.
* `AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality_of_isIso`: the
  naturality of the embedding of Stacks 0ENK, for an isomorphism — the flatness hypothesis of
  `AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality` is discharged by
  `AlgebraicGeometry.Space.isFlat_of_isIso`, and the extension of function fields in it is the
  isomorphism built here.

## Implementation notes

The isomorphism is produced as `RingEquiv.ofBijective` of
`AlgebraicGeometry.Space.rationalFunctionMap`, so that
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfMono_apply` is a definitional identity.
Building it instead out of the three isomorphisms `R(Y) ≃+* κ(η_Y)`, `κ(η_Y) ≃+* κ(f(η_X))`,
`κ(f(η_X)) ≃+* κ(η_X)` and `κ(η_X) ≃+* R(X)` would give the same map, but only up to a lemma,
and the naturality square of Stacks 0ENK is stated for `rationalFunctionMap`.

The monomorphism hypothesis is an instance argument, as for
`AlgebraicGeometry.Space.residueFieldDegreeAt_eq_one_of_mono`, so that it is found by
instance search at an isomorphism.

What this file does *not* do is transport the predicate
`AlgebraicGeometry.Space.IsPrincipalDivisorCycle`. That predicate reads a rational function
through the embeddings `R(V) → Q(𝒪^h_{V,ξ})` of Stacks 0ENK at the generic points of the prime
divisors of `V`, and its coefficients are orders of vanishing computed there; carrying it along
an isomorphism `V ≅ V'` needs, beyond the isomorphism of rings of rational functions built here,
a correspondence of the prime divisors of `V` with those of `V'` and the invariance of
`AlgebraicGeometry.Space.PrimeDivisor.ord` along it. The available naturality,
`AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality`, applies to an
isomorphism — that is the last result below — but it quantifies the homomorphism
`φ : 𝒪^h_{V',ξ'} ⟶ 𝒪^h_{V,ξ}` of henselian local rings existentially and says only that it is
flat and local, and the companion Stacks 0EQA then gives
`ord_ξ(g ∘ e) = m · ord_{ξ'}(g)` with `m` the multiplicity of that `φ`. Nothing states that the
`φ` an isomorphism induces is itself an isomorphism, so `m = 1` is not available and the orders
of vanishing on the two sides are not yet identified.

## References

* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The residue field extension of a monomorphism -/

/-- **Stacks 0EMX for a monomorphism.** A monomorphism of decent algebraic spaces over `S`
induces a bijection from the residue field of the target at the image of a point onto the
residue field of the source at that point.

The representative of a point of a decent algebraic space is monomorphic by Stacks 0EMW, so the
morphism from the spectrum of the residue field at that point to the target is a monomorphism,
which is the criterion of Stacks 0EMX. -/
theorem bijective_residueFieldHom_of_mono (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (x : points B S hS X) :
    Function.Bijective (residueFieldHom B S hS X Y hY hXdec hYdec f x) := by
  have hmono : Mono (residueFieldMorphism B S hS X hXdec x ≫ f) := by
    have := (residueFieldRepresentative B S hS X hXdec x).2.2
    exact mono_comp _ _
  have : IsIso (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) :=
    (isIso_residueFieldHom_iff_mono B S hS X Y hY hXdec hYdec f x).mpr hmono
  simpa using ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x))

/-! ### The extension of function fields along a monomorphism -/

/-- The extension of function fields induced by a monomorphism of integral algebraic spaces
over `S` carrying the generic point to the generic point is bijective: it is the homomorphism of
residue fields at the generic point, which is bijective by Stacks 0EMX, composed with three
isomorphisms — the identifications of Stacks 0END of the two rings of rational functions with
the residue fields at the generic points, and the transport of the residue field along the
equality of points. -/
theorem bijective_rationalFunctionMap_of_mono (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY) :
    Function.Bijective (rationalFunctionMap B S hS hX hY hintX hintY f hgen) := by
  have hcomp : (rationalFunctionMap B S hS hX hY hintX hintY f hgen :
        rationalFunctions B S hS hY → rationalFunctions B S hS hX) =
      (rationalFunctionsRingEquiv B S hS hX hintX).symm ∘
        (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 f
          (genericPoint B S hS hX hintX)) ∘
        (residueFieldCongr B S hS hintY.2.1 hgen).symm ∘
        (rationalFunctionsRingEquiv B S hS hY hintY) := rfl
  rw [hcomp]
  exact (rationalFunctionsRingEquiv B S hS hX hintX).symm.bijective.comp
    (((bijective_residueFieldHom_of_mono B S hS hY hintX.2.1 hintY.2.1 f
        (genericPoint B S hS hX hintX)).comp
      (residueFieldCongr B S hS hintY.2.1 hgen).symm.bijective).comp
      (rationalFunctionsRingEquiv B S hS hY hintY).bijective)

/-- **The transport of the ring of rational functions along a monomorphism.** For a
monomorphism `f : X ⟶ Y` of integral algebraic spaces over `S` carrying the generic point of `X`
to the generic point of `Y`, the extension of function fields of Stacks 0EMP is an isomorphism
of rings `R(Y) ≃+* R(X)`. -/
def rationalFunctionsRingEquivOfMono (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY) :
    rationalFunctions B S hS hY ≃+* rationalFunctions B S hS hX :=
  RingEquiv.ofBijective (rationalFunctionMap B S hS hX hY hintX hintY f hgen)
    (bijective_rationalFunctionMap_of_mono B S hS hX hY hintX hintY f hgen)

/-- The transport of the ring of rational functions along a monomorphism *is* the extension of
function fields: it is that homomorphism, together with the proof that it is bijective. -/
@[simp]
theorem rationalFunctionsRingEquivOfMono_apply (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY) (g : rationalFunctions B S hS hY) :
    rationalFunctionsRingEquivOfMono B S hS hX hY hintX hintY f hgen g =
      rationalFunctionMap B S hS hX hY hintX hintY f hgen g :=
  rfl

/-! ### Isomorphisms -/

/-- An isomorphism of algebraic spaces over `S` is dominant: it is surjective on points.

Surjectivity itself is the base's `AlgebraicGeometry.Space.surjective_pointsMap_of_isIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr`, which is stated for an explicit
isomorphism; this reads it at `asIso f` for a morphism carrying `[IsIso f]`. -/
theorem isDominant_of_isIso (f : X ⟶ Y) [IsIso f] : IsDominant B S hS f :=
  (surjective_pointsMap_of_isIso B S hS (asIso f)).denseRange

/-- **The transport of the ring of rational functions along an isomorphism.** An isomorphism
`e : X ≅ Y` of integral algebraic spaces over `S` induces an isomorphism `R(Y) ≃+* R(X)` of the
rings of rational functions of Stacks 0EMP, namely the extension of function fields it induces,
which is defined because an isomorphism carries the generic point to the generic point.

This is the space-level counterpart of `Stacks.Chow.rationalFunctionsRingEquivOfIso`. -/
def rationalFunctionsRingEquivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (e : X ≅ Y) :
    rationalFunctions B S hS hY ≃+* rationalFunctions B S hS hX :=
  rationalFunctionsRingEquivOfMono B S hS hX hY hintX hintY e.hom
    (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY e.hom)

/-- The transport of the ring of rational functions along an isomorphism is the extension of
function fields along it. -/
@[simp]
theorem rationalFunctionsRingEquivOfIso_apply (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (e : X ≅ Y) (g : rationalFunctions B S hS hY) :
    rationalFunctionsRingEquivOfIso B S hS hX hY hintX hintY e g =
      rationalFunctionMap B S hS hX hY hintX hintY e.hom
        (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY e.hom) g :=
  rfl

/-! ### The naturality of the embedding of Stacks 0ENK along an isomorphism -/

/-- **Naturality of the embedding of Stacks 0ENK along an isomorphism.** Let `e : X ⟶ Y` be an
isomorphism of decent, locally Noetherian, integral algebraic spaces over `S`, let `Z ⊆ X` and
`Z' ⊆ Y` be prime divisors and suppose the generic point of `Z` lies over the generic point of
`Z'`. There is a flat local homomorphism of the henselian local rings there for which the
naturality square of Stacks 0ENK commutes, the extension of function fields in it being the
isomorphism `R(Y) ≃+* R(X)` of
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfMono`.

This is `AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality`, whose two
hypotheses an isomorphism satisfies: it is flat by
`AlgebraicGeometry.Space.isFlat_of_isIso`, and it carries the generic point to the generic
point. Note that the homomorphism of henselian local rings stays existentially quantified and is
*not* asserted to be an isomorphism. -/
theorem exists_genericHenselianLocalRingHom_naturality_of_isIso
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (e : X ⟶ Y)
    [IsIso e] (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (ZX : PrimeDivisor B S hS X) (ZY : PrimeDivisor B S hS Y)
    (hZ : pointsMap B S hS X e (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    ∃ (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) (_ : IsLocalHom φ) (hφflat : φ.Flat),
      ∀ g : rationalFunctions B S hS hY,
        ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX
            (rationalFunctionsRingEquivOfMono B S hS hX hY hintX hintY e
              (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY e) g) =
          IsLocalization.map (T := (↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰)
            (ZX.genericTotalFractionRing B S hS hX hdecX) φ
            (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφflat hc)
            (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g) :=
  exists_genericHenselianLocalRingHom_naturality B S hS hX hY hintX hintY e
    (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY e) hdecX hdecY hNX hNY ZX ZY
    (isFlat_of_isIso e hY) hZ

end AlgebraicGeometry.Space

end
