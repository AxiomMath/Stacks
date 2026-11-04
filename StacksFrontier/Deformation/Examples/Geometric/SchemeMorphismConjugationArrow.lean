module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalConjugationArrow
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismDerivationsHom

/-!
# The arrow `Inf(Def_X × Def_Y) ⟶ Der_k(𝒪_Y, f_*𝒪_X)` of the deformation sequence

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, with `Y` carrying the structure
morphism `pY`. The third arrow of the exact sequence of [Stacks Project, Tag 0E3V] is

`b : Inf(Def_X × Def_Y) ⟶ Der_k(𝒪_Y, f_*𝒪_X)`.

Conceptually: a pair of infinitesimal automorphisms of a first-order deformation of `X` and of
one of `Y` differs from compatibility with `f` by a derivation, and `b` is that difference. In
the source's notation, the pair `(α, β)` carries a lift `f' : X' ⟶ Y'` of `f` to `β ∘ f' ∘ α`,
and `b(α, β)` is the derivation that carries `f'` to the same place.

This file is the deformation-theoretic reading of
`Stacks.Thickenings.conjugationDerivation`, which does the geometry at the level of first-order
thickenings. All this adds is the target: the thickening-level arrow lands in
`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})`, and the third term of the source's sequence is
`Der_k(𝒪_Y, f_*𝒪_X)`. The two are the same group once the conormal sheaf of the thickening is
trivialised, by `Deformation.Examples.schemeMorphismDerivationsEquivHom`, and the arrow is
transported along that identification.

## Main definitions

* `Deformation.Examples.schemeMorphismConjugationArrow`: **Stacks 0E3V, the arrow `b`**, as a map
  from the pairs of infinitesimal automorphisms of the two endpoint deformations into the third
  term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's sequence.

## Main results

* `Deformation.Examples.schemeMorphismConjugationArrow_spec`: **the characterising property of
  `b`** — translating the lift `f'` by `b(α, β)` carries it where conjugating it by `(α, β)`
  carries it. This is the hypothesis `hb` of `Deformation.exact_triple_of_simplyTransitive`,
  `Deformation.map_add_of_simplyTransitive` and
  `Deformation.map_smul_of_simplyTransitive`.
* `Deformation.Examples.eq_schemeMorphismConjugationArrow`: no other derivation has that
  property.
* `Deformation.Examples.schemeMorphismConjugationArrow_add` and
  `Deformation.Examples.schemeMorphismConjugationArrow_zero`: `b` is additive and kills the
  trivial pair.

## Implementation notes

**The source of `b` is the pairs of derivations presenting the infinitesimal automorphisms, not
the `Inf` term itself.** The `Inf` term of the source's sequence is
`Deformation.localizedAutomorphismFunctorTangent`, the tangent space at the identity of an
automorphism functor; `Deformation.Examples.localizedTangentEquivSelfMaps` identifies it with
the invertible self-maps of the total space of the chosen first-order deformation over the base
fixing the special-fibre immersion, and
`Stacks.Thickenings.derivationActionGlobalEquivOfBase` in its self-map case identifies those
with the derivations `u : Ω_{X/Z'}|_X ⟶ 𝒞_{X/X'}`. Both identifications are honest bijections,
so no generality is lost by taking the derivations as the source.

Taking them is the only honest option available. The derivation *action* on the `Inf` term
exists in the library only inside an existential —
`Deformation.Examples.exists_simplyTransitive_addAction_localizedTangent` and
`Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps` produce a function
with the torsor axioms rather than naming one — so an arrow stated on the `Inf` term could not
refer to "the" action at all, and would have to quantify over every action satisfying those
axioms. Quantifying would make the arrow depend on an arbitrary choice, and its additivity would
then be a statement about that choice rather than about the geometry. Stating `b` on the
derivations avoids the question: the group law on the source is the addition of a group of
morphisms of sheaves of modules, which `Stacks.Thickenings.conjugationDerivation_add` uses
directly, and the bridge to the `Inf` term is a separate bijection that can be composed in
later without touching the arrow.

**The other place the arrow could have been built, and why it is not built there.** The library
carries a second presentation of the same data one level up, at the deformation categories
rather than at the thickenings: the lifts are
`Deformation.Examples.globalLiftsOverBase`, the conjugation is
`Deformation.Examples.globalLiftsOverBaseConj` with its action laws
`Deformation.Examples.globalLiftsOverBaseConj_id` and
`Deformation.Examples.globalLiftsOverBaseConj_comp`, and the other three inputs of
`Deformation.exact_triple_of_simplyTransitiveVAdd` are
`Deformation.Examples.exists_liftDeformationFiberAut_eq_iff` (`ha`),
`Deformation.Examples.liftClass_eq_liftClass_iff` (`hcls`) and
`Deformation.Examples.exists_liftClass_iff` (`hc`). The one input that
strand does **not** have is `b` itself, and the obstruction is precisely the existential: the
translation action there is
`Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase`, which produces a
function with the torsor axioms rather than naming one, so "the derivation carrying `ℓ₀` where
`(α, β)` carries it" is not a term. The thickening level has
`Stacks.Thickenings.derivationActionGlobalEquivOfBase`, an honest bijection, and that is why the
arrow is built there and read up.

Bridging the two is therefore a matter of a *named* action on
`Deformation.Examples.globalLiftsOverBase` agreeing with that bijection, plus a reconciliation of
the two conjugation conventions: `Deformation.Examples.globalLiftsOverBaseConj` forms
`inv α ≫ ℓ ≫ β`, while `Stacks.Thickenings.conjugateBaseLift` forms
`(u ⬝ 𝟙) ≫ a' ≫ (v ⬝ 𝟙)` with the source factor not inverted, so the two parametrisations of the
source side differ by a sign. `Stacks.Thickenings.derivationActionGlobal_zero` supplies what that
reconciliation needs — that the self-map of the zero derivation is the identity — and neither the
named action nor the reconciliation is done here.

`b` is a bare function rather than a bundled additive or linear map, because that is the shape
the torsor lemmas of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismSixTerm.lean` consume: they take `b`
as `G → D` with its characterising property `hb` and derive additivity and homogeneity from the
two actions. Additivity is recorded here anyway, since
`Stacks.Thickenings.conjugationDerivation_add` proves it without any hypothesis about the two
actions.

The identification of the target is the additive
`Deformation.Examples.schemeMorphismDerivationsEquivHom` rather than the `k`-linear
`Deformation.Examples.schemeMorphismDerivationsLinearEquivHom`. The two have the same underlying
bijection; the additive one is used because its statement carries no `letI` of a `k`-module
structure, so a caller needs none either. Homogeneity of `b` is a separate matter: it is
`Deformation.map_smul_of_simplyTransitive`, whose hypothesis `hscale` compares the scalar action
on the conjugating side — which rescales the infinitesimal coordinate of the base — with the
translation action, and is not formal from additivity. It is proved, at the chosen re-based
first-order pushforwards, in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismConjugationArrowLinear.lean`, where the
arrow is packaged as the `k`-linear map
`Deformation.Examples.schemeMorphismConjugationArrowLinear`.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}}

section Arrow

variable (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) {X' Y' Z' : Scheme.{u}}
  {i : X ⟶ X'} {j : Y ⟶ Y'} {kk : baseSpec (residueFieldBase Λ k) ⟶ Z'}
  [IsClosedImmersion i] [IsClosedImmersion j] [IsImmersion kk]
  {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'}
  (e : Stacks.Thickenings.conormalModules i ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  (hsq : i.ker ^ 2 = ⊥) (hsqj : j.ker ^ 2 = ⊥) (sq : IsPullback j pY h' kk)
  (ci : i ≫ g' = (f ≫ pY) ≫ kk) (f' : X' ⟶ Y') (comm_f : i ≫ f' = f ≫ j) (hf : f' ≫ h' = g')
  (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
  (comm_j : j ≫ (𝟙 Y' : Y' ⟶ Y') = (𝟙 Y : Y ⟶ Y) ≫ j)

/-- The pairs of derivations presenting the infinitesimal automorphisms of the two endpoint
deformations: a self-map of `X'` over the thickened base fixing `X` is `u ⬝ 𝟙_{X'}` for a unique
`u : Ω_{X/Z'}|_X ⟶ 𝒞_{X/X'}`, and likewise on the target. This is the source of the arrow `b` of
[Stacks Project, Tag 0E3V]. -/
abbrev SchemeMorphismSelfMapPair : Type u :=
  (Stacks.Smooth.pullbackCotangentSheaf (i ≫ g') (𝟙 X) ⟶ Stacks.Thickenings.conormalModules i) ×
    (Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') (𝟙 Y) ⟶
      Stacks.Thickenings.conormalModules j)

/-- **Stacks 0E3V, the arrow `b : Inf(Def_X × Def_Y) ⟶ Der_k(𝒪_Y, f_*𝒪_X)`.** Let `i : X ⟶ X'`
and `j : Y ⟶ Y'` be first-order deformations of the two endpoints of `f : X ⟶ Y` over a
square-zero thickening `kk` of the residue field, with `j` cartesian over `kk` and the conormal
sheaf of `i` trivialised, and let `f' : X' ⟶ Y'` be a lift of `f`. A pair of infinitesimal
automorphisms of `X'` and of `Y'` carries `f'` to another lift of `f`, and the derivations act
simply transitively on the lifts by [Stacks Project, Tag 0CK2], so exactly one derivation carries
`f'` there. This is that derivation, read in the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's
sequence.

The geometry is `Stacks.Thickenings.conjugationDerivation`; the target is moved onto the third
term by `Deformation.Examples.schemeMorphismDerivationsEquivHom`. -/
def schemeMorphismConjugationArrow :
    SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g') →
      schemeMorphismDerivations f pY :=
  fun uv => (schemeMorphismDerivationsEquivHom f pY i e).symm
    (Stacks.Thickenings.conjugationDerivation hsq hsqj sq ci f' comm_f hf uv.1 uv.2
      comm_i comm_j)

/-- **The characterising property of the arrow `b`**: translating the lift `f'` by `b(u, v)`
carries it exactly where conjugating it by the pair `(u, v)` carries it,
`(b(u, v)) ⬝ f' = (u ⬝ 𝟙_{X'}) ≫ f' ≫ (v ⬝ 𝟙_{Y'})`.

Read through the torsor bijection of [Stacks Project, Tag 0CK2] this is the hypothesis `hb` of
`Deformation.exact_triple_of_simplyTransitive`,
`Deformation.map_add_of_simplyTransitive` and `Deformation.map_smul_of_simplyTransitive`. -/
theorem schemeMorphismConjugationArrow_spec
    (uv : SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g')) :
    (Stacks.Thickenings.derivationActionGlobalEquivOfBase hsq sq ci comm_f hf
        (schemeMorphismDerivationsEquivHom f pY i e
          (schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j
            uv))).1 =
      Stacks.Thickenings.conjugateBaseLift hsq hsqj f' uv.1 uv.2 comm_i comm_j := by
  rw [schemeMorphismConjugationArrow, AddEquiv.apply_symm_apply,
    Stacks.Thickenings.derivationActionGlobalEquivOfBase_conjugationDerivation]

/-- **No other element of the third term displaces the lift the way conjugation does.** Simple
transitivity of the action of [Stacks Project, Tag 0CK2] pins `b(u, v)`. -/
theorem eq_schemeMorphismConjugationArrow
    (uv : SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g'))
    (D : schemeMorphismDerivations f pY)
    (hD : (Stacks.Thickenings.derivationActionGlobalEquivOfBase hsq sq ci comm_f hf
        (schemeMorphismDerivationsEquivHom f pY i e D)).1 =
      Stacks.Thickenings.conjugateBaseLift hsq hsqj f' uv.1 uv.2 comm_i comm_j) :
    D = schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j uv := by
  rw [schemeMorphismConjugationArrow, ← AddEquiv.symm_apply_apply
    (schemeMorphismDerivationsEquivHom f pY i e) D]
  exact congrArg (schemeMorphismDerivationsEquivHom f pY i e).symm
    (Stacks.Thickenings.eq_conjugationDerivation hsq hsqj sq ci f' comm_f hf uv.1 uv.2
      comm_i comm_j _ hD)

/-- **Stacks 0E3V, the arrow `b` is additive.** The two perturbations of the lift — conjugating
it and translating it — are independent, so the derivation displacing it adds with the
conjugating pair. The content is
`Stacks.Thickenings.conjugationDerivation_add`; the identification of the target is additive. -/
theorem schemeMorphismConjugationArrow_add
    (uv uv₂ : SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g')) :
    schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j
        (uv + uv₂) =
      schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j uv +
        schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j uv₂ := by
  rw [schemeMorphismConjugationArrow, schemeMorphismConjugationArrow,
    schemeMorphismConjugationArrow, ← map_add]
  exact congrArg (schemeMorphismDerivationsEquivHom f pY i e).symm
    (Stacks.Thickenings.conjugationDerivation_add hsq hsqj sq ci f' comm_f hf uv.1 uv.2
      comm_i comm_j uv₂.1 uv₂.2)

/-- **The arrow `b` kills the trivial pair.** The identity pair of infinitesimal automorphisms
does not displace the lift. -/
theorem schemeMorphismConjugationArrow_zero :
    schemeMorphismConjugationArrow f pY e hsq hsqj sq ci f' comm_f hf comm_i comm_j 0 = 0 := by
  rw [schemeMorphismConjugationArrow,
    show (0 : SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g')).1 = 0 from rfl,
    show (0 : SchemeMorphismSelfMapPair (i := i) (j := j) (h' := h') (g' := g')).2 = 0 from rfl,
    Stacks.Thickenings.conjugationDerivation_zero hsq hsqj sq ci f' comm_f hf comm_i comm_j,
    map_zero]

end Arrow

end Deformation.Examples

end
