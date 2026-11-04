module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap

/-!
# The canonical map `Lh^* R𝓗om(K, L) ⟶ R𝓗om(Lh^*K, Lh^*L)` when the target internal hom raises
the module universe

Tag 08I3 — and its ringed-site twin Tag 08JF — constructs a canonical map

`Lh^* R𝓗om_{𝒪_Y}(K, L) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*L)`

for a morphism `h` whose two sides have internal homs in *one* category.
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` is the construction over
abstract data, and the abstraction it carries is exactly that: its two internal homs
`H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁` and `H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂` are endo-bifunctors.

That shape is the obstruction to Stacks 08JP. There `h` is the morphism of ringed sites `ε` of
Stacks 08H7 from the small étale site of a scheme `S` to its Zariski site, a
`RingedSite.{u + 1, u, u} ⟶ RingedSite.{u, u, u}`; the objects of the small étale site form a type
in `Type (u + 1)`, so the internal Hom complex of Stacks 0A8X raises the module universe there
and the target internal hom is a bifunctor

`D(Mod_u(𝒪))ᵒᵖ ⥤ D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))`

(`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor`), landing one universe above its
arguments. The source internal hom, on the Zariski site, stays where it is. So the canonical map
cannot even be typed: its source and target are objects of different categories.

This file is the generalisation that can be typed. It keeps a target internal hom
`H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂'` landing in a second category `D₂'`, adds the functor `Λ : D₂ ⥤ D₂'` that
moves the source of the map there — on the small étale site that is
`AlgebraicGeometry.SmallEtale.derivedModuleULift`, the derived functor of the universe lift of
module sheaves — and asks for the tensor–hom bijection of the target in the resulting mixed form

`(A ⟶ H₂(B, C)) ≃ (T₂(A, B) ⟶ Λ C)` with `A : D₂'` and `B, C : D₂`,

together with the monoidality comparison in the matching mixed form. The construction is then
word for word the one of `Transpose`, and
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison_id_eq` says that at
`D₂' = D₂` and `Λ = 𝟭` it *is* `Transpose.homComparison`, on the nose.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparisonDatum`: the transpose
  datum `T₂(Λ P hom(A, B), P A) ⟶ Λ P B`, the mixed monoidality comparison followed by `Λ P` of
  the evaluation.
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison`: **the comparison
  `Λ P hom(A, B) ⟶ hom(P A, P B)`**, the transpose of that datum under the mixed tensor–hom
  bijection of the target.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison_adjoint`: the
  transpose of the comparison is the transpose datum, the recipe Tag 08I3 gives, in the mixed
  form.
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparisonDatum_id_eq` and
  `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison_id_eq`: **at
  `Λ = 𝟭` the mixed datum and the mixed comparison are
  `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparisonDatum` and
  `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`**.

## What this does not give

It does not give Stacks 08JP, and the gap is in the *data*, not in the construction. Instantiating
`homComparison` at `ε` and at the derived internal homs of the two ringed sites requires three
things this development does not have, each a mixed-universe form of an equal-universe statement:

* a derived tensor product `T₂ : D(Mod_{u+1}(𝒪)) × D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))` on the small
  étale ringed site, of an object with raised sections against one without. Every derived tensor
  product of Stacks 06YU in the repository is an endo-bifunctor of one `D(Mod_v(𝒪))`, and the
  K-flat resolutions of Stacks 06YS behind them are stated at a `RingedSite.{u, u, u}`;
* the tensor–internal-Hom bijection of Stacks 08J8/08DI in the mixed form `e₂` above, whose
  target `Λ C` is where the asymmetry of the universes shows up;
* the monoidality of `ε^*` against that mixed tensor product, the mixed form of Stacks 07A4/079U.

The two sides of 08JP are objects of one category,
`AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom` and
`AlgebraicGeometry.SmallEtale.derivedSheafHom`, and
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleDerivedSheafHomComparison` is `homComparison`
between them with the three data above carried as hypotheses.

## Implementation notes

`m` is a natural isomorphism of functors, as it is in `Transpose`, although only one of its
components is used.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose

variable {D₁ D₂ D₂' : Type*} [Category D₁] [Category D₂] [Category D₂']
  (P : D₁ ⥤ D₂) (Λ : D₂ ⥤ D₂')
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂')
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂' × D₂ ⥤ D₂')
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ (A : D₂') (B C : D₂), (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ Λ.obj C))
  (m : T₁ ⋙ P ⋙ Λ ≅ (P ⋙ Λ).prod P ⋙ T₂)

/-- The transpose datum `T₂(Λ P hom(A, B), P A) ⟶ Λ P B` of the comparison of a functor with
internal hom, when the internal hom of the target lands one category further on and the source of
the comparison is moved there by `Λ`: the mixed monoidality comparison followed by `Λ P` of the
evaluation `hom(A, B) ⊗ A ⟶ B`.

At `Λ = 𝟭` this is
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparisonDatum`
(`homComparisonDatum_id_eq`). -/
def homComparisonDatum (A B : D₁) :
    T₂.obj (Λ.obj (P.obj ((H₁.obj (op A)).obj B)), P.obj A) ⟶ Λ.obj (P.obj B) :=
  m.inv.app ((H₁.obj (op A)).obj B, A) ≫ Λ.map (P.map (Transpose.evaluation H₁ T₁ e₁ A B))

/-- **The comparison `Λ P hom(A, B) ⟶ hom(P A, P B)`** of a functor with internal hom, when the
internal hom of the target raises the ambient category and the source of the comparison is moved
there by `Λ`: the transpose, under the mixed tensor–hom bijection of the target, of
`homComparisonDatum`.

At `Λ = 𝟭` it is `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`, the
canonical map of Stacks 08I3 (`homComparison_id_eq`). -/
def homComparison (A B : D₁) :
    Λ.obj (P.obj ((H₁.obj (op A)).obj B)) ⟶ (H₂.obj (op (P.obj A))).obj (P.obj B) :=
  (e₂ (Λ.obj (P.obj ((H₁.obj (op A)).obj B))) (P.obj A) (P.obj B)).symm
    (homComparisonDatum P Λ H₁ T₁ T₂ e₁ m A B)

/-- The transpose of the comparison is the transpose datum. -/
theorem homComparison_adjoint (A B : D₁) :
    e₂ (Λ.obj (P.obj ((H₁.obj (op A)).obj B))) (P.obj A) (P.obj B)
        (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m A B) =
      homComparisonDatum P Λ H₁ T₁ T₂ e₁ m A B :=
  (e₂ _ (P.obj A) (P.obj B)).apply_symm_apply _

/-! ### Agreement with the equal-universe construction -/

section Agreement

variable (H₂' : D₂ᵒᵖ ⥤ D₂ ⥤ D₂) (T₂' : D₂ × D₂ ⥤ D₂)
  (e₂' : ∀ A B C : D₂, (A ⟶ (H₂'.obj (op B)).obj C) ≃ (T₂'.obj (A, B) ⟶ C))
  (m' : T₁ ⋙ P ≅ P.prod P ⋙ T₂')

/-- **At `Λ = 𝟭` the mixed transpose datum is the transpose datum of
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose`.** -/
theorem homComparisonDatum_id_eq (A B : D₁) :
    homComparisonDatum P (𝟭 D₂) H₁ T₁ T₂' e₁ m' A B =
      Transpose.homComparisonDatum P H₁ T₁ T₂' e₁ m' A B := rfl

/-- **At `Λ = 𝟭` the mixed comparison is
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`**, the construction behind
the canonical map of Stacks 08I3. -/
theorem homComparison_id_eq (A B : D₁) :
    homComparison P (𝟭 D₂) H₁ H₂' T₁ T₂' e₁ e₂' m' A B =
      Transpose.homComparison P H₁ H₂' T₁ T₂' e₁ e₂' m' A B := rfl

end Agreement

end Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose

end
