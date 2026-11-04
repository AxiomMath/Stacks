module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcompProduct

/-!
# The product comparison as an isomorphism of functors, and the sections it identifies

Let `τ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  `AlgebraicGeometry.Space.isLimitBinaryFanPostcompBaseChange` says that for every
object `V` of the spaces-étale site of `X` the postcomposition along `τ` of the base change of
`V` along `τ` is the binary product `U ⨯ V` of that site.  This file packages that comparison
as an isomorphism of functors and draws the consequence the proof of Stacks 03M8 uses.

For a second morphism `f : X ⟶ Y` and `a = τ ≫ f` it gives the identification

`(V ×_Y U) read over X   ≅   U ⨯ (V ×_Y X)`,

natural in the object `V` of the spaces-étale site of `Y` — the base change along `a` split by
`AlgebraicGeometry.Space.spacesBaseChange_comp` into the base change along `f` followed by the
base change along `τ`, and the latter turned into the product by the comparison.  This is the
geometric identification that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean` record as the one thing
missing for reading the middle and right terms of the sequence of Stacks 03M8 as the sections of
`a_*(F|_U)` and `b_*(F|_R)`: on sections it says that the sections over `V` of the extension
of `F|_U` pushed forward along `a` are the sections of `F` over the product `U ⨯ (V ×_Y X)`,
which is the middle term of
`AlgebraicGeometry.Space.isLimitForkDirectImage`.

## Main definitions

* `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp` is the comparison isomorphism at one
  object, and `AlgebraicGeometry.Space.postcompBaseChangeProdIso` is the isomorphism of
  functors `(V ↦ V ×_X U read over X) ≅ (V ↦ U ⨯ V)`.
* `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` is the same for a composite
  `a = τ ≫ f`, as an isomorphism of functors from the spaces-étale site of `Y`.
* `AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso` is the induced isomorphism of
  presheaves of sections, with arbitrary coefficients.

## Main results

* `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_fst` and
  `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_snd`: the comparison is compatible
  with the two projections, which is what pins it down.
* `AlgebraicGeometry.Space.postcompBaseChangeChartIso`: the identification at an étale scheme
  chart `V` of `Y`, where its target is `U ⨯ (V ×_Y X)` with `V ×_Y X` the base-changed chart
  `AlgebraicGeometry.Space.chartBaseChange`.

## Implementation notes

The isomorphism of functors is built from the pointwise comparison by
`CategoryTheory.NatIso.ofComponents`, its naturality being checked on the two projections of
the target product: `AlgebraicGeometry.Space.postcompBaseChange_map_fst` and
`AlgebraicGeometry.Space.postcompBaseChange_map_snd` are exactly the two naturality statements
for the source, and `CategoryTheory.Limits.prod.hom_ext` reduces the naturality square to
them.

The target of the comparison is the *chosen* product `CategoryTheory.Limits.prod.functor`, so
this file needs `AlgebraicGeometry.Space.SpacesEtale.instHasBinaryProducts`, which is why it
sits downstream of `PushforwardPresentationExact`; the comparison itself needs no product API
and is proved there without it.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (bc : SpacesBaseChange B S hS τ)

/-! ### The comparison as an isomorphism of functors -/

/-- The product comparison of `AlgebraicGeometry.Space.isLimitBinaryFanPostcompBaseChange` as
an isomorphism: the postcomposition along `τ` of the base change of `V` along `τ` is the
chosen binary product `U ⨯ V` of the spaces-étale site of `X`. -/
noncomputable def postcompBaseChangeProdIsoApp (V : SpacesEtale B S hS X) :
    (spacesEtalePostcomp B S hS τ hτ).obj (bc.functor.obj V) ≅
      etaleOverObj B S hS τ hτ ⨯ V :=
  IsLimit.conePointUniqueUpToIso (isLimitBinaryFanPostcompBaseChange B S hS τ hτ bc V)
    (limit.isLimit (pair (etaleOverObj B S hS τ hτ) V))

/-- The comparison isomorphism `postcompBaseChangeProdIsoApp` followed by the first product
projection is the projection `postcompBaseChangeFst` of the postcomposed base change to `U`. -/
@[reassoc (attr := simp)]
theorem postcompBaseChangeProdIsoApp_hom_fst (V : SpacesEtale B S hS X) :
    (postcompBaseChangeProdIsoApp B S hS τ hτ bc V).hom ≫ prod.fst =
      postcompBaseChangeFst B S hS τ hτ bc V :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitBinaryFanPostcompBaseChange B S hS τ hτ bc V)
    (limit.isLimit (pair (etaleOverObj B S hS τ hτ) V)) ⟨WalkingPair.left⟩

/-- The comparison isomorphism `postcompBaseChangeProdIsoApp` followed by the second product
projection is the projection `postcompBaseChangeSnd` of the postcomposed base change to `V`. -/
@[reassoc (attr := simp)]
theorem postcompBaseChangeProdIsoApp_hom_snd (V : SpacesEtale B S hS X) :
    (postcompBaseChangeProdIsoApp B S hS τ hτ bc V).hom ≫ prod.snd =
      postcompBaseChangeSnd B S hS τ hτ bc V :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitBinaryFanPostcompBaseChange B S hS τ hτ bc V)
    (limit.isLimit (pair (etaleOverObj B S hS τ hτ) V)) ⟨WalkingPair.right⟩

/-- **The product comparison of the proof of Stacks 03M8, as an isomorphism of functors.**
Base change along the étale morphism `τ : U ⟶ X` followed by postcomposition with `τ` is the
binary-product functor `V ↦ U ⨯ V` of the spaces-étale site of `X`.

The isomorphism is compatible with the two projections, by
`AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_fst` and
`AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_snd`, which pins it down. -/
noncomputable def postcompBaseChangeProdIso :
    bc.functor ⋙ spacesEtalePostcomp B S hS τ hτ ≅
      prod.functor.obj (etaleOverObj B S hS τ hτ) :=
  NatIso.ofComponents (postcompBaseChangeProdIsoApp B S hS τ hτ bc) (fun {V V'} k ↦ by
    change (spacesEtalePostcomp B S hS τ hτ).map (bc.functor.map k) ≫
          (postcompBaseChangeProdIsoApp B S hS τ hτ bc V').hom =
        (postcompBaseChangeProdIsoApp B S hS τ hτ bc V).hom ≫
          prod.map (𝟙 (etaleOverObj B S hS τ hτ)) k
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, postcompBaseChangeProdIsoApp_hom_fst,
        postcompBaseChange_map_fst, prod.map_fst, Category.comp_id,
        postcompBaseChangeProdIsoApp_hom_fst]
    · rw [Category.assoc, Category.assoc, postcompBaseChangeProdIsoApp_hom_snd,
        postcompBaseChange_map_snd, prod.map_snd, ← Category.assoc,
        postcompBaseChangeProdIsoApp_hom_snd])

/-- **The comparison is compatible with a change of the étale morphism.**  If `θ : R ⟶ U`
satisfies `θ ≫ τ = ρ` then the morphism
`AlgebraicGeometry.Space.postcompBaseChangeOverMap` induced by `θ` on the postcomposed base
changes is, under the comparison, the morphism `prod.map θ (𝟙 V)` of the products.

In the proof of Stacks 03M8 this is the statement that the two parallel arrows
`V ×_Y U ⇉ V ×_Y R` of the asserted sequence, induced by the two projections `t, s` of the
relation of an étale chart, are the two arrows `prod.map t (𝟙)` and `prod.map s (𝟙)` of the
sequence of `AlgebraicGeometry.Space.isLimitForkDirectImage`. -/
theorem postcompBaseChangeOverMap_prodIsoApp {R : AlgebraicSpaces B S hS} {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (θ : R ⟶ U) (hθ : θ ≫ τ = ρ)
    (bcρ : SpacesBaseChange B S hS ρ) (V : SpacesEtale B S hS X) :
    postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bc V ≫
        (postcompBaseChangeProdIsoApp B S hS τ hτ bc V).hom =
      (postcompBaseChangeProdIsoApp B S hS ρ hρ bcρ V).hom ≫
        prod.map (etaleOverMap B S hS τ hτ hρ θ hθ) (𝟙 V) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, postcompBaseChangeProdIsoApp_hom_fst,
      postcompBaseChangeOverMap_fst, prod.map_fst, ← Category.assoc,
      postcompBaseChangeProdIsoApp_hom_fst]
  · rw [Category.assoc, Category.assoc, postcompBaseChangeProdIsoApp_hom_snd,
      postcompBaseChangeOverMap_snd, prod.map_snd, Category.comp_id,
      postcompBaseChangeProdIsoApp_hom_snd]

/-! ### The identification of the sections of Stacks 03M8 -/

variable (f : X ⟶ Y)

/-- **The geometric identification the proof of Stacks 03M8 needs.**  Let `τ : U ⟶ X` be étale,
let `f : X ⟶ Y` be arbitrary and put `a = τ ≫ f`.  Then the base change along `a` of an object
`V` of the spaces-étale site of `Y`, read back over `X` by postcomposition with `τ`, is the
binary product of `U` with the base change of `V` along `f`:

`(V ×_Y U) read over X   ≅   U ⨯ (V ×_Y X)`,

naturally in `V`.

The base change along `a` is split into the base change along `f` followed by the base change
along `τ` by `AlgebraicGeometry.Space.spacesBaseChange_comp`, and the latter is turned into
the product by `AlgebraicGeometry.Space.postcompBaseChangeProdIso`. -/
noncomputable def postcompBaseChangeCompProdIso :
    (spacesBaseChange B S hS (τ ≫ f)).functor ⋙ spacesEtalePostcomp B S hS τ hτ ≅
      (spacesBaseChange B S hS f).functor ⋙ prod.functor.obj (etaleOverObj B S hS τ hτ) :=
  Functor.isoWhiskerRight (spacesBaseChange_comp B S hS τ f).symm
      (spacesEtalePostcomp B S hS τ hτ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (spacesBaseChange B S hS f).functor
      (postcompBaseChangeProdIso B S hS τ hτ (spacesBaseChange B S hS τ))

/-- The identification of `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` at an étale
scheme chart `V` of `Y`: the chart `V ×_Y U`, read over `X`, is the product of `U` with the
base-changed chart `V ×_Y X` of `AlgebraicGeometry.Space.chartBaseChange`.

This is the identification the proof of Stacks 03M8 performs when it reads the middle term of
its exact sequence, the sections of `a_*(F|_U)` over `V`, as the sections of `F` over
`V ×_Y U`. -/
noncomputable def postcompBaseChangeChartIso (V : SmallEtale B S hS Y.1) :
    (spacesEtalePostcomp B S hS τ hτ).obj
        ((spacesBaseChange B S hS (τ ≫ f)).functor.obj
          ((comparisonFunctor B S hS Y).obj V)) ≅
      etaleOverObj B S hS τ hτ ⨯ chartBaseChange B S hS f V :=
  (postcompBaseChangeCompProdIso B S hS τ hτ f).app ((comparisonFunctor B S hS Y).obj V)

variable {A : Type w} [Category.{w'} A]

/-- **The identification on sections.**  For a presheaf `P` on the spaces-étale site of `X`
with arbitrary coefficients, the presheaf on the spaces-étale site of `Y` of sections of `P`
over the base change along `a = τ ≫ f` read over `X` — which for a sheaf is the presheaf
underlying `a_*(P|_U)`, the restriction along `τ` being restriction along
`AlgebraicGeometry.Space.spacesEtalePostcomp` — is the presheaf of sections of `P` over the
product `U ⨯ (V ×_Y X)`, which is the middle term of
`AlgebraicGeometry.Space.isLimitForkDirectImage`.

This is `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` restricted into `P`. -/
noncomputable def postcompBaseChangeCompSectionsIso (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A) :
    ((spacesBaseChange B S hS (τ ≫ f)).functor ⋙
        spacesEtalePostcomp B S hS τ hτ).op ⋙ P ≅
      ((spacesBaseChange B S hS f).functor ⋙
        prod.functor.obj (etaleOverObj B S hS τ hτ)).op ⋙ P :=
  Functor.isoWhiskerRight
    (NatIso.op (postcompBaseChangeCompProdIso B S hS τ hτ f)).symm P

end AlgebraicGeometry.Space

end
