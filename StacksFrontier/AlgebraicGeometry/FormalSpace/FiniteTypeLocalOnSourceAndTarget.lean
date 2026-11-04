module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget

/-!
# Being locally of finite type is local on the source and the target

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Stacks 0ANL compares the following ways of asking that `f`
be locally of finite type:

1. `f` is locally of finite type;
2. there is one commutative square with `U`, `V` formal algebraic spaces, vertical arrows
   representable by algebraic spaces and étale, `U ⟶ X` surjective, and `U ⟶ V` locally of
   finite type;
3. every commutative square with `U`, `V` formal algebraic spaces and vertical arrows
   representable by algebraic spaces and étale has `U ⟶ V` locally of finite type;
4. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uⱼᵢ ⟶ Vⱼ` locally of finite type;
5. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable by algebraic spaces
   and étale over `Y` with `Uᵢ ⟶ Vᵢ` locally of finite type.

This is the finite type counterpart of the comparison of Stacks 0AN4, which carries out the
same four-way comparison for the property of being representable by algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnSomeSquare`,
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnEverySquare`,
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeAfterTargetCover` and
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnFactoredAtlas`: conditions (2), (3),
  (4) and (5) of Stacks 0ANL.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType`:
  condition (1) implies condition (2).
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_of_onEverySquare`: condition (3)
  implies condition (1).
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnSomeSquare_of_onEverySquare`:
  condition (3) implies condition (2).
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare`:
  condition (3) implies condition (4).
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover`:
  condition (4) implies condition (5).

## Implementation notes

Being locally of finite type is `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType`, that is
Definition 0AM4, part (1): representability by algebraic spaces together with the Bootstrap
condition of Stacks 03XZ on every represented base change. It is therefore not a conjunction of
representability with a further condition but an existential over the representability witness,
which is what makes the base changes algebraic spaces. The vertical arrows of the squares in
conditions (2) and (3) are representable étale in the sense of
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale`, and surjectivity of `U ⟶ X` in condition
(2) is surjectivity of the morphism of sheaves, `CategoryTheory.Sheaf.IsLocallySurjective`,
which is how Definition 0AIM records surjectivity of an atlas.

The implication from condition (3) to condition (1) is sharper than the implication from
condition (3) to condition (2) recorded in the source, and it is free: instantiating condition
(3) at the square formed by the identities of `X` and of `Y` returns `f` itself. The implication
from condition (3) to condition (2) is then that implication followed by the implication from
condition (1) to condition (2).

The two implications of the source which are not proved here are the two whose Stacks proofs
need the relative diagonal of a morphism of formal algebraic spaces to be locally of finite
type, Stacks 0AN2: the implication from condition (1) to condition (3), and the implication
from condition (2) to condition (1). That assertion of Stacks 0AN2 is available for an
arbitrary formal algebraic space source, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable`; the two implications have
simply not been carried out here. Each tag attribute below names the implication it carries.

Two inputs of the source are explicit hypotheses because the library does not carry them. The
step from condition (3) to condition (4) needs the fibre products `Vⱼ ×_Y X` to be formal
algebraic spaces, which is Stacks 0AJ3; it is `h0AJ3`, exactly as in the corresponding step of
Stacks 0AN4 and of Stacks 0ANG. The step from condition (4) to condition (5) needs that the
composite of a covering as in Definition 0AIM of the target with coverings of the fibre products
of its members is again a covering of the source; it is `h0AIM`. Of the three clauses of that
conclusion only the joint surjectivity of the composite family is genuinely missing from the
library: affineness is inherited from the given coverings, and representable étaleness of a
composite `Uⱼᵢ ⟶ Vⱼ ×_Y X ⟶ X` follows from `IsRepresentableEtale.comp` together with
`isRepresentableEtale_pullback_snd`, the second projection being a base change of `Vⱼ ⟶ Y`.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ANL, condition (2).** There is a commutative square whose source column is a
surjective representable étale map from a formal algebraic space, whose target column is a
representable étale map from a formal algebraic space, and whose upper horizontal map is
locally of finite type. -/
abbrev IsLocallyOfFiniteTypeOnSomeSquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (U V : FppfSheaf B S hS) (p : U ⟶ X) (q : V ⟶ Y) (t : U ⟶ V),
    IsFormalAlgebraicSpace B S hS U ∧ IsFormalAlgebraicSpace B S hS V ∧
      IsRepresentableEtale B S hS p ∧ Sheaf.IsLocallySurjective p ∧
      IsRepresentableEtale B S hS q ∧ IsLocallyOfFiniteType B S hS t ∧ p ≫ f = t ≫ q

/-- **Stacks 0ANL, condition (3).** Every commutative square whose vertical maps are
representable étale and whose corners are formal algebraic spaces has its upper horizontal map
locally of finite type. -/
abbrev IsLocallyOfFiniteTypeOnEverySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS) (p : U ⟶ X) (q : V ⟶ Y) (t : U ⟶ V),
    IsFormalAlgebraicSpace B S hS U → IsFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS p → IsRepresentableEtale B S hS q →
    p ≫ f = t ≫ q → IsLocallyOfFiniteType B S hS t

/-- **Stacks 0ANL, condition (4).** There is an affine étale covering of the target and, for
each of its members, an affine étale covering of the fibre product of that member with the
source whose members are locally of finite type over that member. -/
abbrev IsLocallyOfFiniteTypeAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, IsLocallyOfFiniteType B S hS (w i ≫ pullback.fst (v j) f)

/-- **Stacks 0ANL, condition (5).** There is an affine étale covering of the source, each
member of which factors through an affine formal algebraic space representable étale over the
target by a map which is locally of finite type. -/
abbrev IsLocallyOfFiniteTypeOnFactoredAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS v ∧
          u i ≫ f = t ≫ v ∧ IsLocallyOfFiniteType B S hS t

/-- **Stacks 0ANL, condition (1) implies condition (2).** The square formed by the identities
of `X` and of `Y` witnesses condition (2): both columns are identities, hence representable
étale and surjective, and the upper horizontal map is `f` itself. -/
@[stacks 0ANL "condition (1) implies condition (2), reading surjectivity of the source column \
as surjectivity of the morphism of sheaves"]
theorem isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteTypeOnSomeSquare B S hS f :=
  ⟨X, Y, 𝟙 X, 𝟙 Y, f, hX, hY, isRepresentableEtale_id B S hS X,
    (Sheaf.isLocallySurjective_iff_epi (𝟙 X)).mpr inferInstance,
    isRepresentableEtale_id B S hS Y, hf, by simp⟩

/-- **Stacks 0ANL, condition (3) implies condition (1).** Condition (3), instantiated at the
square formed by the identities of `X` and of `Y`, asserts that `f` itself is locally of finite
type. -/
@[stacks 0ANL "condition (3) implies condition (1), by instantiating condition (3) at the \
square formed by the identities"]
theorem isLocallyOfFiniteType_of_onEverySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnEverySquare B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  hf X Y (𝟙 X) (𝟙 Y) f hX hY (isRepresentableEtale_id B S hS X)
    (isRepresentableEtale_id B S hS Y) (by simp)

/-- **Stacks 0ANL, condition (3) implies condition (2).** Condition (3) gives that `f` is
locally of finite type, and the identity square then witnesses condition (2). -/
@[stacks 0ANL "condition (3) implies condition (2)"]
theorem isLocallyOfFiniteTypeOnSomeSquare_of_onEverySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnEverySquare B S hS f) :
    IsLocallyOfFiniteTypeOnSomeSquare B S hS f :=
  isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType B S hS f hX hY
    (isLocallyOfFiniteType_of_onEverySquare B S hS f hX hY hf)

/-- **Stacks 0ANL, condition (3) implies condition (4).** The atlas of the target and the
atlases of the fibre products of its members with the source witness condition (4): a chart
`Uⱼᵢ` of `Vⱼ ×_Y X` maps to `X` by a representable étale morphism, because the second
projection is a base change of `Vⱼ ⟶ Y`, and the square it forms with `f` and `Vⱼ ⟶ Y`
commutes by the universal property of the fibre product.

The hypothesis `h0AJ3` is the assertion of Stacks 0AJ3 that `Vⱼ ×_Y X` is a formal algebraic
space, which this library does not carry. -/
@[stacks 0ANL "condition (3) implies condition (4), with Stacks 0AJ3 — that the fibre product \
of a chart of the target with the morphism is a formal algebraic space — carried as the \
hypothesis h0AJ3, since this library does not have it"]
theorem isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hY : IsFormalAlgebraicSpace B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (hf : IsLocallyOfFiniteTypeOnEverySquare B S hS f) :
    IsLocallyOfFiniteTypeAfterTargetCover B S hS f := by
  obtain ⟨-, J, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  refine ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, I, U, w, hUaffine, hUetale, hUsurj⟩ := h0AJ3 (V j) (v j) (hVaffine j) (hVetale j)
  refine ⟨I, U, w, ⟨hUaffine, hUetale, hUsurj⟩, fun i ↦ ?_⟩
  refine hf (U i) (V j) (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hUaffine i))
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hVaffine j))
    (IsRepresentableEtale.comp B S hS (hUetale i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hVetale j)))
    (hVetale j) ?_
  rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- **Stacks 0ANL, condition (4) implies condition (5).** Composing the coverings of the fibre
products `Vⱼ ×_Y X` with the second projections gives a covering of `X` indexed by the pairs
`(j, i)`, and the member `Uⱼᵢ ⟶ X` of it factors as `Uⱼᵢ ⟶ Vⱼ ⟶ Y` over `f` through the first
projection, which condition (4) asserts to be locally of finite type.

The hypothesis `h0AIM` is that the composite family is again a covering as in Definition 0AIM.
Its affineness clause is inherited from the given coverings and its representable étaleness
clause follows from `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.comp` together with
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd`; what the library does not
carry is the joint surjectivity of the composite family. -/
@[stacks 0ANL "condition (4) implies condition (5), with the assertion that the composite of \
a covering of the target with coverings of the fibre products is again a covering as in \
Definition 0AIM carried as the hypothesis h0AIM"]
theorem isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (h0AIM : ∀ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
      IsAffineEtaleCover B S hS V v → ∀ (I : J → Type (u + 1))
        (U : ∀ j, I j → FppfSheaf B S hS) (w : ∀ j i, U j i ⟶ pullback (v j) f),
        (∀ j, IsAffineEtaleCover B S hS (U j) (w j)) →
        IsAffineEtaleCover B S hS (fun ji : Σ j, I j ↦ U ji.1 ji.2)
          (fun ji ↦ w ji.1 ji.2 ≫ pullback.snd (v ji.1) f))
    (hf : IsLocallyOfFiniteTypeAfterTargetCover B S hS f) :
    IsLocallyOfFiniteTypeOnFactoredAtlas B S hS f := by
  obtain ⟨J, V, v, hVcover, hcharts⟩ := hf
  choose I U w hUcover hUfinite using hcharts
  refine ⟨Σ j, I j, fun ji ↦ U ji.1 ji.2, fun ji ↦ w ji.1 ji.2 ≫ pullback.snd (v ji.1) f,
    h0AIM J V v hVcover I U w hUcover, fun ji ↦ ?_⟩
  refine ⟨V ji.1, v ji.1, w ji.1 ji.2 ≫ pullback.fst (v ji.1) f, hVcover.1 ji.1,
    hVcover.2.1 ji.1, ?_, hUfinite ji.1 ji.2⟩
  rw [Category.assoc, Category.assoc, ← pullback.condition]

end AlgebraicGeometry.FormalSpace

end
