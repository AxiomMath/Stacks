module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.CoforkTransport
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# Coequalizers of finite étale covers, and finite colimits of `FÉt_X`

Let `X` be a scheme and let `a, b : Y ⟶ Z` be two morphisms of finite étale covers of `X`. A
finite morphism is affine, so `Y` and `Z` are objects of the category of schemes affine over
`X`, and under the anti-equivalence of Stacks Tag 01SA they correspond to the quasi-coherent
`𝒪_X`-algebras `Z_* 𝒪` and `Y_* 𝒪`, the pair `a, b` corresponding to a pair of morphisms
`a^♯, b^♯ : Z_* 𝒪 ⇉ Y_* 𝒪`. The equalizer `𝓐 = Eq(a^♯, b^♯)` of that pair is again a
quasi-coherent algebra, and its relative spectrum is finite étale over `X`; so `Spec_X 𝓐` is
again an object of `FÉt_X`, and transporting the equalizer back along the fully faithful
contravariant functor `FÉt_X ⥤ QCoh-Alg_X` exhibits it as the coequalizer of `a` and `b`
in `FÉt_X`.

Together with the finite coproducts of
`Stacks.FundamentalGroup.hasFiniteCoproducts_finiteEtaleOver` this gives all finite colimits of
`FÉt_X`, which is the right-exactness half of the first assertion of Stacks Tag 0BN9.

## Main definitions

* `Stacks.FundamentalGroup.affineOfFiniteEtale` — a finite étale cover of `X` is affine over
  `X`, as a functor `FÉt_X ⥤ Aff_X`.
* `Stacks.FundamentalGroup.finiteEtalePushforwardFunctor` — the resulting fully faithful
  contravariant functor `Y ↦ Y_* 𝒪` from `FÉt_X` to the quasi-coherent `𝒪_X`-algebras.
* `Stacks.FundamentalGroup.equalizerPushforwardAlgebra` — the equalizer `Eq(a^♯, b^♯)`.
* `Stacks.FundamentalGroup.finiteEtaleCoequalizer` — its relative spectrum, as an object of
  `FÉt_X`, with `Stacks.FundamentalGroup.finiteEtaleCoequalizerπ` the projection from `Z`.

## Main results

* `Stacks.FundamentalGroup.finiteEtale_relativeSpecToBase_equalizerPushforwardAlgebra` — the
  relative spectrum of `Eq(a^♯, b^♯)` is finite étale over `X`.
* `Stacks.FundamentalGroup.isColimit_finiteEtaleCofork` — **the coequalizer of two morphisms of
  finite étale covers of `X` is the relative spectrum of the equalizer of the two induced maps
  of quasi-coherent algebras**, and `Stacks.FundamentalGroup.hasCoequalizers_finiteEtaleOver`
  the resulting instance.
* `Stacks.FundamentalGroup.hasFiniteColimits_finiteEtaleOver` — **`FÉt_X` has finite
  colimits.**

## Implementation notes

The anti-equivalence is used only through its underlying functor
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentPushforwardFunctor`, which is fully
faithful, and whose value on an object affine over `X` *is* the pushed-forward structure sheaf
(`Stacks.AffineAlgebraEquivalence.pushforwardIso_rfl`, proved by `rfl`). So
`finiteEtalePushforwardFunctor` sends a finite étale cover to `pushforwardAlgebra` of its
structure morphism definitionally, which is what makes
`Stacks.QuasicoherentAlgebraEqualizer.isFinite_and_etale_relativeSpecToBase_of_finiteEtale`
applicable to the induced pair of algebra maps without any transport.

Essential surjectivity enters only through
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, the isomorphism
`(relativeSpecToBase 𝓐)_* 𝒪 ≅ 𝓐`, which identifies the image of the apex
`finiteEtaleCoequalizer` with the equalizer algebra; the projection
`finiteEtaleCoequalizerπ` is defined as the preimage under the fully faithful functor of that
isomorphism followed by the equalizer inclusion, so that
`Stacks.FundamentalGroup.map_op_finiteEtaleCoequalizerπ` holds. The universal property is then
`Stacks.FundamentalGroup.isColimitCoforkOfIsLimitFork` applied to
`Stacks.QuasicoherentAlgebraEqualizer.isLimitQuasicoherentFork`.

Quasi-coherence of the equalizer algebra is the property field of the object
`equalizerPushforwardAlgebra` of the full subcategory of quasi-coherent algebras; it is a
`Prop`, so the instance it provides is interchangeable with any other proof of the same
statement and the relative spectrum it defines is unambiguous. It is introduced by `let` rather
than `letI` so that its value stays visible.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.QuasicoherentAlgebraEqualizer

universe u

namespace Stacks.FundamentalGroup

/-! ### Finite étale covers are affine over the base -/

/-- A finite étale cover of `X` is affine over `X`: the forgetful functor from the finite étale
covers of `X` to the schemes affine over `X`. -/
def affineOfFiniteEtale (X : Scheme.{u}) :
    FiniteEtaleOver X ⥤ AffineOver X :=
  (IsAffineHomOver X).lift (MorphismProperty.Over.forget finiteEtale ⊤ X) fun Y ↦ by
    have : IsFinite Y.hom := Y.prop.1
    exact inferInstanceAs (IsAffineHom Y.hom)

/-- The forgetful functor to the schemes affine over `X` is full. -/
instance full_affineOfFiniteEtale (X : Scheme.{u}) : (affineOfFiniteEtale X).Full :=
  inferInstanceAs (((IsAffineHomOver X).lift
    (MorphismProperty.Over.forget finiteEtale ⊤ X) _).Full)

/-- The forgetful functor to the schemes affine over `X` is faithful. -/
instance faithful_affineOfFiniteEtale (X : Scheme.{u}) : (affineOfFiniteEtale X).Faithful :=
  inferInstanceAs (((IsAffineHomOver X).lift
    (MorphismProperty.Over.forget finiteEtale ⊤ X) _).Faithful)

/-- The contravariant functor `Y ↦ Y_* 𝒪` from the finite étale covers of `X` to the
quasi-coherent `𝒪_X`-algebras, the restriction of the anti-equivalence of Stacks Tag 01SA. -/
def finiteEtalePushforwardFunctor (X : Scheme.{u}) :
    (FiniteEtaleOver X)ᵒᵖ ⥤ QuasicoherentAlgebra X :=
  (affineOfFiniteEtale X).op ⋙ affineQuasicoherentPushforwardFunctor X

/-- The pushforward functor on finite étale covers is full. -/
instance full_finiteEtalePushforwardFunctor (X : Scheme.{u}) :
    (finiteEtalePushforwardFunctor X).Full :=
  inferInstanceAs (((affineOfFiniteEtale X).op ⋙ _).Full)

/-- The pushforward functor on finite étale covers is faithful. -/
instance faithful_finiteEtalePushforwardFunctor (X : Scheme.{u}) :
    (finiteEtalePushforwardFunctor X).Faithful :=
  inferInstanceAs (((affineOfFiniteEtale X).op ⋙ _).Faithful)

/-- The algebra attached to a finite étale cover is the pushforward of its structure sheaf. -/
theorem obj_finiteEtalePushforwardFunctor {X : Scheme.{u}} (Y : FiniteEtaleOver X) :
    ((finiteEtalePushforwardFunctor X).obj (op Y)).obj = pushforwardAlgebra Y.hom :=
  rfl

/-! ### The equalizer of the two induced maps of algebras -/

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X} (a b : Y ⟶ Z)

/-- The equalizer `Eq(a^♯, b^♯)` of the two maps of quasi-coherent `𝒪_X`-algebras induced by a
pair of morphisms `a, b : Y ⟶ Z` of finite étale covers of `X`. -/
def equalizerPushforwardAlgebra : QuasicoherentAlgebra X :=
  quasicoherentEqualizer ((finiteEtalePushforwardFunctor X).map a.op)
    ((finiteEtalePushforwardFunctor X).map b.op)

/-- The inclusion of the equalizer `Eq(a^♯, b^♯)` into `Z_* 𝒪`. -/
def equalizerPushforwardAlgebraι :
    equalizerPushforwardAlgebra a b ⟶ (finiteEtalePushforwardFunctor X).obj (op Z) :=
  quasicoherentEqualizerι _ _

/-- The inclusion of the equalizer equalizes the two induced algebra maps. -/
theorem equalizerPushforwardAlgebraι_comp :
    equalizerPushforwardAlgebraι a b ≫ (finiteEtalePushforwardFunctor X).map a.op =
      equalizerPushforwardAlgebraι a b ≫ (finiteEtalePushforwardFunctor X).map b.op :=
  quasicoherentEqualizerι_comp _ _

/-- **The equalizer of the two maps of quasi-coherent algebras induced by `a` and `b`** is
`Eq(a^♯, b^♯)`, computed on sections. -/
def isLimitForkEqualizerPushforwardAlgebra :
    IsLimit (Fork.ofι (equalizerPushforwardAlgebraι a b)
      (equalizerPushforwardAlgebraι_comp a b)) :=
  isLimitQuasicoherentFork _ _

/-! ### The coequalizer of two morphisms of finite étale covers -/

/-- **The relative spectrum of the equalizer `Eq(a^♯, b^♯)` is finite étale over the base.**
This is
`Stacks.QuasicoherentAlgebraEqualizer.isFinite_and_etale_relativeSpecToBase_of_finiteEtale`
for the two algebra maps induced by `a` and `b`. -/
theorem finiteEtale_relativeSpecToBase_equalizerPushforwardAlgebra :
    finiteEtale (@relativeSpecToBase X (equalizerPushforwardAlgebra a b).obj
      (equalizerPushforwardAlgebra a b).property) := by
  obtain ⟨_, _⟩ := Z.prop
  obtain ⟨_, _⟩ := Y.prop
  exact isFinite_and_etale_relativeSpecToBase_of_finiteEtale Z.hom Y.hom
    ((finiteEtalePushforwardFunctor X).map a.op).hom
    ((finiteEtalePushforwardFunctor X).map b.op).hom

/-- The relative spectrum of `Eq(a^♯, b^♯)`, as a finite étale cover of `X`. This is the
coequalizer of `a` and `b`. -/
def finiteEtaleCoequalizer : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤
    (@relativeSpecToBase X (equalizerPushforwardAlgebra a b).obj
      (equalizerPushforwardAlgebra a b).property)
    (finiteEtale_relativeSpecToBase_equalizerPushforwardAlgebra a b)

/-- The algebra of the relative spectrum of `Eq(a^♯, b^♯)` is `Eq(a^♯, b^♯)`: essential
surjectivity of the pushforward functor at the equalizer algebra. -/
def pushforwardFiniteEtaleCoequalizerIso :
    (finiteEtalePushforwardFunctor X).obj (op (finiteEtaleCoequalizer a b)) ≅
      equalizerPushforwardAlgebra a b :=
  let := (equalizerPushforwardAlgebra a b).property
  (IsQuasicoherentAlgebra X).ι.preimageIso
    (pushforwardAlgebraIso (equalizerPushforwardAlgebra a b).obj)

/-- The projection of `Z` onto the relative spectrum of `Eq(a^♯, b^♯)`, the morphism of finite
étale covers corresponding to the inclusion of the equalizer algebra into `Z_* 𝒪`. -/
def finiteEtaleCoequalizerπ : Z ⟶ finiteEtaleCoequalizer a b :=
  ((finiteEtalePushforwardFunctor X).preimage
    ((pushforwardFiniteEtaleCoequalizerIso a b).hom ≫
      equalizerPushforwardAlgebraι a b)).unop

/-- The image of the projection onto the coequalizer under the pushforward functor is the
inclusion of the equalizer algebra, transported along the identification of the algebra of the
relative spectrum. -/
theorem map_op_finiteEtaleCoequalizerπ :
    (finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ a b).op =
      (pushforwardFiniteEtaleCoequalizerIso a b).hom ≫ equalizerPushforwardAlgebraι a b :=
  (finiteEtalePushforwardFunctor X).map_preimage _

/-- The image of the projection onto the coequalizer equalizes the two induced algebra maps. -/
theorem map_op_finiteEtaleCoequalizerπ_comp :
    (finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ a b).op ≫
        (finiteEtalePushforwardFunctor X).map a.op =
      (finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ a b).op ≫
        (finiteEtalePushforwardFunctor X).map b.op := by
  rw [map_op_finiteEtaleCoequalizerπ, Category.assoc, Category.assoc,
    equalizerPushforwardAlgebraι_comp]

/-- The projection onto the relative spectrum of `Eq(a^♯, b^♯)` coequalizes `a` and `b`. -/
theorem comp_finiteEtaleCoequalizerπ :
    a ≫ finiteEtaleCoequalizerπ a b = b ≫ finiteEtaleCoequalizerπ a b :=
  comp_eq_of_map_op_comp_eq (finiteEtalePushforwardFunctor X) (finiteEtaleCoequalizerπ a b)
    (map_op_finiteEtaleCoequalizerπ_comp a b)

/-- The identification of the algebra of the relative spectrum carries the image of the
projection onto the coequalizer to the inclusion of the equalizer algebra. -/
theorem inv_comp_map_op_finiteEtaleCoequalizerπ :
    (pushforwardFiniteEtaleCoequalizerIso a b).inv ≫
        (finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ a b).op =
      equalizerPushforwardAlgebraι a b := by
  rw [map_op_finiteEtaleCoequalizerπ, Iso.inv_hom_id_assoc]

/-- The image under the pushforward functor of the cofork on `a` and `b` with apex the relative
spectrum of `Eq(a^♯, b^♯)` is the equalizer of the two induced algebra maps. -/
def isLimitForkMapOpFiniteEtaleCoequalizerπ :
    IsLimit (Fork.ofι ((finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ a b).op)
      (map_op_finiteEtaleCoequalizerπ_comp a b)) :=
  IsLimit.ofIsoLimit (isLimitForkEqualizerPushforwardAlgebra a b)
    (Fork.ext (pushforwardFiniteEtaleCoequalizerIso a b).symm
      (inv_comp_map_op_finiteEtaleCoequalizerπ a b))

/-- **The coequalizer of two morphisms of finite étale covers of `X`**, Stacks Tag 0BN9: it is
the relative spectrum of the equalizer of the two induced maps of quasi-coherent
`𝒪_X`-algebras.

Under the anti-equivalence of Stacks Tag 01SA the pair `a, b : Y ⟶ Z` corresponds to a pair
`a^♯, b^♯ : Z_* 𝒪 ⇉ Y_* 𝒪` of maps of quasi-coherent algebras, whose equalizer is computed on
sections; `Stacks.FundamentalGroup.isColimitCoforkOfIsLimitFork` transports that equalizer back
to a coequalizer, and the apex is a finite étale cover because the structure map of its algebra
is finite étale on sections over every affine open. -/
def isColimit_finiteEtaleCofork :
    IsColimit (Cofork.ofπ (finiteEtaleCoequalizerπ a b) (comp_finiteEtaleCoequalizerπ a b)) :=
  isColimitCoforkOfIsLimitFork (finiteEtalePushforwardFunctor X) (finiteEtaleCoequalizerπ a b)
    (map_op_finiteEtaleCoequalizerπ_comp a b) (isLimitForkMapOpFiniteEtaleCoequalizerπ a b)

/-- Two morphisms of finite étale covers of `X` have a coequalizer in `FÉt_X`. -/
instance hasCoequalizer_finiteEtaleOver : HasCoequalizer a b :=
  ⟨⟨⟨_, isColimit_finiteEtaleCofork a b⟩⟩⟩

/-- **Stacks 0BN9**, the coequalizer half of right exactness: the category of schemes finite
étale over a scheme has coequalizers. -/
instance hasCoequalizers_finiteEtaleOver (X : Scheme.{u}) : HasCoequalizers (FiniteEtaleOver X) :=
  hasCoequalizers_of_hasColimit_parallelPair _

/-- **Stacks 0BN9**, right exactness: the category of schemes finite étale over a scheme has
finite colimits. The finite coproducts are the disjoint unions of
`Stacks.FundamentalGroup.hasFiniteCoproducts_finiteEtaleOver` and the coequalizers are the
relative spectra of the equalizer algebras of
`Stacks.FundamentalGroup.isColimit_finiteEtaleCofork`. -/
-- NO `@[stacks 0BN9]` ATTRIBUTE HERE. The finite-colimit clause of 0BN9 is stated on a
-- declaration whose type is `HasFiniteColimitsWithLocalCoequalizers X`, which is strictly more
-- than this instance; that clause site is
-- `Stacks.FundamentalGroup.hasFiniteColimitsWithLocalCoequalizers` of
-- `FiniteEtaleColimits/LocalCoequalizer.lean`, which is proved from this instance. The one clause
-- of 0BN9 still open is the preservation of finite colimits under base change along a general
-- morphism; `Stacks.FundamentalGroup.isColimitCoforkBaseChange` has it for a flat morphism and
-- `Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange_geometricPoint` for a
-- geometric point.
instance hasFiniteColimits_finiteEtaleOver (X : Scheme.{u}) :
    HasFiniteColimits (FiniteEtaleOver X) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end Stacks.FundamentalGroup

end
