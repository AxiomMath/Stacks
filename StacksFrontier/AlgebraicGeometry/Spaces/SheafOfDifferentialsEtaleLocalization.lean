module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization

/-!
# Étale localization of the sheaf of differentials of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let

```
U --ψ--> V
|        |
a        b
v        v
X --f--> Y
```

be a commutative square whose vertical arrows are étale.  Stacks 04CU asserts the identification
`Ω_{X/Y}|_{U_étale} = Ω_{U/V}`, where the restriction is the pullback of `𝒪_X`-modules along `a`
by the abuse of notation of Stacks' Equation 03LW.  The source's proof has two steps:

1. the restriction of `Ω_{X/Y}` to `U_étale` is the sheaf of differentials of the restricted
   structure map, by Properties of Spaces, Lemma 03LP and Equation 03LQ together with Modules on
   Sites, Lemma 04BO;
2. the restricted base ring is the one of `ψ`, because
   `a_{small}^{-1}f_{small}^{-1}𝒪_{Y_étale} = ψ_{small}^{-1}b_{small}^{-1}𝒪_{Y_étale}
   = ψ_{small}^{-1}𝒪_{V_étale}`, the last equality being the clause `b^{-1}𝒪_Y = 𝒪_V` of
   Stacks 03LV for the étale morphism `b`.

The *second* step is proved here in the form in which it is used: the sheaf of differentials of
a morphism of algebraic spaces depends on the structure map `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` only through
its source up to isomorphism, so two morphisms out of `X` whose structure maps differ by an
isomorphism of their sources have the same sheaf of differentials.  Applied to `ψ : U ⟶ V` and
`ψ ≫ b : U ⟶ Y` this is `Ω_{U/V} = Ω_{U/Y}`, which is what turns step 1 into the statement of
Stacks 04CU.  The isomorphism of structure maps it needs is itself built here, from the
composition law of Stacks 03G8 and the clause `b^{-1}𝒪_Y = 𝒪_V` of Stacks 03LV.

The first step is `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`.  Both
steps are therefore available unconditionally, and
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` assembles them into the
identification the source states with no hypothesis beyond the étaleness of `a` and `b` and the
commutativity of the square.

## Main definitions

* `PresheafOfModules.Derivation'.precompBase` transports a relative derivation along a morphism
  of the presheaf of commutative rings it is taken relative to, in the direction in which no
  condition has to be checked: the underlying additive map is unchanged.
* `AlgebraicGeometry.Space.sharpIsoHom` and `AlgebraicGeometry.Space.sharpIsoInv` are the two
  comparison morphisms `Ω_{X/Y} ⟶ Ω_{X/Z}` and `Ω_{X/Z} ⟶ Ω_{X/Y}`, each factoring one
  universal derivation read through the other base.
* `AlgebraicGeometry.Space.sharpFactorHom` and `AlgebraicGeometry.Space.sharpFactorInv` read the
  isomorphism of structure maps on underlying presheaves of commutative rings.
* `AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso` is the étale-base comparison
  `(ψ ≫ b)^{-1}𝒪_Y ≅ ψ^{-1}𝒪_V` for an étale `b`, from Stacks 03G8 and 03LV.

## Main results

* `PresheafOfModules.Derivation'.precompBase_postcomp` and
  `PresheafOfModules.Derivation'.precompBase_precompBase`: the two calculations with derivations
  that the identification below adds to the two postcomposition lemmas it imports, each of them
  an equality of underlying additive maps.
* `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`: if the structure maps of
  `p : X ⟶ Y` and `q : X ⟶ Z` differ by an isomorphism of their sources, then
  `Ω_{X/Y} ≅ Ω_{X/Z}`, by the identification carrying one universal derivation to the other.
* `AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsIsoOfSharpIso`: that
  identification carries `d_{X/Y}` to `d_{X/Z}` on sections, so it is canonical.
* `AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage`:
  the étale-base comparison carries `ψ♯` to `(ψ ≫ b)♯`.
* `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`: **Stacks 04CU**, the
  identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}`, assembled from the étale-source localization of
  Stacks 03LP, 03LQ and 04BO and the étale-base comparison above.

## Implementation notes

A `PresheafOfModules.Derivation'` relative to `φ : A ⟶ 𝒪` is an additive map on the sections of
`𝒪` subject to the Leibniz rule and to vanishing on the image of `φ`; only the last condition
mentions `A`.  So a derivation relative to `φ` is one relative to `e ≫ φ` for any `e`, with the
*same* underlying additive map, and when `e` is invertible the two notions coincide.  That is
`PresheafOfModules.Derivation'.precompBase`, and it is why no comparison of the two sheaves of
differentials has to be built by hand: both corepresent the same functor of derivations, by
`AlgebraicGeometry.Space.universalDerivation_isUniversal`, and the identification is read off
from `AlgebraicGeometry.Space.differentialsHomEquiv` in both directions.

`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` takes an isomorphism `e` of the two
*sheaves* of commutative rings together with the equation `e.hom ≫ p♯ = q♯`, rather than
invertibility of a given comparison, because that is the shape in which the composition law of
Stacks 03G8 and the clause `b^{-1}𝒪_Y = 𝒪_V` of Stacks 03LV produce it: the comparison of
`(ψ ≫ b)^{-1}𝒪_Y` with `ψ^{-1}𝒪_V` is `ψ^{-1}` of the structure map of `b`, followed by the
comparison of the two inverse images of a composite.  That is exactly how
`AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso` is built.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP) and
  [Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ), restriction to the small étale site of
  an étale morphism as the inverse image.
* [Stacks Project, Tag 04BO](https://stacks.math.columbia.edu/tag/04BO), differentials and
  localization at an object of a site.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), the clause
  `b^{-1}𝒪_Y = 𝒪_V` for an étale morphism `b`.
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW), the abuse of notation
  `G|_{U_étale} = a^*G`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v w v₂ u₂ u

namespace PresheafOfModules.Derivation'

variable {E : Type u₂} [Category.{v₂} E] {S₁ S₂ R : Eᵒᵖ ⥤ CommRingCat.{w}}
  {M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
  {a₁ : S₁ ⟶ R} {a₂ : S₂ ⟶ R}

/-- A relative derivation of `M` over `a₁ : S₁ ⟶ R`, read as a relative derivation over
`a₂ : S₂ ⟶ R` whenever `a₂` factors as `e ≫ a₁`.  The underlying additive map is unchanged: the
Leibniz rule and the compatibility with restriction do not mention the base, and the vanishing
on the image of `a₂` is the vanishing on the image of `a₁` at the sections `e` produces. -/
def precompBase (e : S₂ ⟶ S₁) (h : e ≫ a₁ = a₂) (D : M.Derivation' a₁) : M.Derivation' a₂ where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {X} s := by
    subst h
    exact D.d_app (e.app X s)

/-- The transported derivation has the same underlying additive map. -/
@[simp]
lemma precompBase_d (e : S₂ ⟶ S₁) (h : e ≫ a₁ = a₂) (D : M.Derivation' a₁) {X : Eᵒᵖ}
    (x : R.obj X) : (precompBase e h D).d x = D.d x := rfl

/-- Reading a derivation over a factored base commutes with postcomposition by a morphism of
presheaves of modules, both operations acting on the underlying additive map alone. -/
lemma precompBase_postcomp (e : S₂ ⟶ S₁) (h : e ≫ a₁ = a₂) (D : M.Derivation' a₁)
    (α : M ⟶ N) : (precompBase e h D).postcomp α = precompBase e h (D.postcomp α) := by
  apply PresheafOfModules.Derivation.ext
  ext X z
  rfl

/-- Reading a derivation over a factored base and back returns it. -/
lemma precompBase_precompBase (e : S₂ ⟶ S₁) (h : e ≫ a₁ = a₂) (e' : S₁ ⟶ S₂)
    (h' : e' ≫ a₂ = a₁) (D : M.Derivation' a₁) :
    precompBase e' h' (precompBase e h D) = D := by
  apply PresheafOfModules.Derivation.ext
  ext X z
  rfl

end PresheafOfModules.Derivation'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

section SharpIso

variable (p : X ⟶ Y) (q : X ⟶ Z)
  (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)

/-- The hypothesis of `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` on underlying
presheaves of commutative rings. -/
lemma sharpFactorHom
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    e.hom.hom ≫ (structureSharpInverseImage B S hS p).hom =
      (structureSharpInverseImage B S hS q).hom := by
  rw [← he]
  rfl

/-- The hypothesis of `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` for the inverse
of `e`, on underlying presheaves of commutative rings. -/
lemma sharpFactorInv
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    e.inv.hom ≫ (structureSharpInverseImage B S hS q).hom =
      (structureSharpInverseImage B S hS p).hom := by
  have h : e.inv ≫ structureSharpInverseImage B S hS q =
      structureSharpInverseImage B S hS p := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [← h]
  rfl

/-- The forward comparison `Ω_{X/Y} ⟶ Ω_{X/Z}` of
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`: the morphism through which the
universal `Z`-derivation `d_{X/Z}`, read as a `Y`-derivation along `e.inv`, factors. -/
def sharpIsoHom
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    sheafOfDifferentials B S hS p ⟶ sheafOfDifferentials B S hS q :=
  (differentialsHomEquiv B S hS p (sheafOfDifferentials B S hS q)).symm
    ((universalDerivation B S hS q).precompBase e.inv.hom (sharpFactorInv B S hS p q e he))

/-- The backward comparison `Ω_{X/Z} ⟶ Ω_{X/Y}`: the morphism through which the universal
`Y`-derivation `d_{X/Y}`, read as a `Z`-derivation along `e.hom`, factors. -/
def sharpIsoInv
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    sheafOfDifferentials B S hS q ⟶ sheafOfDifferentials B S hS p :=
  (differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS p)).symm
    ((universalDerivation B S hS p).precompBase e.hom.hom (sharpFactorHom B S hS p q e he))

/-- The defining property of the forward comparison. -/
lemma postcomp_sharpIsoHom
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    (universalDerivation B S hS p).postcomp (sharpIsoHom B S hS p q e he).val =
      (universalDerivation B S hS q).precompBase e.inv.hom (sharpFactorInv B S hS p q e he) :=
  (differentialsHomEquiv B S hS p (sheafOfDifferentials B S hS q)).apply_symm_apply _

/-- The defining property of the backward comparison. -/
lemma postcomp_sharpIsoInv
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    (universalDerivation B S hS q).postcomp (sharpIsoInv B S hS p q e he).val =
      (universalDerivation B S hS p).precompBase e.hom.hom (sharpFactorHom B S hS p q e he) :=
  (differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS p)).apply_symm_apply _

/-- **Stacks 04CU, the étale-base step.**  If the structure maps of `p : X ⟶ Y` and `q : X ⟶ Z`
differ by an isomorphism `e` of their sources, then the two sheaves of differentials agree:
`Ω_{X/Y} ≅ Ω_{X/Z}`.

Both sheaves corepresent the same functor of derivations — a `Y`-derivation and a `Z`-derivation
are the same additive map, by `PresheafOfModules.Derivation'.precompBase` applied to `e` and to
its inverse — so the identification is the one matching the two universal derivations.

Applied to `ψ : U ⟶ V` and `ψ ≫ b : U ⟶ Y` for an étale `b : V ⟶ Y` this is the equality
`Ω_{U/V} = Ω_{U/Y}` which the final sentence of the source's proof uses. -/
@[stacks 04CU "the étale-base step: Ω_{X/Y} = Ω_{X/Z} when the two structure maps differ by an
  isomorphism of their sources, which is what 03G8 and the clause `b⁻¹𝒪_Y = 𝒪_V` of 03LV supply
  for an étale `b : V ⟶ Y` at `p = ψ`, `q = ψ ≫ b`"]
def sheafOfDifferentialsIsoOfSharpIso
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    sheafOfDifferentials B S hS p ≅ sheafOfDifferentials B S hS q where
  hom := sharpIsoHom B S hS p q e he
  inv := sharpIsoInv B S hS p q e he
  hom_inv_id := by
    refine (differentialsHomEquiv B S hS p (sheafOfDifferentials B S hS p)).injective ?_
    refine Eq.trans (PresheafOfModules.Derivation'.postcomp_comp
      (universalDerivation B S hS p) (sharpIsoHom B S hS p q e he).val
      (sharpIsoInv B S hS p q e he).val) ?_
    refine Eq.trans (congrArg (fun T ↦ PresheafOfModules.Derivation.postcomp T
      (sharpIsoInv B S hS p q e he).val) (postcomp_sharpIsoHom B S hS p q e he)) ?_
    refine Eq.trans (PresheafOfModules.Derivation'.precompBase_postcomp e.inv.hom
      (sharpFactorInv B S hS p q e he) (universalDerivation B S hS q)
      (sharpIsoInv B S hS p q e he).val) ?_
    refine Eq.trans (congrArg (fun T ↦ PresheafOfModules.Derivation'.precompBase e.inv.hom
      (sharpFactorInv B S hS p q e he) T) (postcomp_sharpIsoInv B S hS p q e he)) ?_
    exact Eq.trans (PresheafOfModules.Derivation'.precompBase_precompBase e.hom.hom
        (sharpFactorHom B S hS p q e he) e.inv.hom (sharpFactorInv B S hS p q e he)
        (universalDerivation B S hS p))
      (PresheafOfModules.Derivation'.postcomp_id (universalDerivation B S hS p)).symm
  inv_hom_id := by
    refine (differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS q)).injective ?_
    refine Eq.trans (PresheafOfModules.Derivation'.postcomp_comp
      (universalDerivation B S hS q) (sharpIsoInv B S hS p q e he).val
      (sharpIsoHom B S hS p q e he).val) ?_
    refine Eq.trans (congrArg (fun T ↦ PresheafOfModules.Derivation.postcomp T
      (sharpIsoHom B S hS p q e he).val) (postcomp_sharpIsoInv B S hS p q e he)) ?_
    refine Eq.trans (PresheafOfModules.Derivation'.precompBase_postcomp e.hom.hom
      (sharpFactorHom B S hS p q e he) (universalDerivation B S hS p)
      (sharpIsoHom B S hS p q e he).val) ?_
    refine Eq.trans (congrArg (fun T ↦ PresheafOfModules.Derivation'.precompBase e.hom.hom
      (sharpFactorHom B S hS p q e he) T) (postcomp_sharpIsoHom B S hS p q e he)) ?_
    exact Eq.trans (PresheafOfModules.Derivation'.precompBase_precompBase e.inv.hom
        (sharpFactorInv B S hS p q e he) e.hom.hom (sharpFactorHom B S hS p q e he)
        (universalDerivation B S hS q))
      (PresheafOfModules.Derivation'.postcomp_id (universalDerivation B S hS q)).symm

/-- **Stacks 04CU, the étale-base step is canonical.**  The identification of
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` carries the universal
`Y`-derivation `d_{X/Y}` of a local section to the universal `Z`-derivation `d_{X/Z}` of the
same section, so it is the comparison the source names and not merely some isomorphism. -/
@[stacks 04CU "the étale-base step carries one universal derivation to the other"]
lemma universalDerivation_sheafOfDifferentialsIsoOfSharpIso
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q)
    {W : (SmallEtale B S hS X.1)ᵒᵖ} (x : (structureRingSheaf B S hS X).obj.obj W) :
    (((sharpIsoHom B S hS p q e he).val.app W).hom)
        ((universalDerivation B S hS p).d x) =
      (universalDerivation B S hS q).d x := by
  have h := (differentialsHomEquiv B S hS p (sheafOfDifferentials B S hS q)).apply_symm_apply
    ((universalDerivation B S hS q).precompBase e.inv.hom (sharpFactorInv B S hS p q e he))
  exact PresheafOfModules.Derivation.congr_d h x

end SharpIso

variable {U V : AlgebraicSpaces B S hS}

/-- The étale-base comparison `(ψ ≫ b)^{-1}𝒪_Y ≅ ψ^{-1}𝒪_V` for an étale `b : V ⟶ Y`: the
composition law of Stacks 03G8 for inverse images of sheaves of commutative rings, followed by
the clause `b^{-1}𝒪_Y = 𝒪_V` of Stacks 03LV taken inside `ψ^{-1}`. -/
noncomputable def etaleBaseInverseImageStructureSheafIso (ψ : U ⟶ V) (b : V ⟶ Y)
    (hb : IsEtale B S hS b.hom) :
    inverseImageStructureSheaf B S hS (ψ ≫ b) ≅ inverseImageStructureSheaf B S hS ψ :=
  (inverseImageStructureSheafCompIso B S hS ψ b).symm ≪≫
    (smallEtaleInverseImageRing B S hS ψ).mapIso
      (etaleInverseImageStructureSheafIso B S hS b hb)

/-- The étale-base comparison carries the structure map `ψ♯ : ψ^{-1}𝒪_V ⟶ 𝒪_U` to the structure
map `(ψ ≫ b)♯`, which is the compatibility that the étale-base step of Stacks 04CU consumes. -/
theorem etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage (ψ : U ⟶ V)
    (b : V ⟶ Y) (hb : IsEtale B S hS b.hom) :
    (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb).hom ≫
        structureSharpInverseImage B S hS ψ =
      structureSharpInverseImage B S hS (ψ ≫ b) := by
  have key := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS ψ b
  change ((inverseImageStructureSheafCompIso B S hS ψ b).inv ≫
      (smallEtaleInverseImageRing B S hS ψ).map
        (etaleInverseImageStructureSheafIso B S hS b hb).hom) ≫
      (smallEtaleRingedToposHom B S hS ψ).fSharpInverseImage =
    (smallEtaleRingedToposHom B S hS (ψ ≫ b)).fSharpInverseImage
  rw [etaleInverseImageStructureSheafIso_hom, Category.assoc]
  exact Eq.trans
    (congrArg (fun z => (inverseImageStructureSheafCompIso B S hS ψ b).inv ≫ z) key.symm)
    ((inverseImageStructureSheafCompIso B S hS ψ b).inv_hom_id_assoc _)

/-- **Stacks 04CU.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let
`a ≫ f = ψ ≫ b` be a commutative square with `a : U ⟶ X` and `b : V ⟶ Y` étale.  Then the
restriction of `Ω_{X/Y}` to the small étale site of `U` — the pullback of `𝒪_X`-modules along
`a`, by the abuse of notation of Stacks' Equation 03LW — is `Ω_{U/V}`.

The source's proof has two steps and both are carried out here.  Its first step is the
étale-source localization `Ω_{X/Y}|_{U_étale} = Ω_{U/Y}` of Stacks 03LP, 03LQ and 04BO, which is
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` at the étale `a`.  Its
second step is the identification `ψ^{-1}𝒪_V = (ψ ≫ b)^{-1}𝒪_Y` under the structure maps, which
is `AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso` and its compatibility, from
the composition law of Stacks 03G8 and the clause `b^{-1}𝒪_Y = 𝒪_V` of Stacks 03LV for the
étale `b`.  The square then identifies `Ω_{U/Y}` with `Ω_{U/(ψ ≫ b)}`, and
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` identifies that with `Ω_{U/V}`. -/
@[stacks 04CU "the identification Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V} on a square of étale charts, from
  the étale-source localization of 03LP, 03LQ and 04BO and the étale-base comparison of 03G8 and
  03LV"]
noncomputable def sheafOfDifferentialsEtaleLocalizationIso (f : X ⟶ Y) (a : U ⟶ X) (ψ : U ⟶ V)
    (b : V ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = ψ ≫ b) :
    (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ≅
      sheafOfDifferentials B S hS ψ :=
  sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f ≪≫
    eqToIso (congrArg (fun g : U ⟶ Y => sheafOfDifferentials B S hS g) hcomm) ≪≫
    (sheafOfDifferentialsIsoOfSharpIso B S hS ψ (ψ ≫ b)
      (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb)
      (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage
        B S hS ψ b hb)).symm

end AlgebraicGeometry.Space

end
