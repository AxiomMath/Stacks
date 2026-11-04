module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuotientRestriction
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor

/-!
# `Ext` out of `K^p` is the cohomology of `U_p` twisted by the sign character

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S`, let
`W_p = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `p + 1` factors, let `U_p = W_p/S_{p+1}` and let
`ℤ(χ_p)` be the rank one twist of [Stacks 0727] attached to the sign character. This file
proves the identification of the `E₁`-page of [Stacks 0725] asserted by **Stacks 0728**:

`Ext^q_{Ab(X_étale)}(K^p, ℱ) = H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`

for every `q`, and not only for `q = 0`.

The proof is the source's. Restriction to `U_p` is exact and carries injective abelian sheaves
to injective abelian sheaves (`preservesInjectiveObjects_diagonalComplementQuotientRestriction`),
and `Hom(K^p, ℱ) = Hom(ℤ(χ_p), ℱ|_{U_p})` naturally in `ℱ` — both sides being the group of
`S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`, by [Stacks 0726] on one side and the
defining property of the twist on the other. So Stacks 015Z for `Ext`,
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`, identifies `Ext^q(K^p, -)` with
`Ext^q(ℤ(χ_p), -|_{U_p})`.

Tensoring with `ℤ(χ_p)` is an auto-equivalence of abelian sheaves on `U_p`, so it too is exact
and preserves injectives, and it carries `ℤ(χ_p)` to the constant sheaf `ℤ`
(`CategoryTheory.IsTorsorObject.constantSheafIsoTwistTensorSelf`). The same comparison,
in its adjunction form, therefore turns `Ext^q(ℤ(χ_p), -)` into `Ext^q(ℤ, - ⊗_ℤ ℤ(χ_p))`,
which is the cohomology of `U_p` with coefficients in the twisted sheaf.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.koszulCoyonedaRestrictionIso`:
  **`Hom(K^p, ℱ) = Hom(ℤ(χ_p), ℱ|_{U_p})`**, naturally in `ℱ`.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementTwistTensorFunctor`: the
  auto-equivalence `𝒢 ↦ 𝒢 ⊗_ℤ ℤ(χ_p)` of abelian sheaves on `U_p`.
* `AlgebraicGeometry.Space.SpacesEtale.signTwistIsoInvTwistTensorConstant`: `ℤ(χ_p)` is the
  image of the constant sheaf `ℤ` under the inverse of that auto-equivalence.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.nonempty_zExtKoszulSignTwistAddEquiv`: **Stacks 0728,
  the `E₁`-page identification in every degree**, as an isomorphism of abelian groups
  `Ext^q(K^p, ℱ) ≅ Ext^q(ℤ, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`.

## Implementation notes

The `Ext`-groups of the comparison machinery live in the universe of the morphisms of the sheaf
categories, which is `u + 1`, while the pages of the spectral sequence of [Stacks 0725] are
stated with the derived-category `Ext` of
`AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechExtSpectralSequence`. The two are
identified by `CategoryTheory.Abelian.Ext.homAddEquiv`, which for any `Ext`-universe compares
`Ext` with the morphisms of the derived category; the statements below are therefore phrased
with `CategoryTheory.Abelian.zExt`, which needs no `Ext`-universe at all, and the universe
`u + 1` appears only inside the proofs. The instance `HasExt.{u + 1}` is available because the
sheaf categories are Grothendieck abelian at `u + 1`, the level at which the spaces-étale site
is a small category; as in
`AlgebraicGeometry.Space.SpacesEtale.enoughInjectivesSheafSpacesEtale`, that universe is not
determined by the conclusion, so the instance is produced by hand.

## References

* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0725](https://stacks.math.columbia.edu/tag/0725)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom) (p : ℕ)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-! ### `Hom(K^p, ℱ)` is `Hom(ℤ(χ_p), ℱ|_{U_p})` -/

/-- The composite identification of a map `ℤ(χ_p) ⟶ ℱ|_{U_p}` with a map `K^p ⟶ ℱ`: the
section of `ℱ` over `W_p` that the first determines is anti-invariant, hence is the image of a
unique map out of `K^p`. -/
def koszulHomOfTwistHom (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ((characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
        (diagonalComplementSignCharacter (p + 1))).twist ⟶
      (diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F) ≃+
    ((koszulComplex B S hS X U).X p ⟶ F) :=
  ((characterTwistHomAddEquiv (diagonalComplementEtaleSource B S hS X U (p + 1) hsep)
        (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)
        (diagonalComplementSignCharacter (p + 1))
        (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F)).trans
      (diagonalComplementQuotientCharacterSectionsAddEquiv B S hS X U (p + 1) hsep F)).trans
    (koszulHomSignSectionsEquiv B S hS X U p hsep F).symm

/-- The anti-invariant section over `W_p` attached to a map out of `K^p` built from a map out
of `ℤ(χ_p)` is the one the latter determines. -/
theorem koszulHomSignSectionsEquiv_koszulHomOfTwistHom
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (u : (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
        (diagonalComplementSignCharacter (p + 1))).twist ⟶
      (diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F) :
    koszulHomSignSectionsEquiv B S hS X U p hsep F
        (koszulHomOfTwistHom B S hS X U hsep p F u) =
      diagonalComplementQuotientCharacterSectionsAddEquiv B S hS X U (p + 1) hsep F
        (characterTwistHomAddEquiv (diagonalComplementEtaleSource B S hS X U (p + 1) hsep)
          (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)
          (diagonalComplementSignCharacter (p + 1))
          (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
          ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F) u) :=
  (koszulHomSignSectionsEquiv B S hS X U p hsep F).apply_symm_apply _

/-- The identification of maps out of `ℤ(χ_p)` with maps out of `K^p` is natural in the
sheaf. -/
theorem koszulHomOfTwistHom_comp
    {F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}} (k : F ⟶ F')
    (u : (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
        (diagonalComplementSignCharacter (p + 1))).twist ⟶
      (diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F) :
    koszulHomOfTwistHom B S hS X U hsep p F'
        (u ≫ (diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).map k) =
      koszulHomOfTwistHom B S hS X U hsep p F u ≫ k := by
  refine (koszulHomSignSectionsEquiv B S hS X U p hsep F').injective (Subtype.ext ?_)
  have h₁ : ((koszulHomSignSectionsEquiv B S hS X U p hsep F'
        (koszulHomOfTwistHom B S hS X U hsep p F u ≫ k)).1 :
      F'.obj.obj (op (diagonalComplement B S hS X U (p + 1) hsep))) =
      k.hom.app (op (diagonalComplement B S hS X U (p + 1) hsep))
        ((koszulHomSignSectionsEquiv B S hS X U p hsep F
          (koszulHomOfTwistHom B S hS X U hsep p F u)).1) :=
    koszulHomToSignSections_naturality B S hS X U p hsep k _
  rw [h₁, koszulHomSignSectionsEquiv_koszulHomOfTwistHom,
    koszulHomSignSectionsEquiv_koszulHomOfTwistHom]
  exact (congrArg
      (fun t => (diagonalComplementQuotientSectionsIso B S hS X U (p + 1) hsep F').hom t)
      (characterTwistHomEquiv_comp (diagonalComplementEtaleSource B S hS X U (p + 1) hsep)
        (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)
        (diagonalComplementSignCharacter (p + 1))
        (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep)) u
        ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).map k))).trans
    (diagonalComplementQuotientSectionsIso_naturality B S hS X U (p + 1) hsep k _)

/-- **`Hom(K^p, ℱ) = Hom(ℤ(χ_p), ℱ|_{U_p})`, naturally in `ℱ`.** Maps out of the twist are the
sections of `ℱ|_{U_p}` over `W_p` transforming according to the sign character, which are the
`S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`, which are the maps out of `K^p` by
[Stacks 0726]. -/
def koszulCoyonedaRestrictionIso :
    diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep ⋙
        preadditiveCoyoneda.obj
          (op (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
            (diagonalComplementSignCharacter (p + 1))).twist) ≅
      preadditiveCoyoneda.obj (op ((koszulComplex B S hS X U).X p)) :=
  NatIso.ofComponents
    (fun F => AddEquiv.toAddCommGrpIso (koszulHomOfTwistHom B S hS X U hsep p F))
    (fun k => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun u =>
      koszulHomOfTwistHom_comp B S hS X U hsep p k u))

/-! ### Tensoring with `ℤ(χ_p)` -/

/-- The auto-equivalence `𝒢 ↦ 𝒢 ⊗_ℤ ℤ(χ_p)` of abelian sheaves on the spaces-étale site of
`U_p`. -/
abbrev diagonalComplementTwistTensorFunctor :
    Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        AddCommGrpCat.{u + 1} :=
  characterTwistTensorFunctor (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)
    (diagonalComplementSignCharacter (p + 1))
    (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))

/-- Tensoring with `ℤ(χ_p)` is an equivalence of categories of abelian sheaves on `U_p`. -/
instance isEquivalence_diagonalComplementTwistTensorFunctor :
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).IsEquivalence :=
  IsTorsorObject.isEquivalence_characterTwistTensorFunctor
    (diagonalComplementSignCharacter (p + 1))
    (final_isTerminal B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
    (isTorsorObject_diagonalComplement B S hS X U (p + 1) hsep)

/-- Tensoring with `ℤ(χ_p)` preserves finite limits. -/
instance preservesFiniteLimits_diagonalComplementTwistTensorFunctor :
    PreservesFiniteLimits (diagonalComplementTwistTensorFunctor B S hS X U hsep p) :=
  IsTorsorObject.preservesFiniteLimits_characterTwistTensorFunctor
    (diagonalComplementSignCharacter (p + 1))
    (final_isTerminal B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
    (isTorsorObject_diagonalComplement B S hS X U (p + 1) hsep)

/-- Tensoring with `ℤ(χ_p)` preserves finite colimits. -/
instance preservesFiniteColimits_diagonalComplementTwistTensorFunctor :
    PreservesFiniteColimits (diagonalComplementTwistTensorFunctor B S hS X U hsep p) :=
  IsTorsorObject.preservesFiniteColimits_characterTwistTensorFunctor
    (diagonalComplementSignCharacter (p + 1))
    (final_isTerminal B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
    (isTorsorObject_diagonalComplement B S hS X U (p + 1) hsep)

/-- Tensoring with `ℤ(χ_p)` carries injective abelian sheaves to injective abelian sheaves. -/
instance preservesInjectiveObjects_diagonalComplementTwistTensorFunctor :
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).PreservesInjectiveObjects :=
  IsTorsorObject.preservesInjectiveObjects_characterTwistTensorFunctor
    (diagonalComplementSignCharacter (p + 1))
    (final_isTerminal B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
    (isTorsorObject_diagonalComplement B S hS X U (p + 1) hsep)

/-- **Tensoring with `ℤ(χ_p)` is additive.** It preserves finite limits, hence binary products
and the zero morphisms. -/
instance additive_diagonalComplementTwistTensorFunctor :
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of the auto-equivalence `- ⊗_ℤ ℤ(χ_p)` is additive. -/
instance additive_inv_diagonalComplementTwistTensorFunctor :
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).asEquivalence.symm.functor.Additive :=
  have : (diagonalComplementTwistTensorFunctor B S hS X U hsep
      p).asEquivalence.functor.Additive :=
    additive_diagonalComplementTwistTensorFunctor B S hS X U hsep p
  Equivalence.inverse_additive
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).asEquivalence

/-- **`ℤ(χ_p)` is the image of the constant sheaf `ℤ` under the inverse of the auto-equivalence
`- ⊗_ℤ ℤ(χ_p)`.** This is `ℤ ≅ ℤ(χ_p) ⊗_ℤ ℤ(χ_p)` read through the equivalence. -/
def signTwistIsoInvTwistTensorConstant :
    (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
        (diagonalComplementSignCharacter (p + 1))).twist ≅
      (diagonalComplementTwistTensorFunctor B S hS X U hsep p).inv.obj
        (constantIntSheaf B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep)) :=
  (diagonalComplementTwistTensorFunctor B S hS X U hsep p).asEquivalence.unitIso.app
      (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
        (diagonalComplementSignCharacter (p + 1))).twist ≪≫
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).inv.mapIso
      ((isTorsorObject_diagonalComplement B S hS X U (p + 1) hsep).constantSheafIsoTwistTensorSelf
        (diagonalComplementSignCharacter (p + 1))
        (final_isTerminal B S hS
          (diagonalComplementQuotient B S hS X U (p + 1) hsep))).symm

/-! ### The comparison of `Ext` groups -/

/-- **Stacks 0728, the `E₁`-page identification in every degree.** For `U → X` étale and
separated, every `q` and every abelian sheaf `ℱ` on the spaces-étale site of `X`,

`Ext^q_{Ab(X_étale)}(K^p, ℱ) ≅ Ext^q_{Ab(U_{p,étale})}(ℤ, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`,

the right-hand side being the cohomology `H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` of the quotient
`U_p = W_p/S_{p+1}` with coefficients twisted by the sign character. -/
theorem nonempty_zExtKoszulSignTwistAddEquiv (q : ℕ)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Nonempty (zExt ((koszulComplex B S hS X U).X p) F (q : ℤ) ≃+
      zExt (constantIntSheaf B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        ((diagonalComplementTwistTensorFunctor B S hS X U hsep p).obj
          ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F))
        (q : ℤ)) := by
  let hGA : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) := inferInstance
  let hGA' : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        AddCommGrpCat.{u + 1}) := inferInstance
  let : HasExt.{u + 1} (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) := inferInstance
  let : HasExt.{u + 1}
      (Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
        AddCommGrpCat.{u + 1}) := inferInstance
  have e₁ := Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp
    (diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep)
    (koszulCoyonedaRestrictionIso B S hS X U hsep p) q
  have e₂ := Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (diagonalComplementTwistTensorFunctor B S hS X U hsep p).asEquivalence.symm.toAdjunction
    (signTwistIsoInvTwistTensorConstant B S hS X U hsep p).symm q
  exact ⟨(Ext.homAddEquiv.symm.trans
    (((e₁.app F).addCommGroupIsoToAddEquiv.trans
      ((e₂.app ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj
        F)).addCommGroupIsoToAddEquiv)).trans Ext.homAddEquiv))⟩

end AlgebraicGeometry.Space.SpacesEtale

end
