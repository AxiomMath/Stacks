module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.AntiInvariantSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementCharacterTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientBase
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite

/-!
# Restricting an abelian sheaf from `X` to the quotient `U_p = W_p/S_{p+1}`

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S`, let
`W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors and let `U_p = W/S_n`, an object of the
spaces-étale site of `X` by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientObject`. This file builds the
restriction functor `ℱ ↦ ℱ|_{U_p}` on abelian sheaves, shows that it is exact and preserves
injectives, and identifies the `χ`-semi-invariant sections of `ℱ|_{U_p}` over `W` with the
`S_n`-anti-invariant sections of `ℱ` over `W`.

All declarations live in the namespace `AlgebraicGeometry.Space.SpacesEtale`.

The restriction is the composite of restriction to the slice of the spaces-étale site of `X`
at `U_p` with the identification of that slice with the spaces-étale site of `U_p`. The first
factor is exact and preserves injectives, by [Stacks 01DR] through
`Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback`, and the second is an
equivalence of categories.

Sections over `W` do not move: `W` with its projection to `U_p` is an object of the slice whose
image in the spaces-étale site of `U_p` is `W` itself, so the unit of the equivalence gives an
isomorphism of the sections of `ℱ|_{U_p}` over `W` with the sections of `ℱ` over `W`, natural
in `ℱ` and compatible with the two readings of the action of the symmetric group. That is what
carries one group of semi-invariant sections to the other.

## Main definitions

* `diagonalComplementQuotientRestriction`: **the restriction `ℱ ↦ ℱ|_{U_p}`.**
* `diagonalComplementQuotientSectionsIso`: the sections of `ℱ|_{U_p}` over `W` are the sections
  of `ℱ` over `W`.
* `diagonalComplementSignCharacter`: the sign character of `S_n`, read on the universe-lifted
  symmetric group that acts on `W` over `U_p`.

## Main results

* `preservesInjectiveObjects_diagonalComplementQuotientRestriction`:
  **an injective abelian sheaf on `X` restricts to an injective abelian sheaf on `U_p`.**
* `diagonalComplementQuotientCharacterSectionsAddEquiv`:
  **`H⁰(W, ℱ|_{U_p})^{χ} = H⁰(W, ℱ)^{sign}`**, the two readings of the semi-invariant sections
  over `W`.

## References

* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The sign character of the symmetric group on `n` letters, read on the universe-lifted
group that acts on `W` in the spaces-étale site of the quotient `U_p = W/S_n`. -/
def diagonalComplementSignCharacter : ULift.{u} (Equiv.Perm (Fin n)) →* ℤˣ :=
  (Equiv.Perm.sign).comp (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom

/-- The sign character sends a lifted permutation `σ` to the sign of `σ.down`. -/
@[simp]
lemma diagonalComplementSignCharacter_apply (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    diagonalComplementSignCharacter n σ = Equiv.Perm.sign σ.down :=
  rfl

/-! ### The restriction functor -/

/-- **The restriction `ℱ ↦ ℱ|_{U_p}`** of an abelian sheaf on the spaces-étale site of `X` to
the spaces-étale site of the quotient `U_p = W/S_n`: restrict to the slice of the site of `X`
at `U_p`, then read the slice as the spaces-étale site of `U_p`. -/
def diagonalComplementQuotientRestriction :
    Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U n hsep))
        AddCommGrpCat.{u + 1} :=
  (topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep) ⋙
    (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).functor

/-- Reading the slice of the spaces-étale site of `X` at `U_p` as the spaces-étale site of
`U_p` is additive on abelian sheaves in the direction of restriction along `sliceToSmall`. -/
instance additive_sheafOverEquivSmall_inverse (V : SpacesEtale B S hS X) :
    (sheafOverEquivSmall B S hS V AddCommGrpCat.{u + 1}).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Reading an abelian sheaf on the spaces-étale site of `V` as a sheaf on the slice of the
spaces-étale site of `X` at `V` is additive. -/
instance additive_sheafOverEquivSmall_functor (V : SpacesEtale B S hS X) :
    (sheafOverEquivSmall B S hS V AddCommGrpCat.{u + 1}).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The restriction `ℱ ↦ ℱ|_{U_p}` is additive. -/
instance additive_diagonalComplementQuotientRestriction :
    (diagonalComplementQuotientRestriction B S hS X U n hsep).Additive := by
  unfold diagonalComplementQuotientRestriction
  exact Functor.instAdditiveComp
    ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep))
    (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).functor

/-- The restriction `ℱ ↦ ℱ|_{U_p}` is left exact. -/
instance preservesFiniteLimits_diagonalComplementQuotientRestriction :
    PreservesFiniteLimits (diagonalComplementQuotientRestriction B S hS X U n hsep) := by
  unfold diagonalComplementQuotientRestriction
  exact comp_preservesFiniteLimits
    ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep))
    (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).functor

/-- **Restriction to `U_p` is right exact.** Restriction to a localization is right exact by
[Stacks 04BD] and the second factor is an equivalence. -/
instance preservesFiniteColimits_diagonalComplementQuotientRestriction :
    PreservesFiniteColimits (diagonalComplementQuotientRestriction B S hS X U n hsep) :=
  have h : PreservesFiniteColimits ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep)) :=
    Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback _ _
  by
  unfold diagonalComplementQuotientRestriction
  exact comp_preservesFiniteColimits
    ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep))
    (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).functor

/-- **An injective abelian sheaf on `X` restricts to an injective abelian sheaf on `U_p`.**
Restriction to a localization preserves injectives, its left adjoint being the left exact
extension by zero of [Stacks 01DR], and the second factor is an equivalence. -/
instance preservesInjectiveObjects_diagonalComplementQuotientRestriction :
    (diagonalComplementQuotientRestriction B S hS X U n hsep).PreservesInjectiveObjects :=
  have hle : UnivLE.{u + 1, u + 1} := inferInstance
  have hsf : HasSheafify (topology B S hS X) AddCommGrpCat.{u + 1} := inferInstance
  have hsh : ∀ V : SpacesEtale B S hS X,
      HasSheafify ((topology B S hS X).over V) AddCommGrpCat.{u + 1} := fun _ => inferInstance
  have h : ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep)).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback
      (topology B S hS X) (diagonalComplementQuotientObject B S hS X U n hsep)
  by
  unfold diagonalComplementQuotientRestriction
  exact Functor.preservesInjectiveObjects_comp
    ((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep))
    (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).functor

/-! ### Sections over `W` -/

/-- **The sections of `ℱ|_{U_p}` over `W` are the sections of `ℱ` over `W`.** The object `W`
of the slice of the spaces-étale site of `X` at `U_p` is carried by
`AlgebraicGeometry.Space.SpacesEtale.sliceToSmall` to `W` as an object of the spaces-étale site
of `U_p`, so the unit of the equivalence of the two sites gives the comparison. -/
def diagonalComplementQuotientSectionsIso
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj.obj
        (op (diagonalComplementEtaleSource B S hS X U n hsep)) ≅
      F.obj.obj (op (diagonalComplement B S hS X U n hsep)) := by
  unfold diagonalComplementQuotientRestriction
  exact ((sheafToPresheaf ((topology B S hS X).over
        (diagonalComplementQuotientObject B S hS X U n hsep)) AddCommGrpCat.{u + 1}).mapIso
    ((sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).unitIso.app
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
          (diagonalComplementQuotientObject B S hS X U n hsep)).obj F)).symm).app
      (op (diagonalComplementSlice B S hS X U n hsep))

/-- The comparison of sections over `W` is natural in the sheaf. -/
theorem diagonalComplementQuotientSectionsIso_naturality
    {F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}} (k : F ⟶ F')
    (s : ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj.obj
      (op (diagonalComplementEtaleSource B S hS X U n hsep))) :
    (diagonalComplementQuotientSectionsIso B S hS X U n hsep F').hom
        (((diagonalComplementQuotientRestriction B S hS X U n hsep).map k).hom.app
          (op (diagonalComplementEtaleSource B S hS X U n hsep)) s) =
      k.hom.app (op (diagonalComplement B S hS X U n hsep))
        ((diagonalComplementQuotientSectionsIso B S hS X U n hsep F).hom s) := by
  unfold diagonalComplementQuotientRestriction at s ⊢
  have h := (sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).unitIso.symm.hom.naturality
    (((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
      (diagonalComplementQuotientObject B S hS X U n hsep)).map k)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app ((sheafToPresheaf _ _).congr_map h)
    (op (diagonalComplementSlice B S hS X U n hsep))) s

/-- The comparison of sections over `W` carries the action of the symmetric group on `W` over
`U_p` to its action on `W` over `X`. -/
theorem diagonalComplementQuotientSectionsIso_smul
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (σ : ULift.{u} (Equiv.Perm (Fin n)))
    (s : ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj.obj
      (op (diagonalComplementEtaleSource B S hS X U n hsep))) :
    (diagonalComplementQuotientSectionsIso B S hS X U n hsep F).hom
        (((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj.map
          ((diagonalComplementQuotientAut B S hS X U n hsep σ).asIso.hom).op s) =
      F.obj.map ((diagonalComplementAut B S hS X U n hsep σ.down).asIso.hom).op
        ((diagonalComplementQuotientSectionsIso B S hS X U n hsep F).hom s) := by
  rw [← sliceToSmall_map_diagonalComplementSliceAut B S hS X U n hsep σ]
  exact NatTrans.naturality_apply
    (((sheafOverEquivSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)
      AddCommGrpCat.{u + 1}).unitIso.symm.hom.app
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1}
          (diagonalComplementQuotientObject B S hS X U n hsep)).obj F)).hom)
    (diagonalComplementSliceAut B S hS X U n hsep σ).op s

/-- The comparison of sections over `W`, read backwards, carries the action of the symmetric
group on `W` over `X` to its action on `W` over `U_p`. -/
theorem diagonalComplementQuotientSectionsIso_inv_smul
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (σ : ULift.{u} (Equiv.Perm (Fin n)))
    (t : F.obj.obj (op (diagonalComplement B S hS X U n hsep))) :
    (diagonalComplementQuotientSectionsIso B S hS X U n hsep F).inv
        (F.obj.map ((diagonalComplementAut B S hS X U n hsep σ.down).asIso.hom).op t) =
      ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj.map
        ((diagonalComplementQuotientAut B S hS X U n hsep σ).asIso.hom).op
        ((diagonalComplementQuotientSectionsIso B S hS X U n hsep F).inv t) := by
  have h := diagonalComplementQuotientSectionsIso_smul B S hS X U n hsep F σ
    ((diagonalComplementQuotientSectionsIso B S hS X U n hsep F).inv t)
  rw [Iso.inv_hom_id_apply] at h
  rw [← h, Iso.hom_inv_id_apply]

/-- **`H⁰(W, ℱ|_{U_p})^{χ_p} = H⁰(W, ℱ)^{sign}`.** The sections of the restriction of `ℱ` to
`U_p` over `W` transforming according to the sign character of the group acting over `U_p` are
the `S_n`-anti-invariant sections of `ℱ` over `W`. -/
def diagonalComplementQuotientCharacterSectionsAddEquiv
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    CategoryTheory.characterSections (diagonalComplementEtaleSource B S hS X U n hsep)
        (diagonalComplementQuotientAut B S hS X U n hsep)
        (diagonalComplementSignCharacter n)
        ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F).obj ≃+
      CategoryTheory.characterSections (diagonalComplement B S hS X U n hsep)
        (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign F.obj where
  toFun s := ⟨(diagonalComplementQuotientSectionsIso B S hS X U n hsep F).hom s.1, by
    intro σ
    rw [← diagonalComplementQuotientSectionsIso_smul B S hS X U n hsep F (ULift.up σ),
      s.2 (ULift.up σ), map_zsmul]
    rfl⟩
  invFun t := ⟨(diagonalComplementQuotientSectionsIso B S hS X U n hsep F).inv t.1, by
    intro σ
    rw [← diagonalComplementQuotientSectionsIso_inv_smul B S hS X U n hsep F σ,
      t.2 σ.down, map_zsmul]
    rfl⟩
  left_inv s := Subtype.ext (Iso.hom_inv_id_apply _ _)
  right_inv t := Subtype.ext (Iso.inv_hom_id_apply _ _)
  map_add' s s' := Subtype.ext (map_add _ _ _)

end AlgebraicGeometry.Space.SpacesEtale

end
