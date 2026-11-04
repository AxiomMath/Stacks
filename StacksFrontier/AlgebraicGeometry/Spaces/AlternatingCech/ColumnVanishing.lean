module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuotientSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistExt
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistLocalFreeness
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentToSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensorAbelianForget
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTwistQuasicoherent

/-!
# The columns of the `E₁`-page at quasi-coherent coefficients

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S` with
`U` representable.  The column `p` of the first page of the alternating Čech spectral sequence
of [Stacks, Tag 0728] is the cohomology `H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` of the quotient
`U_p = W_{p+1}/S_{p+1}` with coefficients twisted by the sign character
(`AlgebraicGeometry.Space.SpacesEtale.nonempty_zExtKoszulSignTwistAddEquiv`).  Since `W_{p+1}` is
an `S_{p+1}`-torsor over `U_p`, the twist `ℤ(χ_p)` is locally free of rank one
([Stacks, Tag 0727]), so twisting keeps quasi-coherent coefficients quasi-coherent
([Stacks, Tag 072A]).  Hence when `U_p` is affine and the coefficients are quasi-coherent, the
column vanishes in positive degrees.

## Main definitions

All declarations below are in the namespace `AlgebraicGeometry.Space.SpacesEtale`.

* `IsQuasicoherentAbelian`: the class of abelian sheaves on the spaces-étale site isomorphic to the
  underlying abelian sheaf of a quasi-coherent module on the ringed spaces-étale site.
* `AffineSerreVanishing`: the positive-degree vanishing of the cohomology of a quasi-coherent
  module on the spaces-étale site of an affine algebraic space — the clause of [Stacks, Tag 03DW]
  in positive degrees.

## Main results

* `IsQuasicoherentAbelian.of_iso`: the class is stable under isomorphism.
* `isQuasicoherentAbelian_characterTwistTensor`: the class is stable under twisting by a character
  whose twist is locally free of rank one, which is [Stacks, Tag 072A] on the spaces-étale site
  together with the identification of the underlying abelian sheaf of a module tensor with the
  abelian tensor.
* `isQuasicoherentAbelian_diagonalComplementQuotientRestriction` and
  `isQuasicoherentAbelian_diagonalComplementTwistedRestriction`: the coefficients carried to the
  spaces-étale site of `U_p`, and their sign twist, stay in the class.
* `isLocallyFreeOfRankOne_diagonalComplementCharacterTwist`: the twist `ℤ(χ)` on `U_p` is locally
  free of rank one.
* `isZero_zExt_koszulComplex_X_of_subsingleton_sheafH`: the column `p` vanishes in degree `q` when
  `H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` does.
* `isZero_zExt_koszulComplex_X_of_isAffineSpace_quotient`: the same in the `Abelian.zExt` spelling
  of the `E₁`-page.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

/-- An additive equivalence carries a subsingleton to a subsingleton. -/
theorem subsingleton_of_addEquiv {α β : Type*} [Add α] [Add β] (e : α ≃+ β)
    (h : Subsingleton β) : Subsingleton α :=
  e.toEquiv.subsingleton_congr.mpr h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The coefficient class**: the abelian sheaves on the spaces-étale site of
`Y` isomorphic to the underlying abelian sheaf of a quasi-coherent `𝒪_Y`-module. -/
def IsQuasicoherentAbelian (Y : AlgebraicSpaces B S hS)
    (F : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1}) : Prop :=
  ∃ M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS Y),
    M.IsQuasicoherentOnSite ∧
      Nonempty (F ≅ (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Y)).obj M)

/-- **The positive-degree vanishing on an affine algebraic space**: the cohomology of the
spaces-étale site of an affine algebraic space with coefficients in a quasi-coherent module
vanishes in positive degrees.  This is the clause of [Stacks, Tag 03DW] in positive degrees. -/
def AffineSerreVanishing : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS), IsAffineSpace B S hS Y.obj →
    ∀ M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS Y), M.IsQuasicoherentOnSite →
      ∀ q : ℕ, 0 < q →
        Subsingleton (Sheaf.H.{u + 1, u + 1}
          ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Y)).obj M) q)

/-- **The vanishing of cohomology transports along an isomorphism of coefficients.** -/
theorem subsingleton_sheafH_of_iso {Y : AlgebraicSpaces B S hS}
    {F F' : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1}} (i : F ≅ F') (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1, u + 1} F' q)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  have := h
  have key : ∀ z : Sheaf.H.{u + 1, u + 1} F q,
      Sheaf.H.map.{u + 1, u + 1} i.inv q (Sheaf.H.map.{u + 1, u + 1} i.hom q z) = z := by
    intro z
    rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y]
  exact congrArg _ (Subsingleton.elim _ _)

/-- The coefficient class is stable under isomorphism. -/
theorem IsQuasicoherentAbelian.of_iso {Y : AlgebraicSpaces B S hS}
    {F F' : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1}}
    (hF : IsQuasicoherentAbelian B S hS Y F) (e : F' ≅ F) :
    IsQuasicoherentAbelian B S hS Y F' := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := hF
  exact ⟨M, hM, ⟨e.trans eM⟩⟩

/-- **The coefficient class is stable under twisting by a character.**  If the twist `ℤ(χ)` of an
object `W` of the spaces-étale site of `Y` by a character `χ` is locally free of rank one, then
the twist `ℱ ⊗_ℤ ℤ(χ)` of a coefficient sheaf in the class is again in the class. -/
theorem isQuasicoherentAbelian_characterTwistTensor (Y : AlgebraicSpaces B S hS)
    {G : Type w} [Group G] (W : SpacesEtale B S hS Y) (act : G →* Aut W) (χ : G →* ℤˣ)
    (F : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS Y F)
    (hL : IsLocallyFreeOfRankOne B S hS Y
      (characterTwist W act χ (topology B S hS Y))) :
    IsQuasicoherentAbelian B S hS Y
      (characterTwistTensor F.obj act χ (topology B S hS Y)) := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := hF
  refine ⟨Stacks.SheafOfModules.tensorAbelianModule M
      (characterTwist W act χ (topology B S hS Y)).obj,
    isQuasicoherentOnSite_tensorAbelianModule B S hS Y _ hL M hM, ⟨?_⟩⟩
  exact ((characterTwistFunctor W act χ (topology B S hS Y)).mapIso eM).trans
    (Stacks.SheafOfModules.toSheafTensorAbelianModuleCharacterTwistIso M act χ).symm

variable (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The coefficients restricted to the quotient `U_p` stay in the class**: restriction to the
spaces-étale site of an object of the spaces-étale site of `X` carries the underlying abelian
sheaf of a quasi-coherent module to that of a quasi-coherent module. -/
theorem isQuasicoherentAbelian_diagonalComplementQuotientRestriction (n : ℕ)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS X F) :
    IsQuasicoherentAbelian B S hS (diagonalComplementQuotient B S hS X U n hsep)
      ((diagonalComplementQuotientRestriction B S hS X U n hsep).obj F) := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := hF
  obtain ⟨M', hM', ⟨eM'⟩⟩ := exists_isQuasicoherentOnSite_toSheaf_iso B S hS X
    (diagonalComplementQuotientObject B S hS X U n hsep) M hM
  exact ⟨M', hM', ⟨(diagonalComplementQuotientRestriction B S hS X U n hsep).mapIso eM ≪≫ eM'⟩⟩

/-- **The twist `ℤ(χ)` on the quotient `U_p` is locally free of rank one**, for every character
`χ` of the symmetric group. -/
theorem isLocallyFreeOfRankOne_diagonalComplementCharacterTwist (n : ℕ)
    (χ : ULift.{u} (Equiv.Perm (Fin n)) →* ℤˣ) :
    IsLocallyFreeOfRankOne B S hS (diagonalComplementQuotient B S hS X U n hsep)
      (characterTwist (diagonalComplementEtaleSource B S hS X U n hsep)
        (diagonalComplementQuotientAut B S hS X U n hsep) χ
        (topology B S hS (diagonalComplementQuotient B S hS X U n hsep))) :=
  ⟨finalHypercover B S hS
      (fun _ : PUnit.{u + 2} => diagonalComplementEtaleSource B S hS X U n hsep),
    fun x => by
      obtain ⟨y, hy⟩ := isSurjective_toOrbitQuotient
        (isNaturalAction_diagonalComplement B S hS X U n hsep)
        (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
        (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep) x
      exact ⟨PUnit.unit, y, hy⟩,
    fun _ => ⟨(characterTwistOverIso (isTorsorObject_diagonalComplement B S hS X U n hsep)
      χ).symm⟩⟩

/-- **The twisted coefficients `ℱ|_{U_p} ⊗_ℤ ℤ(χ_p)` stay in the class**. -/
theorem isQuasicoherentAbelian_diagonalComplementTwistedRestriction (p : ℕ)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS X F) :
    IsQuasicoherentAbelian B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep)
      (diagonalComplementTwistedRestriction B S hS X U hsep p F) :=
  isQuasicoherentAbelian_characterTwistTensor B S hS _
    (diagonalComplementEtaleSource B S hS X U (p + 1) hsep)
    (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)
    (diagonalComplementSignCharacter (p + 1)) _
    (isQuasicoherentAbelian_diagonalComplementQuotientRestriction B S hS X U hsep (p + 1) F hF)
    (isLocallyFreeOfRankOne_diagonalComplementCharacterTwist B S hS X U hsep (p + 1) _)

/-- **The column `p` of the `E₁`-page of [Stacks, Tag 0728] vanishes in degree `q` when the
cohomology `H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` does**. -/
theorem isZero_zExt_koszulComplex_X_of_subsingleton_sheafH (p q : ℕ)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (h : Subsingleton (Sheaf.H.{u + 1, u + 1}
      (diagonalComplementTwistedRestriction B S hS X U hsep p F) q)) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X p) F (q : ℤ))) := by
  obtain ⟨g⟩ := nonempty_zExtKoszulSignTwistAddEquiv B S hS X U hsep p q F
  have hH : Subsingleton (Sheaf.H.{u + 2, u + 1}
      (diagonalComplementTwistedRestriction B S hS X U hsep p F) q) :=
    subsingleton_of_addEquiv
      Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{u + 2, u + 1} h
  have hz : Subsingleton (Abelian.zExt
      (constantIntSheaf B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
      (diagonalComplementTwistedRestriction B S hS X U hsep p F) (q : ℤ)) :=
    subsingleton_of_addEquiv
      (sheafHIsoZExt B S hS _ (diagonalComplementTwistedRestriction B S hS X U hsep p F)
        q).addCommGroupIsoToAddEquiv.symm hH
  have : Subsingleton (Abelian.zExt ((koszulComplex B S hS X U).X p) F (q : ℤ)) :=
    subsingleton_of_addEquiv g hz
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **The column `p` of the `E₁`-page of [Stacks, Tag 0728] vanishes in positive degrees when the
quotient `U_p` is affine and the coefficients are quasi-coherent.** -/
theorem isZero_zExt_koszulComplex_X_of_isAffineSpace_quotient
    (hSerre : AffineSerreVanishing B S hS) (p : ℕ)
    (haff : IsAffineSpace B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep).obj)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS X F) (q : ℕ) (hq : 0 < q) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X p) F (q : ℤ))) := by
  obtain ⟨N, hN, ⟨eN⟩⟩ :=
    isQuasicoherentAbelian_diagonalComplementTwistedRestriction B S hS X U hsep p F hF
  exact isZero_zExt_koszulComplex_X_of_subsingleton_sheafH B S hS X U hsep p q F
    (subsingleton_sheafH_of_iso B S hS eN q
      (hSerre (diagonalComplementQuotient B S hS X U (p + 1) hsep) haff N hN q hq))

end AlgebraicGeometry.Space.SpacesEtale

end
