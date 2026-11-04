module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceAlgebrasCanonical
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationCommRing
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpace
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the symmetric algebra of a module sheaf on a scheme

Let `X` be a scheme and `F` a quasi-coherent `𝒪_X`-module. Stacks Tag 01CL asserts that the
symmetric algebra `Sym(F) = ⨁_{n ≥ 0} Symⁿ F` is again quasi-coherent. The library proves this
for the canonical package of algebras of a ringed space,
`Stacks.SheafOfModules.isQuasicoherent_ringedSpaceSymmetricAlgebraSheaf`, while the symmetric
algebra a scheme-level consumer is handed is
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`, built as a degreewise sheafification. The
two are compared here by the universal property: a symmetric algebra of `F` is unique up to a
canonical isomorphism in every degree, so quasi-coherence transports.

The second half of the file identifies the sheaf of rings underlying the ungraded algebra sheaf
of a sheaf of graded algebras with the ungraded realization
`SheafOfModules.GradedAlgebra.ungradedSheaf`, which sheafifies the same direct sum in `RingCat`
rather than in `CommRingCat`, and then identifies the *module* underlying that algebra sheaf
with the coproduct of the homogeneous pieces. For `Sym(L)` that coproduct is quasi-coherent, so
the algebra sheaf of a line bundle is quasi-coherent and the total space of the line bundle is
the relative spectrum of `Sym(L)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.canonicalAlgebras`: the canonical package of tensor,
  exterior and symmetric algebras of `F`, read on the ringed space underlying `X`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceIso`: the degreewise comparison
  `Symⁿ F ≅ Symⁿ F` between the two symmetric algebras of `F`.
* `AlgebraicGeometry.Scheme.Modules.coprodSymmetricAlgebraIso`: the resulting comparison of the
  direct sums of the homogeneous pieces.
* `Stacks.RelativeSpec.ringSheafIsoUngradedSheaf`: **the sheaf of rings underlying the ungraded
  algebra sheaf of a sheaf of graded algebras is its ungraded realization.**
* `Stacks.RelativeSpec.ungradedRingUnit`: the sheafification unit of the ungraded realization,
  read as a morphism of presheaves of possibly noncommutative rings.
* `Stacks.RelativeSpec.coprodIsoUnderlyingModule`: **the module underlying the ungraded algebra
  sheaf of a sheaf of graded algebras concentrated in nonnegative degrees is the coproduct of
  its homogeneous pieces.**
* `Stacks.LineBundle.Situation.totalSpace`: **the total space of the line bundle**, with
  structure morphism `Stacks.LineBundle.Situation.totalSpaceToBase` to the scheme on which the
  line bundle lives.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece`: **every symmetric
  power of a quasi-coherent module sheaf on a scheme is quasi-coherent.**
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coprod_symmetricAlgebra`: **the direct sum
  of the homogeneous pieces of the symmetric algebra of a quasi-coherent module sheaf on a
  scheme is quasi-coherent.** This is the `isQuasicoherent` datum that
  `Stacks.ProjectiveBundle.Situation` and `Stacks.RelativeProj.Situation` ask for.
* `Stacks.LineBundle.Situation.isQuasicoherent_coprod_symmetricAlgebra`: the same for the
  symmetric algebra of a line bundle, whose underlying module is quasi-coherent because it is
  invertible.
* `Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf`: **an ungraded algebra sheaf whose
  homogeneous pieces are concentrated in nonnegative degrees and whose coproduct is
  quasi-coherent is quasi-coherent.**
* `Stacks.LineBundle.Situation.isQuasicoherent_algebraSheaf`: **the algebra sheaf of a line
  bundle is quasi-coherent**, which is the datum a relative spectrum requires.

## Implementation notes

The sheaf of rings of the ringed space underlying a scheme is the scheme's own `ringCatSheaf`
on the nose, both being `sheafCompose _ (forget₂ CommRingCat RingCat)` applied to the structure
sheaf, so the package of algebras of the ringed space is a package of algebras of `F` with no
transport. Instance search does not see this, because `structureSheafRing` is
not reducible: `isQuasicoherent_ringSheaf` restates the quasi-coherence hypothesis at the
ringed-space spelling, and is `inferInstanceAs`.

Degreewise quasi-coherence is read off the same covering family for every degree, which is the
content of `Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over`: the open over
which `F` is presented presents every symmetric power of `F`, so one application of
`SheafOfModules.IsQuasicoherent.of_coversTop` per degree suffices.

The comparison of the two sheafifications of the direct sum is `Stacks.ModuleUp`'s
`sheafifyForgetToRingIso`, which is `CategoryTheory.sheafComposeNatIso` for
`forget₂ CommRingCat RingCat`; the presheaf of rings underlying
`Stacks.RelativeSpec.ungradedCommPresheaf` is `Stacks.GradedAlgebra.totalPresheaf` on the nose,
so no comparison of presheaves is needed first.

Quasi-coherence of the algebra sheaf itself is a statement about `AlgebraSheaf.underlyingModule`,
whose scalar action is multiplication by the image of the structure map. That is exactly the
shape `Stacks.GradedAlgebra.directSumIsoUnderlyingModule` asks for, with the morphism `β` into
the sheafified ring taken to be the sheafification unit of `ungradedCommPresheaf` whiskered by
`forget₂ CommRingCat RingCat`: choosing `β` this way makes the compatibility with the structure
map hold by `rfl`, since both sides are the same whiskering of the same composite, and avoids
comparing `Stacks.ModuleUp.sheafifyForgetToRingIso` with a sheafification unit.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (F : X.Modules)

/-- The canonical package of tensor, exterior and symmetric algebras of a module sheaf on a
scheme, read on the ringed space underlying the scheme. -/
def canonicalAlgebras :
    SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.toRingedSpace.carrier) F :=
  SheafOfModules.ringedSpaceAlgebras X.toRingedSpace F


/-- **The symmetric algebra of a quasi-coherent module sheaf on a scheme is quasi-coherent**,
for the canonical package of algebras. -/
theorem isQuasicoherent_canonicalSymmetricAlgebraSheaf [F.IsQuasicoherent] :
    (canonicalAlgebras X F).symmetricAlgebraSheaf.IsQuasicoherent :=
  have := AlgebraicGeometry.isQuasicoherent_ringSheaf (X := X) F
  Stacks.SheafOfModules.isQuasicoherent_ringedSpaceSymmetricAlgebraSheaf F

/-- **Every symmetric power of a quasi-coherent module sheaf on a scheme is quasi-coherent**,
for the canonical package of algebras. -/
theorem isQuasicoherent_canonicalSymmetricPower [F.IsQuasicoherent] (n : ℕ) :
    ((canonicalAlgebras X F).symmetricPower n).IsQuasicoherent := by
  have := AlgebraicGeometry.isQuasicoherent_ringSheaf (X := X) F
  obtain ⟨c⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
    (M := (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
  have h : ∀ i, (((canonicalAlgebras X F).symmetricPower n).over (c.X i)).IsQuasicoherent :=
    fun i => (Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over (c.X i) F
      (canonicalAlgebras X F) (c.presentation i) n).some.isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((canonicalAlgebras X F).symmetricPower n) c.X c.coversTop

/-- **The two symmetric algebras of a module sheaf on a scheme agree in every degree**: the one
built by degreewise sheafification and the one in the canonical package of algebras are both
symmetric algebras of `F`, and a symmetric algebra is unique up to canonical isomorphism. -/
def symmetricAlgebraPieceIso (n : ℤ) :
    (symmetricAlgebra X F).piece n ≅ (canonicalAlgebras X F).symmetric.piece n :=
  (isSymmetricAlgebra_symmetricAlgebra X F).pieceIso
    (canonicalAlgebras X F).symmetric_isSymmetricAlgebra n

/-- The direct sums of the homogeneous pieces of the two symmetric algebras of a module sheaf on
a scheme agree. -/
def coprodSymmetricAlgebraIso :
    (∐ fun n : ℕ => (symmetricAlgebra X F).piece (n : ℤ)) ≅
      (canonicalAlgebras X F).symmetricAlgebraSheaf :=
  Sigma.mapIso fun n => symmetricAlgebraPieceIso X F (n : ℤ)

/-- **Every symmetric power of a quasi-coherent module sheaf on a scheme is quasi-coherent.**
This is the degreewise half of [Stacks, Tag 01CL], for `Sym(F)` in the shape a scheme-level
consumer receives it. -/
theorem isQuasicoherent_symmetricAlgebra_piece [F.IsQuasicoherent] (n : ℕ) :
    ((symmetricAlgebra X F).piece (n : ℤ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (symmetricAlgebraPieceIso X F (n : ℤ)).symm (isQuasicoherent_canonicalSymmetricPower X F n)

/-- **The direct sum of the homogeneous pieces of the symmetric algebra of a quasi-coherent
module sheaf on a scheme is quasi-coherent.** This is [Stacks, Tag 01CL] for `Sym(F)` in the
shape a scheme-level consumer receives it, and is the `isQuasicoherent` datum that a projective
bundle or a relative `Proj` over `X` requires. -/
theorem isQuasicoherent_coprod_symmetricAlgebra [F.IsQuasicoherent] :
    (∐ fun n : ℕ => (symmetricAlgebra X F).piece (n : ℤ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (coprodSymmetricAlgebraIso X F).symm (isQuasicoherent_canonicalSymmetricAlgebraSheaf X F)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- The presheaf of rings underlying the ungraded realization of a sheaf of graded algebras with
commuting homogeneous multiplication is the ungraded realization as a presheaf of rings. -/
theorem ungradedCommPresheaf_comp_forget₂ :
    ungradedCommPresheaf X A hA ⋙ forget₂ CommRingCat.{u} RingCat.{u} =
      A.toPresheafGradedAlgebra.totalPresheaf :=
  rfl

/-- **The sheaf of rings underlying the ungraded algebra sheaf of a sheaf of graded algebras is
its ungraded realization**: sheafification commutes with forgetting commutativity, so
sheafifying the direct sum of the homogeneous components in `CommRingCat` and sheafifying it in
`RingCat` give the same sheaf of rings. -/
def ringSheafIsoUngradedSheaf :
    A.ungradedSheaf ≅ AlgebraSheaf.ringSheaf (ungradedAlgebraSheaf X A hA) :=
  Stacks.ModuleUp.sheafifyForgetToRingIso (Opens.grothendieckTopology (X : TopCat))
    (ungradedCommPresheaf X A hA)

/-- The sheafification unit of the ungraded realization of a sheaf of graded algebras, read as a
morphism of presheaves of possibly noncommutative rings into the sections of the algebra
sheaf. -/
def ungradedRingUnit :
    A.toPresheafGradedAlgebra.totalPresheaf ⟶
      (AlgebraSheaf.ringSheaf (ungradedAlgebraSheaf X A hA)).obj :=
  Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat))
    (ungradedCommPresheaf X A hA)) (forget₂ CommRingCat.{u} RingCat.{u})

/-- The sheafification unit of the ungraded realization is compatible with the structure map of
the graded algebra and the structure morphism of the algebra sheaf. -/
theorem structureHom_comp_ungradedRingUnit :
    A.toPresheafGradedAlgebra.structureHom ≫ ungradedRingUnit X A hA =
      (AlgebraSheaf.structureMap (ungradedAlgebraSheaf X A hA)).hom :=
  rfl

/-- The sheafification unit of the ungraded realization is locally injective. -/
theorem isLocallyInjective_ungradedRingUnit :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (ungradedRingUnit X A hA) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (X : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat))
      (ungradedCommPresheaf X A hA)) x y h⟩

/-- The sheafification unit of the ungraded realization is locally surjective. -/
theorem isLocallySurjective_ungradedRingUnit :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (ungradedRingUnit X A hA) :=
  ⟨fun s => Presheaf.imageSieve_mem (Opens.grothendieckTopology (X : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat))
      (ungradedCommPresheaf X A hA)) s⟩

/-- The comparison morphism from the direct sum of the homogeneous components of a sheaf of
graded algebras to the module underlying its ungraded algebra sheaf. -/
def ungradedDirectSumHom :
    Stacks.directSum (fun n : ℤ => (A.piece n).val) ⟶
      (AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA)).val :=
  Stacks.GradedAlgebra.directSumHom A.toPresheafGradedAlgebra
    (AlgebraSheaf.structureMap (ungradedAlgebraSheaf X A hA)) (ungradedRingUnit X A hA)
    (structureHom_comp_ungradedRingUnit X A hA)

/-- **The module underlying the ungraded algebra sheaf of a sheaf of graded algebras is the
sheafification of the direct sum of the homogeneous components.** -/
def directSumIsoUnderlyingModule :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (Stacks.directSum fun n : ℤ => (A.piece n).val) ≅
      AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA) :=
  Stacks.GradedAlgebra.directSumIsoUnderlyingModule A.toPresheafGradedAlgebra
    (AlgebraSheaf.structureMap (ungradedAlgebraSheaf X A hA)) (ungradedRingUnit X A hA)
    (structureHom_comp_ungradedRingUnit X A hA) (isLocallyInjective_ungradedRingUnit X A hA)
    (isLocallySurjective_ungradedRingUnit X A hA)

/-- The comparison morphism of `Stacks.RelativeSpec.ungradedDirectSumHom`, restricted to the
direct sum over the nonnegative degrees. -/
def coprodDirectSumHom :
    Stacks.directSum (fun n : ℕ => (A.piece (n : ℤ)).val) ⟶
      (AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA)).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (A.piece n).val) ≫ ungradedDirectSumHom X A hA

/-- **The module underlying the ungraded algebra sheaf of a sheaf of graded algebras
concentrated in nonnegative degrees is the coproduct of its homogeneous pieces.** -/
def coprodIsoUnderlyingModule (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (∐ fun n : ℕ => A.piece (n : ℤ)) ≅
      AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA) :=
  (Stacks.sheafifyDirectSumIso (fun n : ℕ => A.piece (n : ℤ))).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective (coprodDirectSumHom X A hA)
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
          (isLocallyInjective_ungradedRingUnit X A hA)))
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
          (isLocallySurjective_ungradedRingUnit X A hA)))

/-- **An ungraded algebra sheaf whose homogeneous pieces are concentrated in nonnegative degrees
and whose coproduct is quasi-coherent is quasi-coherent.** This is the datum a relative spectrum
requires. -/
theorem isQuasicoherent_ungradedAlgebraSheaf (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
    (hqc : (∐ fun n : ℕ => A.piece (n : ℤ)).IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (ungradedAlgebraSheaf X A hA) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (coprodIsoUnderlyingModule X A hA hzero) hqc

end Stacks.RelativeSpec

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The sheaf of rings underlying the algebra sheaf of a line bundle is the ungraded
realization of `Sym(L)`.** -/
def Situation.ringSheafIsoUngradedSheaf :
    D.symmetricAlgebra.ungradedSheaf ≅
      Stacks.RelativeSpec.AlgebraSheaf.ringSheaf D.algebraSheaf :=
  Stacks.RelativeSpec.ringSheafIsoUngradedSheaf D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm

/-- **Every symmetric power of the line bundle of a situation is quasi-coherent.** -/
theorem Situation.isQuasicoherent_symmetricAlgebra_piece (n : ℕ) :
    (D.symmetricAlgebra.piece (n : ℤ)).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece D.X D.L n

/-- **The direct sum of the homogeneous pieces of `Sym(L)` is quasi-coherent**, for `L` the line
bundle of a situation. -/
theorem Situation.isQuasicoherent_coprod_symmetricAlgebra :
    (∐ fun n : ℕ => D.symmetricAlgebra.piece (n : ℤ)).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coprod_symmetricAlgebra D.X D.L

/-- **The module underlying the algebra sheaf of a line bundle is `⨁_{n ≥ 0} Symⁿ(L)`**: the
sheafified direct sum of the homogeneous pieces of `Sym(L)`. -/
def Situation.coprodIsoUnderlyingModule :
    (∐ fun n : ℕ => D.symmetricAlgebra.piece (n : ℤ)) ≅
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModule D.algebraSheaf :=
  Stacks.RelativeSpec.coprodIsoUnderlyingModule D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm D.isZero_symmetricAlgebra_piece

/-- **The algebra sheaf of a line bundle is quasi-coherent**, because its underlying module is
the direct sum of the homogeneous pieces of `Sym(L)`. -/
instance Situation.isQuasicoherent_algebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent D.algebraSheaf :=
  Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm D.isZero_symmetricAlgebra_piece
    D.isQuasicoherent_coprod_symmetricAlgebra

/-- The scheme on which the line bundle lives, together with the quasi-coherent sheaf of
algebras `Sym(L)`, as a relative-spectrum situation. -/
def Situation.relativeSpecSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} where
  base := D.X
  algebra := D.algebraSheaf

/-- **The total space of a line bundle**: the relative spectrum of `Sym(L)` over the scheme on
which `L` lives. -/
@[ega "II 8.9.3"]
def Situation.totalSpace : Scheme.{u} :=
  (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).scheme

/-- The structure morphism of the total space of a line bundle. -/
def Situation.totalSpaceToBase : D.totalSpace ⟶ D.X :=
  (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).toBase

end Stacks.LineBundle

end
