module

public import StacksFrontier.AlgebraicGeometry.Etale.RefinedTorsionStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The refined torsion conditions move back along a finite direct image

Let `f : X ⟶ Y` be a finite morphism of schemes of a big étale site and let `F` be an abelian
sheaf on the small étale site of `X`. If `f_* F` satisfies one of the two refinements of the
torsion condition — being `l`-power torsion, or being torsion prime to `p` — then so does `F`.

This is the direction the proof of [Stacks, Tag 0A5D] needs and the one the source leaves
implicit: statements (3) and (6) of Situation 0A52 are conditional on a torsion condition on the
coefficient sheaf, so transferring them to `f_* F` requires reading the condition for `f_* F`
back on `F`.

The argument is the source's own. By [Stacks, Tag 03QP] part (1) the stalk of `f_* F` at a
geometric point `ȳ` of `Y` is the direct sum of the stalks of `F` over the geometric points of
`X` lying over `ȳ`, which is `AlgebraicGeometry.stalkPushforwardIsoDirectSum`. Every geometric
point of `X` is such a lift, of its own image; the coproduct injection at that lift is split, so
a stalk of `F` is a retract of a stalk of `f_* F`, and an annihilator of the latter annihilates
the former. The stalk criterion
`AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_iff_forall_etaleStalk` turns the resulting
stalkwise statement back into the condition on the sheaf.

The decomposition is stated on the size-bounded small étale site of [Stacks, Tag 021B], so the
transfer is proved there first and then carried to Mathlib's small étale site by
`AlgebraicGeometry.SmallEtale.isPrimePowerTorsion_toEtaleSite_iff` and its companion, using
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` to identify the restriction of
`f_* F` with the direct image of the restriction of `F`. The coefficient universe is `u + 1`,
`u` being the universe of the schemes, because that is where the decomposition lives.

## Main results

* `AlgebraicGeometry.isLocallyAnnihilatedBy_of_smallPushforward` — on the size-bounded small
  étale site, local annihilation by a prescribed set of integers passes from a finite direct
  image back to the sheaf.
* `AlgebraicGeometry.isPrimePowerTorsion_of_inclusionSmallEtaleDirectImageAb` and
  `AlgebraicGeometry.isPrimeToCharacteristicTorsion_of_inclusionSmallEtaleDirectImageAb` — the
  two refinements pass from `f_* F` back to `F` on Mathlib's small étale site, for a morphism of
  the underlying category of a big étale site.
* `Stacks.EtaleCohomology.isPrimePowerTorsion_of_smallEtaleDirectImageAb` and
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_smallEtaleDirectImageAb` — the same
  for an arbitrary finite morphism of schemes, the big étale site discharged. These are what the
  transfer of statements (3) and (6) of Situation 0A52 along a finite morphism needs.

## References

* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Torsion

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsFinite (B.inclusion.map f)]

section BoundedSite

/-- **The stalk of `F` at a geometric point is a retract of the stalk of `f_* F` at its image.**
The decomposition of [Stacks, Tag 03QP] part (1) has the stalk at the given point as one of its
summands, a geometric point of `X` being a lift of its own image, and a coproduct injection into
a family of abelian groups is split by the corresponding projection. -/
private theorem exists_mem_nsmul_eq_zero_etaleStalk_of_smallPushforward (N : Set ℕ)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsLocallyAnnihilatedBy (SmallEtale.topology B Y.1 Y.property) N
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).obj)
    (t : GeometricPoint X.1) (g : ↑(etaleStalk B X.1 X.property t F.obj)) :
    ∃ n ∈ N, n • g = 0 := by
  classical
  let y : GeometricPoint Y.1 := t.map (B.inclusion.map f)
  let x : GeometricLifts B f y := ⟨t.hom, rfl⟩
  let D : GeometricLifts B f y → AddCommGrpCat.{u + 1} := fun w =>
    etaleStalk B X.1 X.property (geometricPointLift (B.inclusion.map f) y w) F.obj
  let e : etaleStalk B Y.1 Y.property y
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).obj ≅ ∐ D :=
    stalkPushforwardIsoDirectSum B f y F
  have hid : (Limits.Sigma.ι D x ≫ e.inv) ≫ (e.hom ≫ Limits.Sigma.π D x) = 𝟙 (D x) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using Limits.Sigma.ι_π_eq_id D x
  exact exists_mem_nsmul_eq_zero_of_retraction (Limits.Sigma.ι D x ≫ e.inv)
    (e.hom ≫ Limits.Sigma.π D x) hid
    (SmallEtale.exists_mem_nsmul_eq_zero_etaleStalk.{u, u + 1} B Y.1 Y.property N y
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F) hF) g

/-- **Local annihilation by a prescribed set of integers passes back along a finite direct image
on the size-bounded small étale site.** Every geometric point of `X` is a lift of its image, so
every stalk of `F` is a retract of a stalk of `f_* F`; the stalk criterion does the rest. -/
public theorem isLocallyAnnihilatedBy_of_smallPushforward (N : Set ℕ)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsLocallyAnnihilatedBy (SmallEtale.topology B Y.1 Y.property) N
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).obj) :
    IsLocallyAnnihilatedBy (SmallEtale.topology B X.1 X.property) N F.obj :=
  SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk.{u, u + 1} B X.1 X.property N F
    (exists_mem_nsmul_eq_zero_etaleStalk_of_smallPushforward B f N F hF)

end BoundedSite

section EtaleSite

variable (F : Sheaf X.1.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **The restriction of `f_* F` to the size-bounded small étale site is the direct image there
of the restriction of `F`.** This is
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` evaluated at `F`. -/
private def restrictionSmallPushforwardIso :
    ((SmallEtale.toEtaleSite B Y.1 Y.property).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.1 Y.property)
          Y.1.smallEtaleTopology).obj
        ((Stacks.EtaleCohomology.smallEtaleDirectImageAb (B.inclusion.map f)).obj F) ≅
      (B.smallPushforward f AddCommGrpCat.{u + 1}).obj
        (((SmallEtale.toEtaleSite B X.1 X.property).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B X.1 X.property)
          X.1.smallEtaleTopology).obj F) :=
  (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).app F

/-- **`l`-power torsion passes back along a finite direct image.** If `f_* F` is `l`-power
torsion then so is `F`.

This is the transfer that the proof of [Stacks, Tag 0A5D] needs for statement (3) of
Situation 0A52. -/
public theorem isPrimePowerTorsion_of_inclusionSmallEtaleDirectImageAb (l : ℕ)
    (hF : IsPrimePowerTorsion Y.1.smallEtaleTopology l
      ((Stacks.EtaleCohomology.smallEtaleDirectImageAb (B.inclusion.map f)).obj F)) :
    IsPrimePowerTorsion X.1.smallEtaleTopology l F := by
  refine (SmallEtale.isPrimePowerTorsion_toEtaleSite_iff B X.1 X.property F l).1 ?_
  refine (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l _).2 ?_
  refine isLocallyAnnihilatedBy_of_smallPushforward B f (primePowerAnnihilators l) _ ?_
  refine (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l _).1 ?_
  exact IsPrimePowerTorsion.of_iso (restrictionSmallPushforwardIso B f F)
    ((SmallEtale.isPrimePowerTorsion_toEtaleSite_iff B Y.1 Y.property _ l).2 hF)

/-- **Torsion prime to `p` passes back along a finite direct image.** If `f_* F` is of torsion
prime to `p` then so is `F`.

This is the transfer that the proof of [Stacks, Tag 0A5D] needs for statement (6) of
Situation 0A52. -/
public theorem isPrimeToCharacteristicTorsion_of_inclusionSmallEtaleDirectImageAb (p : ℕ)
    (hF : IsPrimeToCharacteristicTorsion Y.1.smallEtaleTopology p
      ((Stacks.EtaleCohomology.smallEtaleDirectImageAb (B.inclusion.map f)).obj F)) :
    IsPrimeToCharacteristicTorsion X.1.smallEtaleTopology p F := by
  refine (SmallEtale.isPrimeToCharacteristicTorsion_toEtaleSite_iff B X.1 X.property F p).1 ?_
  refine (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p _).2 ?_
  refine isLocallyAnnihilatedBy_of_smallPushforward B f (coprimeAnnihilators p) _ ?_
  refine (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p _).1 ?_
  exact IsPrimeToCharacteristicTorsion.of_iso (restrictionSmallPushforwardIso B f F)
    ((SmallEtale.isPrimeToCharacteristicTorsion_toEtaleSite_iff B Y.1 Y.property _ p).2 hF)

end EtaleSite

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- A big étale site containing `X` and `Y` makes `f` a finite morphism of its underlying
category. -/
private theorem exists_bigEtaleSite_isFinite_homMk :
    ∃ (B : BigEtaleSite.{u}) (hX : B.Contains X) (hY : B.Contains Y),
      IsFinite (B.inclusion.map (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f)) := by
  have := small_single.{u} Y
  obtain ⟨B, hB⟩ :=
    BigEtaleSite.exists_contains_of_small ({X, Y} : Set AlgebraicGeometry.Scheme.{u})
  exact ⟨B, hB X (by simp), hB Y (by simp), ‹IsFinite f›⟩

/-- **`l`-power torsion passes back along a finite direct image of schemes.** If `f_* F` is
`l`-power torsion then so is `F`.

The big étale site is discharged as in
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback`: a big étale site containing
both schemes exists, `f` is a morphism of its underlying category, and the conclusion is about
the two schemes themselves. -/
public theorem isPrimePowerTorsion_of_smallEtaleDirectImageAb (l : ℕ)
    (hF : Stacks.Torsion.IsPrimePowerTorsion Y.smallEtaleTopology l
      ((smallEtaleDirectImageAb f).obj F)) :
    Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F := by
  obtain ⟨B, hX, hY, _⟩ := exists_bigEtaleSite_isFinite_homMk f
  exact AlgebraicGeometry.isPrimePowerTorsion_of_inclusionSmallEtaleDirectImageAb B
    (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f) F l hF

/-- **Torsion prime to `p` passes back along a finite direct image of schemes.** If `f_* F` is of
torsion prime to `p` then so is `F`. -/
public theorem isPrimeToCharacteristicTorsion_of_smallEtaleDirectImageAb (p : ℕ)
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology p
      ((smallEtaleDirectImageAb f).obj F)) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F := by
  obtain ⟨B, hX, hY, _⟩ := exists_bigEtaleSite_isFinite_homMk f
  exact AlgebraicGeometry.isPrimeToCharacteristicTorsion_of_inclusionSmallEtaleDirectImageAb B
    (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f) F p hF

end Stacks.EtaleCohomology

end
