module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeGeometricPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationFibreSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Base change for a proper direct image through the strict henselization

Let `f : X ⟶ S` be proper and `s` a geometric point of `S`, with strict henselization
`π : Spec(O^{sh}_{S,s}) ⟶ S` and canonical lift `s̃ : Spec Ω ⟶ Spec(O^{sh}_{S,s})` of `s`. Every
cartesian square of `f` over `s` is the paste of the base change of `f` to the strict henselization
and a cartesian square of the proper morphism `X ×_S Spec(O^{sh}_{S,s}) ⟶ Spec(O^{sh}_{S,s})` over
`s̃`, which lies over the closed point. The second has an invertible base change map
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_strictlyHenselian`). This file records
the consequence: base change for `f_*` holds for every cartesian square with `f` proper as soon as
the base change map of the strict-henselization square of every proper `f` becomes invertible after
inverse image along `s̃` — which is the identification of the stalk of `f_*` at `s` with the
sections over `X ×_S Spec(O^{sh}_{S,s})`, [Stacks, Tag 03Q9] in degree zero.

## Main results

* `Stacks.EtaleCohomology.geometricPointToStrictHenselization_eq` — the canonical lift factors
  through the closed point of the strict henselization.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselization` — the
  reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Lift

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

attribute [local instance] structureSheafStalkToGeometricField_isLocalHom

attribute [local instance] strictHenselizationResidueAlgebra

/-- **The canonical lift of a geometric point to the strict henselization lies over the closed
point**: it is `Spec Ω ⟶ Spec κ ⟶ Spec(O^{sh})`, the evaluation of étale germs factoring through
the residue field of the strictly henselian étale local ring. -/
theorem geometricPointToStrictHenselization_eq :
    geometricPointToStrictHenselization B S hS s =
      Spec.map (CommRingCat.ofHom (algebraMap
          (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField)) ≫
        residueFieldPoint ↥(etaleLocalRing B S hS s) := by
  refine Eq.trans ?_ (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS s)))) (CommRingCat.ofHom (algebraMap
      (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField)))
  refine congrArg Spec.map ?_
  ext a
  exact (congrArg (fun φ => φ a)
    (IsLocalRing.ResidueField.lift_comp_residue
      (structureSheafStalkToGeometricField B S hS s))).symm

/-- **Base change at the canonical lift of a geometric point to the strict henselization.** For
a proper `φ` over the strict henselization `Spec(O^{sh}_{S,s})`, the base change map of every
cartesian square of `φ` over the canonical lift `s̃` of `s` is an isomorphism: `s̃` lies over the
closed point of the strictly henselian local scheme. -/
theorem isIso_etaleAbelianBaseChange_geometricPointToStrictHenselization {A Z : Scheme.{u}}
    (φ : A ⟶ strictHenselization B S hS s) [IsProper φ] (p : Z ⟶ A) (q : Z ⟶ s.source)
    (sq : IsPullback p q φ (geometricPointToStrictHenselization B S hS s)) :
    IsIso (etaleAbelianBaseChange.{u, 0} φ (geometricPointToStrictHenselization B S hS s)
      p q sq.w) :=
  have := etaleLocalRing_strictHenselian B S hS s
  isIso_etaleAbelianBaseChange_of_strictlyHenselian_of_eq ↥(etaleLocalRing B S hS s) φ
    s.residueField p q _ (geometricPointToStrictHenselization_eq B S hS s) sq

end Lift

/-- **Base change at a geometric point, from the strict henselization.** Let `φ : A ⟶ S` be
proper and `s` a geometric point of `S`. If the base change map of the square of `φ` over the
strict henselization `π` becomes an isomorphism after inverse image along the canonical lift `s̃`,
then the base change map of every cartesian square of `φ` over `s` is an isomorphism. -/
theorem isIso_etaleAbelianBaseChange_geometricPoint_of_strictHenselization
    (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)
    {A Z : Scheme.{u}} (φ : A ⟶ S) [IsProper φ]
    (hsh : ∀ K : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso ((etaleAbelianInverseImage.{u, 0} (geometricPointToStrictHenselization B S hS s)).map
        ((etaleAbelianBaseChange.{u, 0} φ (strictHenselizationToBase B S hS s)
          (pullback.fst φ (strictHenselizationToBase B S hS s))
          (pullback.snd φ (strictHenselizationToBase B S hS s)) pullback.condition).app K)))
    (p : Z ⟶ A) (q : Z ⟶ s.source) (sqs : IsPullback p q φ s.hom) :
    IsIso (etaleAbelianBaseChange.{u, 0} φ s.hom p q sqs.w) := by
  have hx := geometricPointToStrictHenselization_comp B S hS s
  have hk : p ≫ φ = (q ≫ geometricPointToStrictHenselization B S hS s) ≫
      strictHenselizationToBase B S hS s := by
    rw [Category.assoc, hx]; exact sqs.w
  obtain ⟨k, hkfst, hksnd⟩ :=
    (IsPullback.of_hasPullback φ (strictHenselizationToBase B S hS s)).exists_lift p _ hk
  have sqs' : IsPullback (k ≫ pullback.fst φ (strictHenselizationToBase B S hS s)) q φ
      (geometricPointToStrictHenselization B S hS s ≫ strictHenselizationToBase B S hS s) := by
    rw [hkfst, hx]
    exact sqs
  have sqU : IsPullback k q (pullback.snd φ (strictHenselizationToBase B S hS s))
      (geometricPointToStrictHenselization B S hS s) :=
    IsPullback.of_right sqs' hksnd (IsPullback.of_hasPullback φ _)
  have hU := isIso_etaleAbelianBaseChange_geometricPointToStrictHenselization B S hS s
    (pullback.snd φ (strictHenselizationToBase B S hS s)) k q sqU
  exact isIso_etaleAbelianBaseChange_of_paste_of_isIso_inverseImage.{u, 0}
    (strictHenselizationToBase B S hS s) φ (pullback.snd φ _) (pullback.fst φ _)
    (geometricPointToStrictHenselization B S hS s) q k pullback.condition sqU.w s.hom hx.symm p
    hkfst.symm sqs.w hsh hU

/-- **Base change for a proper direct image, from the strict henselization.** Suppose that for
every proper `φ : A ⟶ S` and every geometric point `s` of `S`, the base change map of the square
of `φ` over the strict henselization `π : Spec(O^{sh}_{S,s}) ⟶ S` (taken in the big étale site
`BigEtaleSite.containing S`) becomes an isomorphism after inverse image along the canonical lift
`s̃` of `s`. Then the base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian étale sheaves is an
isomorphism for every cartesian square with `f` proper. -/
theorem isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselization
    (hsh : ∀ ⦃A S : Scheme.{u}⦄ (φ : A ⟶ S), IsProper φ → ∀ (s : GeometricPoint S)
      (K : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((etaleAbelianInverseImage.{u, 0} (geometricPointToStrictHenselization
          (BigEtaleSite.containing S) S (BigEtaleSite.contains_containing S) s)).map
        ((etaleAbelianBaseChange.{u, 0} φ (strictHenselizationToBase (BigEtaleSite.containing S) S
            (BigEtaleSite.contains_containing S) s)
          (pullback.fst φ (strictHenselizationToBase (BigEtaleSite.containing S) S
            (BigEtaleSite.contains_containing S) s))
          (pullback.snd φ (strictHenselizationToBase (BigEtaleSite.containing S) S
            (BigEtaleSite.contains_containing S) s)) pullback.condition).app K)))
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) :=
  isIso_etaleAbelianBaseChange_of_geometricPoints @IsProper
    (fun _ S _ φ hφ s p q sqs ↦
      have := hφ
      isIso_etaleAbelianBaseChange_geometricPoint_of_strictHenselization
        (BigEtaleSite.containing S) (BigEtaleSite.contains_containing S) s φ (hsh φ hφ s) p q sqs)
    f inferInstance g g' f' sq

end Stacks.EtaleCohomology

end
