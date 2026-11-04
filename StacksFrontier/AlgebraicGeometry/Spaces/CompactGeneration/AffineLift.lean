module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.EtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.KoszulDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.ExcisionGluing
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallTransport

/-!
# Lifting compact objects from an open of an affine algebraic space

Let `j : Y ⟶ X` be an open immersion (an étale monomorphism) of algebraic spaces, quasi-compact
and quasi-separated, with `X` affine, and let `l` be a list of global functions on `X` such that
the charts of `X` on which some member of `l` is a unit lie in `Y`, while the Koszul object
`K(l)` restricts to zero on `Y`. This is the situation of a quasi-compact open `Y` of an affine
`X` and generators of the ideal of its complement.

Then the restriction `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` is a Verdier localization whose kernel is
detected by `K(l)`, and every compact object `E` of `D_QCoh(𝒪_Y)` has `E ⊕ E[1]` isomorphic to
the restriction of a compact object of `D_QCoh(𝒪_X)`. This is the form of
[Stacks, Tag 08EK] (Thomason–Trobaugh, Neeman) used in the proof of [Stacks, Tag 09IY].

## Main results

* `AlgebraicGeometry.Space.isZero_of_hom_koszul_shift_eq_zero_of_isZero_restrict`: an object of
  `D_QCoh(𝒪_X)` restricting to zero on `Y` and right orthogonal to the shifts of `K(l)` is zero.
* `AlgebraicGeometry.Space.exists_isCompactObject_restrict_iso_biprod_shift`: the lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **Vanishing where a function is a unit, from vanishing on an open.** Let `j : Y ⟶ X` be étale
and `l` a list of global functions on `X` such that every chart of `X` on which some member of `l`
is a unit is, up to isomorphism, a chart of `Y`. An object of `D(𝒪_X)` restricting to zero on `Y`
vanishes where any member of `l` is a unit. -/
theorem vanishesWhereUnit_of_isZero_restrict (j : Y ⟶ X) (hj : IsEtale B S hS j.hom)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hl : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      ∃ U' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS j hj).obj U' ≅ U))
    (N : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hNY : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj N)) :
    ∀ a ∈ l, VanishesWhereUnit a N := fun a ha U hU q => by
  obtain ⟨U', ⟨e⟩⟩ := hl U ⟨a, ha, hU⟩
  have hH : IsZero ((etaleModulePullback.{u, u} B S hS j hj).obj
      ((DerivedCategory.homologyFunctor _ q).obj N)) :=
    ((DerivedCategory.homologyFunctor _ q).map_isZero hNY).of_iso
      (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app N).symm
  have : Subsingleton (((etaleModulePullback.{u, u} B S hS j hj).obj
      ((DerivedCategory.homologyFunctor _ q).obj N)).val.obj (op U')) :=
    ModuleCat.subsingleton_of_isZero ((SheafOfModules.evaluation _ (op U')).map_isZero hH)
  let φ := (((DerivedCategory.homologyFunctor _ q).obj N).val.presheaf.mapIso e.op
    ).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => φ.injective (this.elim (φ a) (φ b))⟩

/-- **Koszul detection relative to an open.** Let `X` have a final affine chart, `j : Y ⟶ X` be
étale and `l` a list of global functions on `X` such that every chart of `X` on which some
member of `l` is a unit is, up to isomorphism, a chart of `Y`. An object of `D_QCoh(𝒪_X)`
restricting to zero on `Y` and right orthogonal to the shifts of `K(l)` is zero. -/
theorem isZero_of_hom_koszul_shift_eq_zero_of_isZero_restrict (T : SmallEtale B S hS X.1)
    (hT : IsTerminal T) (hTa : IsAffineChart B S hS X.1 T) (j : Y ⟶ X)
    (hj : IsEtale B S hS j.hom)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hl : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      ∃ U' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS j hj).obj U' ≅ U))
    (N : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hN : QcohDerived B S hS X N)
    (hNY : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj N))
    (horth : ∀ (n : ℤ) (x : (koszul X.2 l)⟦n⟧ ⟶ N), x = 0) : IsZero N := by
  refine isZero_of_hom_koszul_eq_zero T hT hTa l N hN
    (vanishesWhereUnit_of_isZero_restrict j hj l hl N hNY) fun n x => ?_
  have h1 := horth (-n) ((shiftFunctor _ (-n)).map x ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app N)
  have h2 : (shiftFunctor _ (-n)).map x = 0 := by
    simpa using congrArg (· ≫ (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).inv.app N) h1
  exact (shiftFunctor _ (-n)).map_injective (h2.trans (Functor.map_zero _ _ _).symm)

/-- **Koszul detection relative to an open, on `D_QCoh`.** In the setting of
`AlgebraicGeometry.Space.isZero_of_hom_koszul_shift_eq_zero_of_isZero_restrict`, an object of
`D_QCoh(𝒪_X)` restricting to zero on `Y` and right orthogonal to the shifts of `K(l)` in
`D_QCoh(𝒪_X)` is zero. -/
theorem isZero_of_hom_koszulQuasicoherent_shift_eq_zero_of_isZero_restrict
    (T : SmallEtale B S hS X.1)
    (hT : IsTerminal T) (hTa : IsAffineChart B S hS X.1 T) (j : Y ⟶ X)
    (hj : IsEtale B S hS j.hom)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hl : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      ∃ U' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS j hj).obj U' ≅ U))
    (N : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hN : IsZero ((quasicoherentDerivedEtalePullback B S hS j hj).obj N))
    (horth : ∀ (n : ℤ) (x : (koszulQuasicoherent X.2 l)⟦n⟧ ⟶ N), x = 0) : IsZero N := by
  let ιX := (QcohDerived B S hS X).ι
  refine IsZero.of_full_of_faithful_of_isZero ιX N
    (isZero_of_hom_koszul_shift_eq_zero_of_isZero_restrict T hT hTa j hj l hl N.obj N.property
      ((QcohDerived B S hS Y).ι.map_isZero hN) fun n x => ?_)
  have h0 := horth n (ιX.preimage ((ιX.commShiftIso n).hom.app _ ≫ x))
  have h1 : (ιX.commShiftIso n).hom.app (koszulQuasicoherent X.2 l) ≫ x = 0 := by
    simpa using congrArg ιX.map h0
  exact (cancel_epi ((ιX.commShiftIso n).hom.app _)).1 (h1.trans comp_zero.symm)

/-- **A sheaf of modules with no nonzero sections on the members of covering sieves is zero.** -/
theorem isZero_of_forall_exists_sieve (Z : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS Z.1 Z.2)
    (h : ∀ U : SmallEtale B S hS Z.1, ∃ R ∈ SmallEtale.topology B S hS Z.1 U,
      ∀ ⦃Y : SmallEtale B S hS Z.1⦄ (g : Y ⟶ U), R g → Subsingleton (F.val.obj (op Y))) :
    IsZero F := by
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS Z.1)
      (F.val.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ F.isSheaf
  have hsub : ∀ U : SmallEtale B S hS Z.1, Subsingleton (F.val.obj (op U)) := by
    intro U
    obtain ⟨R, hR, hRs⟩ := h U
    exact ⟨fun s t => (hsheaf R hR).isSeparatedFor.ext fun Y g hg => (hRs g hg).elim _ _⟩
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (hsub U.unop).elim _ _

/-- **Lifting compact objects from an open of an affine algebraic space** ([Stacks, Tag 08EK] in
the form used for [Stacks, Tag 09IY]). Let `X` have a final affine chart, `j : Y ⟶ X` be an
étale monomorphism which is quasi-compact and quasi-separated, and `l` a list of global functions
on `X` such that the charts of `X` on which some member of `l` is a unit are charts of `Y`, and
such that the Koszul object `K(l)` restricts to zero on `Y`. Then for every compact object `E` of
`D_QCoh(𝒪_Y)` there is a compact object `c` of `D_QCoh(𝒪_X)` with `c|_Y ≅ E ⊕ E[1]`. -/
theorem exists_isCompactObject_restrict_iso_biprod_shift (T : SmallEtale B S hS X.1)
    (hT : IsTerminal T) (hTa : IsAffineChart B S hS X.1 T) (j : Y ⟶ X)
    (hj : IsEtale B S hS j.hom) [Mono j] (hjqc : IsQuasiCompact B S hS j.hom)
    (hjqs : IsQuasiSeparated B S hS j.hom)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (hl : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      ∃ U' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS j hj).obj U' ≅ U))
    (hlK : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
      (koszul X.2 l)))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (hE : IsCompactObject.{u} E) :
    ∃ c : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsCompactObject.{u} c ∧
      Nonempty ((quasicoherentDerivedEtalePullback B S hS j hj).obj c ≅ E ⊞ E⟦(1 : ℤ)⟧) := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := isGrothendieckAbelian_modules_ringUniverse B S hS Y.1 Y.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS Y.1 Y.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS Y.1 Y.2
  have := fun J : Type u =>
    preservesCoproducts_quasicoherentDerivedPushforward B S hS j hjqc hjqs J
  let adj := quasicoherentDerivedEtaleAdjunction B S hS j hj hjqc hjqs
  let K := koszulQuasicoherent X.2 l
  have hLK : IsZero ((quasicoherentDerivedEtalePullback B S hS j hj).obj K) :=
    IsZero.of_full_of_faithful_of_isZero (QcohDerived B S hS Y).ι _ hlK
  have hG₀ : (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => unitQuasicoherent X.2)
      ).IsWeakTriangulatedGenerator := by
    have : ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => unitQuasicoherent X.2) =
        ObjectProperty.singleton (unitQuasicoherent X.2) := by
      ext Z
      rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩
    rw [this]
    exact isWeakTriangulatedGenerator_unitQuasicoherent T hT hTa
  exact exists_isCompactObject_iso_biprod_shift_of_locallySmall adj (fun _ : PUnit.{u + 1} => K)
    (fun _ => isCompactObject_koszulQuasicoherent T hT hTa l) (fun _ => hLK)
    (fun N hN => isIso_unit_of_rightOrthogonal adj K hLK
      (isZero_of_hom_koszulQuasicoherent_shift_eq_zero_of_isZero_restrict T hT hTa j hj l hl) N
      (hN PUnit.unit))
    (fun _ : PUnit.{u + 1} => unitQuasicoherent X.2)
    (fun _ => isCompactObject_unitQuasicoherent T hT hTa) hG₀ E hE

end AlgebraicGeometry.Space

end
