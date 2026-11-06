module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.RingTheory.SymmetricAlgebra.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSheafifyModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSmallSections

/-!
# The sections of the symmetric algebra of a quasi-coherent module over an affine étale chart

Let `W` be an algebraic space and `𝒢` a quasi-coherent `𝒪_W`-module on its small étale site.
`AlgebraicGeometry.Space.symmetricAlgebra` is the degreewise sheafification of the presheaf
`V ↦ Symⁿ_{𝒪_W(V)}(𝒢(V))`.  This file proves that **over every affine étale chart `V` the
sheafification changes nothing**: the sections of `Symⁿ(𝒢)` over `V` are
`Symⁿ_{𝒪_W(V)}(𝒢(V))`.

## The argument

The comparison is general: a presheaf of `𝒪_W`-modules (at the universe of the schemes) which is
*cartesian* between affine charts — its restriction maps exhibit the sections over a smaller
affine chart as the base change of those over a larger one — has a sheafification unit which is
bijective over every affine chart
(`AlgebraicGeometry.Space.bijective_sheafificationUnit_app_of_isAffine_of_cartesian`).  Indeed
its restriction to the affine étale site is a sheaf by flat descent
(`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_covers'`), the affine charts form a dense
subsite (Stacks 04JS), and sheafification does not change a presheaf over a dense subsite on
which it is already a sheaf (`CategoryTheory.Presheaf.isIso_toSheafify_app_of_isDenseSubsite`).

The presheaf of sectionwise symmetric powers of `𝒢` is cartesian between affine charts because
`𝒢` is (Stacks 03DX) and the formation of `Symⁿ` commutes with base change
(`Stacks.PresheafOfModules.isIso_restrictionBaseChange_symPowInt`).

## Main results

* `AlgebraicGeometry.Space.bijective_sheafificationUnit_app_of_isAffine_of_cartesian`.
* `AlgebraicGeometry.Space.bijective_symmetricAlgebra_sheafifyUnit_of_isAffine`.

## Implementation notes

Everything is at the universe `u` of the schemes, which is where `Sym(𝒢)` lives.  The existing
`AlgebraicGeometry.Space.isIso_sheafificationUnit_app_of_isAffine` is stated at the module
universe `max (u + 1) z`, which is never `u`, so it is not used; the flat descent statement used
is the one with sections in `Type (max m r)` for the chart rings at the universe `u`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules DirectSum

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf of modules over the chart rings of the affine étale site which is cartesian over
every morphism is a sheaf, with its sections at the universe of the schemes. -/
theorem isSheaf_of_cartesian_affineEtaleChart_small (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (M : PresheafOfModules.{u}
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (AffineEtale B S hS F)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, u} M f)) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf := by
  refine isSheaf_of_cartesian_of_flat_covers'.{u, u + 1, u, u, u, u + 1}
    (AffineEtale.toScheme B S hS F) (affineEtaleChartRings B S hS F) ?_ ?_ M hM
    (AffineEtale.precoverage B S hS F) ?_
  · intro U E _ hE
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS F))).mp hE
    exact faithfullyFlat_pi_affineEtaleChartRings B S hS F E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineEtaleChartRings B S hS F h
  · intro U P hP
    obtain ⟨E, rfl, hE⟩ := hP
    refine ⟨E, rfl, hE.2, ?_⟩
    obtain ⟨hs, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS F))).mp hE.1.2
    exact (Scheme.presieve₀_mem_precoverage_iff _).mpr
      ⟨hs, fun i => by have := het i; infer_instance⟩

/-- **Sheafification of a presheaf of `𝒪_W`-modules which is cartesian between affine charts does
not change its sections over an affine chart.**  Universe-`u` form: the sections of the presheaf
live in the universe of the schemes. -/
theorem bijective_sheafificationUnit_app_of_isAffine_of_cartesian (W : AlgebraicSpaces B S hS)
    (P : PresheafOfModules.{u} (structureRingSheaf B S hS W).obj)
    (hP : ∀ (U V : SmallEtale B S hS W.1),
      IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
      ∀ g : V ⟶ U, IsIso (restrictionBaseChange.{u + 1, u, u, u}
        (R := structurePresheaf B S hS W.1) P g.op))
    (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app P).app (op U)) := by
  have hsh : Presheaf.IsSheaf (AffineEtale.topology B S hS W.1)
      ((AffineEtale.inclusion B S hS W.1).op ⋙ P.presheaf) :=
    isSheaf_of_cartesian_affineEtaleChart_small B S hS W.1
      ((PresheafOfModules.pushforward₀ (AffineEtale.inclusion B S hS W.1)
        (structurePresheaf B S hS W.1 ⋙ forget₂ CommRingCat RingCat)).obj P)
      fun {X Y} f => hP _ _ X.unop.property Y.unop.property
        ((AffineEtale.inclusion B S hS W.1).map f.unop)
  obtain ⟨_, _⟩ := AffineEtale.inclusion_isSpecialCocontinuous B S hS W.1 W.2
  have : IsIso ((toSheafify (SmallEtale.topology B S hS W.1) P.presheaf).app
      (op ((AffineEtale.inclusion B S hS W.1).obj ⟨U, hU⟩))) :=
    Presheaf.isIso_toSheafify_app_of_isDenseSubsite _ _ _ P.presheaf hsh ⟨U, hU⟩
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify (SmallEtale.topology B S hS W.1) P.presheaf).app
      (op ((AffineEtale.inclusion B S hS W.1).obj ⟨U, hU⟩)))

/-- The underlying presheaf of a quasi-coherent `𝒪_W`-module is cartesian between affine
charts, in the form of `Stacks.PresheafOfModules.restrictionBaseChange`. -/
theorem isIso_restrictionBaseChange_val_of_isQuasicoherentOnSite (W : AlgebraicSpaces B S hS)
    (G : SheafOfModules.{u} (structureRingSheaf B S hS W)) (hG : G.IsQuasicoherentOnSite)
    (U V : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (g : V ⟶ U) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS W.1) G.val g.op) :=
  (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS W.1 W.2 G g).1
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS W.1 W.2 G hG U V hU hV g)

/-- **The sections of `Symⁿ(𝒢)` over an affine étale chart are `Symⁿ` of the sections of `𝒢`**,
for `𝒢` quasi-coherent: the sheafification unit of the presheaf of sectionwise symmetric powers
is bijective over every affine chart.  Its target is the degree-`n` piece of
`AlgebraicGeometry.Space.symmetricAlgebra` by definition. -/
theorem bijective_symmetricAlgebra_sheafifyUnit_of_isAffine (W : AlgebraicSpaces B S hS)
    (G : SheafOfModules.{u} (structureRingSheaf B S hS W)) (hG : G.IsQuasicoherentOnSite)
    (n : ℤ) (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app
          (PresheafOfModules.symPowInt n G.val)).app (op U)) :=
  bijective_sheafificationUnit_app_of_isAffine_of_cartesian B S hS W _
    (fun U V hU hV g =>
      have := isIso_restrictionBaseChange_val_of_isQuasicoherentOnSite B S hS W G hG U V hU hV g
      isIso_restrictionBaseChange_symPowInt (O := structurePresheaf B S hS W.1) n G.val g.op)
    U hU

/-! ### The ungraded realization over an affine chart -/

section Ungraded

variable (W : AlgebraicSpaces B S hS)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W))

/-- The sheafification unit of the ungraded realization of a sheaf of graded algebras on the small
étale site is locally injective. -/
theorem isLocallyInjective_toTotalSheaf_smallEtale :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1)
      (A.toPresheafGradedAlgebra.toTotalSheaf (SmallEtale.topology B S hS W.1)) :=
  ((SmallEtale.topology B S hS W.1).W_toSheafify
    A.toPresheafGradedAlgebra.totalPresheaf).isLocallyInjective

/-- The sheafification unit of the ungraded realization of a sheaf of graded algebras on the small
étale site is locally surjective. -/
theorem isLocallySurjective_toTotalSheaf_smallEtale :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1)
      (A.toPresheafGradedAlgebra.toTotalSheaf (SmallEtale.topology B S hS W.1)) :=
  ((SmallEtale.topology B S hS W.1).W_toSheafify
    A.toPresheafGradedAlgebra.totalPresheaf).isLocallySurjective

/-- **The sections of the ungraded realization of a sheaf of graded algebras over an affine
étale chart are the direct sum of the sections of its homogeneous pieces**: the sheafification
unit of the ungraded realization is bijective there, an affine chart being a quasi-compact object
of the small étale site. -/
theorem bijective_totalUnit_of_isAffine (V : SmallEtale B S hS W.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Bijective (A.toPresheafGradedAlgebra.totalUnit
      (SmallEtale.topology B S hS W.1) (op V)) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 (structureRingSheaf B S hS W).obj)
      ((SheafOfModules.restrictScalars.{u} A.ungradedStructureMap).obj
        (SheafOfModules.unit A.ungradedSheaf))
      (A.toPresheafGradedAlgebra.directSumHom A.ungradedStructureMap
        (A.toPresheafGradedAlgebra.toTotalSheaf _) rfl)
      (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallyInjective_toTotalSheaf_smallEtale B S hS W A))
      (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallySurjective_toTotalSheaf_smallEtale B S hS W A))
      (op V)).1
    (Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app (fun n : ℤ => A.piece n) V
      (isQuasiCompactObject_of_isAffine B S hS W.1 V hV))

end Ungraded

/-! ### The ring of sections of `Sym(𝒢)` over an affine chart -/

/-- `Sym(𝒢)` has no nonzero local section in a negative degree. -/
theorem subsingleton_symmetricAlgebra_piece_of_neg (W : AlgebraicSpaces B S hS)
    (G : SheafOfModules.{u} (structureRingSheaf B S hS W)) (n : ℤ) (hn : n < 0)
    (V : (SmallEtale B S hS W.1)ᵒᵖ) :
    Subsingleton (((symmetricAlgebra B S hS W G).piece n).val.obj V) :=
  have hz := @PresheafOfModules.symmetricAlgebraSheafify_piece_eq_zero.{u, u + 1, u, u} _ _
    (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
    (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) G.val
    n hn V
  ⟨fun x y => (hz x).trans (hz y).symm⟩

section SymSections

/-- The underlying presheaf of a sheaf of `𝒪_W`-modules, read over the presheaf of rings
underlying the commutative structure sheaf: the spelling in which the sectionwise symmetric powers
are formed, so that the sections over a chart are a module over the commutative ring of
functions there. -/
abbrev commStructureVal {W : AlgebraicSpaces B S hS}
    (G : SheafOfModules.{u} (structureRingSheaf B S hS W)) :
    PresheafOfModules.{u} ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat) :=
  G.val

variable (W : AlgebraicSpaces B S hS) (G : SheafOfModules.{u} (structureRingSheaf B S hS W))
  (hG : G.IsQuasicoherentOnSite) (V : SmallEtale B S hS W.1)
  (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))

/-- `Symⁿ` of the sections of `𝒢` over an affine chart is the sections of `Symⁿ(𝒢)` there, as an
isomorphism of additive groups: the sheafification unit. -/
def symPieceUnit (n : ℕ) :
    SymPow.symmetricPower n
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)) ≃+
      (((symmetricAlgebra B S hS W G).piece (n : ℤ)).val.obj (op V)) :=
  AddEquiv.mk' (Equiv.ofBijective _
      (bijective_symmetricAlgebra_sheafifyUnit_of_isAffine B S hS W G hG (n : ℤ) V hV))
    fun x y => map_add ((PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
        (R := structureRingSheaf B S hS W)
      (𝟙 (structureRingSheaf B S hS W).obj) (PresheafOfModules.symPowInt (n : ℤ) G.val)).app
        (op V)).hom x y

/-- `symPieceUnit` is the sheafification unit on sections over `V`. -/
theorem symPieceUnit_apply (n : ℕ)
    (x : SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) :
    symPieceUnit B S hS W G hG V hV n x =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
          (R := structureRingSheaf B S hS W)
        (𝟙 (structureRingSheaf B S hS W).obj) (PresheafOfModules.symPowInt (n : ℤ) G.val))
          (op V) x := rfl

/-- The degreewise sheafification unit followed by the inclusion of the degree-`n` summand of the
direct sum of the sections of the homogeneous pieces of `Sym(𝒢)`. -/
def symPowerIncl (n : ℕ) :
    SymPow.symmetricPower n
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)) →+
      (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.Total (op V) :=
  (DirectSum.of (fun m : ℤ => (((symmetricAlgebra B S hS W G).piece m).val.obj (op V) : Type u))
    (n : ℤ)).comp (symPieceUnit B S hS W G hG V hV n).toAddMonoidHom

/-- `symPowerIncl` sends `x` to `symPieceUnit` of `x` in the degree-`n` summand. -/
theorem symPowerIncl_apply (n : ℕ)
    (x : SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) :
    symPowerIncl B S hS W G hG V hV n x =
      DirectSum.of (fun m : ℤ => (((symmetricAlgebra B S hS W G).piece m).val.obj (op V) : Type u))
        (n : ℤ) (symPieceUnit B S hS W G hG V hV n x) := rfl

/-- The degree-zero summand carries the unit to the unit. -/
theorem symPowerIncl_one
    (x : SymPow.symmetricPower 0
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))
    (hx : (x : SymmetricAlgebra
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) = 1) :
    symPowerIncl B S hS W G hG V hV 0 x = 1 :=
  (congrArg (DirectSum.of
      (fun m : ℤ => (((symmetricAlgebra B S hS W G).piece m).val.obj (op V) : Type u)) 0)
      ((congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
          (R := structureRingSheaf B S hS W)
            (𝟙 (structureRingSheaf B S hS W).obj) (PresheafOfModules.symPowInt (0 : ℤ) G.val))
            (op V))
          (Subtype.ext hx : x =
            (PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).one.eval
              (op V))).trans
        ((PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).sheafify_one_eval
          (𝟙 (structureRingSheaf B S hS W).obj) (op V)).symm)).trans
    ((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.one_eq_incl (op V)).symm

/-- The summands multiply as the symmetric powers do. -/
theorem symPowerIncl_mul (i j : ℕ)
    (a : SymPow.symmetricPower i
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))
    (b : SymPow.symmetricPower j
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))
    (c : SymPow.symmetricPower (i + j)
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))
    (hc : (c : SymmetricAlgebra
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V))) =
      (a : SymmetricAlgebra
          (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          ((commStructureVal B S hS G).obj (op V))) *
        (b : SymmetricAlgebra
          (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          ((commStructureVal B S hS G).obj (op V)))) :
    symPowerIncl B S hS W G hG V hV (i + j) c =
      symPowerIncl B S hS W G hG V hV i a * symPowerIncl B S hS W G hG V hV j b :=
  Eq.symm
    (((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.incl_mul_incl
        (i : ℤ) (j : ℤ) _ _).trans
      (congrArg (DirectSum.of
          (fun m : ℤ => (((symmetricAlgebra B S hS W G).piece m).val.obj (op V) : Type u)) _)
        (((PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).sheafify_mul_unit
            (𝟙 (structureRingSheaf B S hS W).obj) (i : ℤ) (j : ℤ) (op V) a b).trans
          (congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
              (R := structureRingSheaf B S hS W)
              (𝟙 (structureRingSheaf B S hS W).obj)
              (PresheafOfModules.symPowInt ((i : ℤ) + (j : ℤ)) G.val)) (op V))
            (Subtype.ext hc.symm)))))

/-- The degreewise sheafification unit as a ring homomorphism out of the external direct sum of
the symmetric powers of the sections of `𝒢`. -/
def ofSymPowers :
    (⨁ n : ℕ, SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) →+*
      (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.Total (op V) :=
  DirectSum.toSemiring (symPowerIncl B S hS W G hG V hV)
    (symPowerIncl_one B S hS W G hG V hV _ rfl)
    (fun {_ _} ai aj => symPowerIncl_mul B S hS W G hG V hV _ _ ai aj _ rfl)

/-- `ofSymPowers` agrees with `symPowerIncl` on the degree-`n` summand. -/
theorem ofSymPowers_of (n : ℕ)
    (x : SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) :
    ofSymPowers B S hS W G hG V hV (DirectSum.of _ n x) = symPowerIncl B S hS W G hG V hV n x :=
  DirectSum.toSemiring_of (symPowerIncl B S hS W G hG V hV) _ _ n x

/-- The degreewise sheafification unit, assembled over the nonnegative degrees. -/
def natSumUnit :
    (⨁ n : ℕ, SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) ≃+
    Stacks.DirectSumType (fun n : ℕ => ((symmetricAlgebra B S hS W G).piece (n : ℤ)).val)
      (op V) :=
  DFinsupp.mapRange.addEquiv fun n => symPieceUnit B S hS W G hG V hV n

/-- `natSumUnit` agrees with `symPieceUnit` on the degree-`n` summand. -/
theorem natSumUnit_of (n : ℕ)
    (x : SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) :
    natSumUnit B S hS W G hG V hV (DirectSum.of _ n x) =
      DirectSum.of (fun m : ℕ =>
        (((symmetricAlgebra B S hS W G).piece (m : ℤ)).val.obj (op V) : Type u)) n
        (symPieceUnit B S hS W G hG V hV n x) :=
  DFinsupp.mapRange_single (hf := fun n => (symPieceUnit B S hS W G hG V hV n).map_zero)

/-- The underlying additive map of `AlgebraicGeometry.Space.ofSymPowers` is the degreewise
sheafification unit followed by the inclusion of the nonnegative degrees. -/
theorem ofSymPowers_apply_eq
    (z : ⨁ n : ℕ, SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) :
    ofSymPowers B S hS W G hG V hV z =
      Stacks.directSumNatToIntApp (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val)
        (op V) (natSumUnit B S hS W G hG V hV z) := by
  induction z using DirectSum.induction_on with
  | zero =>
      exact (map_zero (ofSymPowers B S hS W G hG V hV)).trans
        (((congrArg (Stacks.directSumNatToIntApp
            (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V))
            (map_zero (natSumUnit B S hS W G hG V hV))).trans
          (map_zero (Stacks.directSumNatToIntApp
            (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V)))).symm)
  | of n x =>
      exact (ofSymPowers_of B S hS W G hG V hV n x).trans
        ((Stacks.directSumNatToIntApp_of
            (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V) n
            (symPieceUnit B S hS W G hG V hV n x)).symm.trans
          (congrArg (Stacks.directSumNatToIntApp
              (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V))
            (natSumUnit_of B S hS W G hG V hV n x).symm))
  | add z z' hz hz' =>
      exact (map_add (ofSymPowers B S hS W G hG V hV) z z').trans
        ((congrArg₂ (· + ·) hz hz').trans
          (((congrArg (Stacks.directSumNatToIntApp
              (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V))
              (map_add (natSumUnit B S hS W G hG V hV) z z')).trans
            (map_add (Stacks.directSumNatToIntApp
              (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V)) _ _)).symm))

/-- **The direct sum of the symmetric powers of the sections of `𝒢` over an affine chart is the
direct sum of the sections of the homogeneous pieces of `Sym(𝒢)` there.** -/
theorem bijective_ofSymPowers : Function.Bijective (ofSymPowers B S hS W G hG V hV) := by
  rw [show (ofSymPowers B S hS W G hG V hV : _ → _) = _ from
    funext (ofSymPowers_apply_eq B S hS W G hG V hV)]
  exact (Stacks.bijective_directSumNatToIntApp
      (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val) (op V)
      (fun n hn => subsingleton_symmetricAlgebra_piece_of_neg B S hS W G n hn (op V))).comp
      (natSumUnit B S hS W G hG V hV).bijective

/-- **The ring of sections of `Sym(𝒢)` over an affine étale chart is the symmetric algebra of the
sections of `𝒢`**, for `𝒢` quasi-coherent. -/
def symmetricAlgebraSheafSectionsRingEquiv :
    SymmetricAlgebra
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)) ≃+*
    ((symmetricAlgebraSheaf B S hS W G).right.obj.obj (op V)) :=
  (DirectSum.decomposeRingEquiv (fun n : ℕ => SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))).trans
    ((RingEquiv.ofBijective (ofSymPowers B S hS W G hG V hV)
        (bijective_ofSymPowers B S hS W G hG V hV)).trans
      (RingEquiv.ofBijective ((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.totalUnit
          (SmallEtale.topology B S hS W.1) (op V))
        (bijective_totalUnit_of_isAffine B S hS W (symmetricAlgebra B S hS W G) V hV)))

/-- The image of `r` in the degree-zero symmetric power. -/
def symOne
    (r : (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) :
    SymPow.symmetricPower 0
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)) :=
  ⟨algebraMap (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      (SymmetricAlgebra
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V))) r, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r SetLike.GradedOne.one_mem⟩

/-- The structure map of the ungraded realization is the degree-zero part of the structure map
of the symmetric algebra of the sections. -/
theorem structureMap_eq_ofSymPowers (r : (structureRingSheaf B S hS W).obj.obj (op V)) :
    (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.structureMap (op V) r =
      ofSymPowers B S hS W G hG V hV (DirectSum.of
        (fun m : ℕ => (SymPow.symmetricPower m
            (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            ((commStructureVal B S hS G).obj (op V)) : Type u)) 0
          (symOne B S hS W G V r)) := by
  have hone := (PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).sheafify_one_eval
    (𝟙 (structureRingSheaf B S hS W).obj) (op V)
  have hlin := ((PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
    (R := structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
    (PresheafOfModules.symPowInt (0 : ℤ) G.val)).app (op V)).hom.map_smul r
      ((PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).one.eval (op V))
  have h3 : r • (symmetricAlgebra B S hS W G).one.eval (op V) =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
        (R := structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
        (PresheafOfModules.symPowInt (0 : ℤ) G.val)) (op V) (symOne B S hS W G V r) :=
    ((congrArg (fun y => r • y) hone).trans hlin.symm).trans
      (congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
          (R := structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
          (PresheafOfModules.symPowInt (0 : ℤ) G.val)) (op V))
        (Subtype.ext
          (Algebra.algebraMap_eq_smul_one (R :=
              (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V)))
            (A := SymmetricAlgebra
                (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                ((commStructureVal B S hS G).obj (op V))) r).symm))
  exact Eq.trans
    (((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.incl_smul (0 : ℤ) r
          ((symmetricAlgebra B S hS W G).one.eval (op V))).symm.trans
      (congrArg (DirectSum.of
        (fun m : ℤ => (((symmetricAlgebra B S hS W G).piece m).val.obj (op V) : Type u)) 0) h3))
    (ofSymPowers_of B S hS W G hG V hV 0 (symOne B S hS W G V r)).symm

/-- **The identification carries `algebraMap` to the structure map of the algebra sheaf
`Sym(𝒢)`.** -/
theorem symmetricAlgebraSheafSectionsRingEquiv_algebraMap
    (r : (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) :
    symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV
        (algebraMap (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            (SymmetricAlgebra
              (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
              ((commStructureVal B S hS G).obj (op V))) r) =
      (symmetricAlgebraSheaf B S hS W G).algebraMap (op V) r := by
  have hdec : DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V)))
      (algebraMap (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          (SymmetricAlgebra
            (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            ((commStructureVal B S hS G).obj (op V))) r) =
      DirectSum.of (fun m : ℕ => (SymPow.symmetricPower m
          (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          ((commStructureVal B S hS G).obj (op V)) : Type u)) 0
        (symOne B S hS W G V r) :=
    DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)))
      (symOne B S hS W G V r).2
  have h : ofSymPowers B S hS W G hG V hV (DirectSum.decompose
      (fun n : ℕ => SymPow.symmetricPower n
          (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          ((commStructureVal B S hS G).obj (op V)))
      (algebraMap (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          (SymmetricAlgebra
            (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            ((commStructureVal B S hS G).obj (op V))) r)) =
      (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.structureMap (op V) r :=
    (congrArg (ofSymPowers B S hS W G hG V hV) hdec).trans
      (structureMap_eq_ofSymPowers B S hS W G hG V hV r).symm
  exact congrArg ((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.totalUnit
    (SmallEtale.topology B S hS W.1) (op V)) h

include hG hV in
/-- **For `𝒢` of finite presentation over an affine chart, the structure map of `Sym(𝒢)` there
is of finite presentation.** -/
theorem finitePresentation_symmetricAlgebraSheaf_algebraMap
    (hfp : Module.FinitePresentation
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V))) :
    RingHom.FinitePresentation ((symmetricAlgebraSheaf B S hS W G).algebraMap (op V)) := by
  have halg : RingHom.FinitePresentation (algebraMap
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      (SymmetricAlgebra
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)))) :=
    RingHom.finitePresentation_algebraMap.2 (Stacks.SymAlg.finitePresentation _ _)
  have htr := RingHom.finitePresentation_respectsIso.1 _
    (symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV) halg
  refine (show (symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV).toRingHom.comp
    (algebraMap (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        (SymmetricAlgebra
          (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
          ((commStructureVal B S hS G).obj (op V)))) =
      (symmetricAlgebraSheaf B S hS W G).algebraMap (op V) from ?_) ▸ htr
  exact RingHom.ext (symmetricAlgebraSheafSectionsRingEquiv_algebraMap B S hS W G hG V hV)

end SymSections

end AlgebraicGeometry.Space

end
