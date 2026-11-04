module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSheafifyModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules

/-!
# The sections of the symmetric algebra of a quasi-coherent module over an affine chart

Let `W` be an algebraic space over a scheme `S` and `ℱ` an `𝒪_W`-module on its small étale site
which is cartesian on affine charts — for instance a quasi-coherent one (Stacks 03DX(2)).  The
symmetric algebra `Sym(ℱ)` of `AlgebraicGeometry.Space.symmetricAlgebra` is the degreewise
sheafification of the presheaf of sectionwise symmetric powers `U ↦ Symⁿ_{𝒪(U)}(ℱ(U))`.  This
file proves that over an affine étale chart nothing is changed by that sheafification: the
presheaf of sectionwise symmetric powers is cartesian on the affine étale site (symmetric powers
commute with base change), hence a sheaf there by flat descent, and the affine charts form a dense
subsite of the small étale site (Stacks 04JS).  Two consequences are drawn:

* every homogeneous piece `Symⁿ(ℱ)` is cartesian on affine charts, hence quasi-coherent
  (Stacks 01CK for the small étale site of an algebraic space);
* over an affine chart `U` the sections of `Symⁿ(ℱ)` are `Symⁿ_{𝒪(U)}(ℱ(U))`, so their number is
  bounded by those of `𝒪(U)`, of `ℱ(U)` and `ℵ₀`.

## Main results

* `SymmetricAlgebra.cardinalMk_le_max`: a symmetric algebra is no larger than its ring, its
  module and `ℵ₀`.
* `AlgebraicGeometry.Space.isSheaf_affineEtale_symPowInt`: the sectionwise symmetric powers form
  a sheaf on the affine étale site.
* `AlgebraicGeometry.Space.isIso_symmetricAlgebra_unit_app`: the sheafification unit is an
  isomorphism over an affine chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_symmetricAlgebra_piece` and
  `isQuasicoherentOnSite_symmetricAlgebra_piece_of_isCartesianOnAffineCharts` (same namespace):
  **the homogeneous pieces of `Sym(ℱ)` are cartesian on affine charts and quasi-coherent.**
* `AlgebraicGeometry.Space.mk_symmetricAlgebra_piece_sections_le`: the bound on their sections
  over an affine chart.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SymmetricAlgebra

universe w

/-- **The symmetric algebra of a module is no larger than the ring, the module and `ℵ₀`**: it is
generated as an algebra by the image of the module. -/
theorem cardinalMk_le_max (R : Type w) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M] :
    Cardinal.mk (SymmetricAlgebra R M) ≤
      max (max (Cardinal.mk R) (Cardinal.mk M)) Cardinal.aleph0 := by
  have htop : Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) = ⊤ := by
    refine eq_top_iff.2 fun x hx0 => ?_
    clear hx0
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
    | mul x y hx hy => exact Subalgebra.mul_mem _ hx hy
    | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  have h := Algebra.cardinalMk_adjoin_le R (Set.range (SymmetricAlgebra.ι R M))
  rw [htop] at h
  refine (Cardinal.mk_congr (Subalgebra.topEquiv (R := R) (A := SymmetricAlgebra R M)).toEquiv
    ).symm.trans_le (h.trans ?_)
  exact max_le_max (max_le_max le_rfl (Cardinal.mk_range_le)) le_rfl

end SymmetricAlgebra

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- **The sectionwise symmetric powers of a module cartesian on affine charts form a sheaf on the
affine étale site**: they are cartesian there
(`Stacks.PresheafOfModules.isIso_restrictionBaseChange_symPowInt`), and a cartesian presheaf of
modules on the affine étale site is a sheaf by flat descent. -/
theorem isSheaf_affineEtale_symPowInt (hF : IsCartesianOnAffineCharts F) (n : ℕ) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS W.1)
      ((AffineEtale.inclusion B S hS W.1).op ⋙
        (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val).presheaf) := by
  let F' : PresheafOfModules.{u} (affineEtaleChartRings B S hS W.1 ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pushforward₀ (AffineEtale.inclusion B S hS W.1)
      (structurePresheaf B S hS W.1 ⋙ forget₂ CommRingCat RingCat)).obj F.val
  have hF' : ∀ {X Y : (AffineEtale B S hS W.1)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange F' f) := fun {X Y} f =>
    (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS W.1 W.2 F f.unop.hom).1
      (hF _ _ X.unop.property Y.unop.property f.unop.hom)
  refine
    Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, u + 1, u, u, u, u + 1}
      (AffineEtale.toScheme B S hS W.1) (affineEtaleChartRings B S hS W.1) ?_ ?_
      (PresheafOfModules.symPowInt (n : ℤ) F')
      (fun f => have := hF' f; Stacks.PresheafOfModules.isIso_restrictionBaseChange_symPowInt
        (n : ℤ) F' f)
      (AffineEtale.topology B S hS W.1) ?_
  · intro U E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS W.1))).mp hE
    exact faithfullyFlat_pi_affineEtaleChartRings B S hS W.1 E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineEtaleChartRings B S hS W.1 h
  · intro U T hT
    exact Stacks.Sites.exists_finite_flat_refinement (AffineEtale.toScheme B S hS W.1)
      (AffineEtale.precoverage B S hS W.1) (affineEtale_covering_finite_flat B S hS W.1) T hT

/-- **Over an affine chart the sheafification unit of a sectionwise symmetric power is an
isomorphism**, the affine charts forming a dense subsite on which the presheaf is already a sheaf.
-/
theorem isIso_symmetricAlgebra_unit_app (hF : IsCartesianOnAffineCharts F) (n : ℕ)
    (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    IsIso (((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app
          (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)).app (op U)) := by
  have hsp := AffineEtale.inclusion_isSpecialCocontinuous B S hS W.1 W.2
  let _ : (AffineEtale.inclusion B S hS W.1).IsCocontinuous
    (AffineEtale.topology B S hS W.1) (SmallEtale.topology B S hS W.1) := hsp.1
  let _ : (AffineEtale.inclusion B S hS W.1).IsDenseSubsite
    (AffineEtale.topology B S hS W.1) (SmallEtale.topology B S hS W.1) := hsp.2
  have h : IsIso ((toSheafify (SmallEtale.topology B S hS W.1)
      (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val).presheaf).app
        (op ((AffineEtale.inclusion B S hS W.1).obj ⟨U, hU⟩))) :=
    Presheaf.isIso_toSheafify_app_of_isDenseSubsite _ _ _ _
      (isSheaf_affineEtale_symPowInt B S hS W F hF n) ⟨U, hU⟩
  have key := @PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
    (SmallEtale.topology B S hS W.1) _ (structureRingSheaf B S hS W) (𝟙 _)
    (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W)
    (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)
  rw [ConcreteCategory.isIso_iff_bijective]
  have e2 := congrArg (NatTrans.app · (op U)) key
  have hb' : Function.Bijective ⇑(ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app
          (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val))).app (op U))) := by
    rw [e2]
    exact (ConcreteCategory.isIso_iff_bijective _).1 h
  exact hb'

/-- **The homogeneous pieces of `Sym(ℱ)` are cartesian on affine charts**, for `ℱ` cartesian on
affine charts: over affine charts they are the sectionwise symmetric powers, whose base change
comparison is an isomorphism. -/
theorem isCartesianOnAffineCharts_symmetricAlgebra_piece (hF : IsCartesianOnAffineCharts F)
    (n : ℕ) : IsCartesianOnAffineCharts ((symmetricAlgebra B S hS W F).piece (n : ℤ)) := by
  intro U V hU hV f
  refine (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS W.1 W.2
    ((symmetricAlgebra B S hS W F).piece (n : ℤ)) f).2 ?_
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureRingSheaf B S hS W).obj)).unit.app
      (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)
  have hnat := Stacks.PresheafOfModules.restrictionBaseChange_naturality.{u + 1, u, u, u}
    (R := structurePresheaf B S hS W.1) η f.op
  have hX : IsIso (η.app (op U)) := isIso_symmetricAlgebra_unit_app B S hS W F hF n U hU
  have hY : IsIso (η.app (op V)) := isIso_symmetricAlgebra_unit_app B S hS W F hF n V hV
  have hP : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS W.1)
      (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val) f.op) :=
    have : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := structurePresheaf B S hS W.1) F.val f.op) :=
      (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS W.1 W.2 F f).1
        (hF U V hU hV f)
    Stacks.PresheafOfModules.isIso_restrictionBaseChange_symPowInt
      (O := structurePresheaf B S hS W.1) (n : ℤ) F.val f.op
  have h2 : IsIso ((ModuleCat.extendScalars ((structurePresheaf B S hS W.1).map f.op).hom).map
      (η.app (op U)) ≫ Stacks.PresheafOfModules.restrictionBaseChange
        (R := structurePresheaf B S hS W.1) _ f.op) := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hP hY
  have : IsIso ((ModuleCat.extendScalars ((structurePresheaf B S hS W.1).map f.op).hom).map
      (η.app (op U))) := @Functor.map_isIso _ _ _ _ _ _ _ _ hX
  exact IsIso.of_isIso_comp_left
    ((ModuleCat.extendScalars ((structurePresheaf B S hS W.1).map f.op).hom).map (η.app (op U)))
    (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS W.1)
      ((PresheafOfModules.sheafification.{u} (𝟙 (structureRingSheaf B S hS W).obj) ⋙
        SheafOfModules.forget (structureRingSheaf B S hS W) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureRingSheaf B S hS W).obj)).obj
            (PresheafOfModules.symPowInt.{u, u + 1, u, u} (↑n) F.val)) f.op)

/-- **The homogeneous pieces of `Sym(ℱ)` are quasi-coherent**, for `ℱ` cartesian on affine charts
(Stacks 01CK on the small étale site of an algebraic space). -/
theorem isQuasicoherentOnSite_symmetricAlgebra_piece_of_isCartesianOnAffineCharts
    (hF : IsCartesianOnAffineCharts F) (n : ℕ) :
    ((symmetricAlgebra B S hS W F).piece (n : ℤ)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_symmetricAlgebra_piece B S hS W F hF n)

/-- **Over an affine chart `U` the sections of `Symⁿ(ℱ)` are no more than those of `𝒪(U)`, of
`ℱ(U)` and `ℵ₀`**: they are `Symⁿ_{𝒪(U)}(ℱ(U))`. -/
theorem mk_symmetricAlgebra_piece_sections_le (hF : IsCartesianOnAffineCharts F) (n : ℕ)
    (U : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Cardinal.mk (((symmetricAlgebra B S hS W F).piece (n : ℤ)).val.obj (op U)) ≤
      max (max (Cardinal.mk ((structureSheaf B S hS W.1 W.2).obj.obj (op U)))
        (Cardinal.mk (F.val.obj (op U)))) Cardinal.aleph0 := by
  have hX := isIso_symmetricAlgebra_unit_app B S hS W F hF n U hU
  rw [ConcreteCategory.isIso_iff_bijective] at hX
  refine (Cardinal.mk_congr (Equiv.ofBijective _ hX)).symm.trans_le ?_
  refine (Cardinal.mk_le_of_injective (f := fun x :
    (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val).obj (op U) =>
      PresheafOfModules.symPowIntVal x)
    fun _ _ h => PresheafOfModules.symPowIntVal_injective _ _ h).trans ?_
  exact SymmetricAlgebra.cardinalMk_le_max _ _

end AlgebraicGeometry.Space

end
