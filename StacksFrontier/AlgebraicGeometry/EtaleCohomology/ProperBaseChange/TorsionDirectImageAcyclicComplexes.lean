module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompRightDerivedBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange

/-!
# Complexes of acyclic sheaves compute `Rh_*` for a proper `h` and a torsion ring

Let `h : Y ⟶ Z` be a proper morphism of schemes, `Λ` a torsion ring, and `P` a complex of
sheaves of `Λ`-modules on `Y_étale` each of which is acyclic for `h_*`. Then `P` computes the
derived direct image on the unbounded derived category: `h_*` carries every quasi-isomorphism
`s : P ⟶ J` to a K-injective complex to a quasi-isomorphism.

This is the core of case (b) of [Stacks, Tag 0F7G]. The source argues: the question is local on
`Z`, so one may assume `Z` quasi-compact, hence the fibres of `h` of bounded dimension
([Stacks, Tag 0A3V]); then `Rh_*` has finite cohomological dimension on torsion sheaves
([Stacks, Tag 095U]), every sheaf of `Λ`-modules being torsion, and a complex of acyclics computes
it ([Stacks, Tag 07K7]). Here the localization is done at the level of complexes: over an affine
open `U ⊆ Z` the restriction of `h_*(s)` is `h_{U,*}` of the restriction of `s`, restriction
preserving K-injective complexes and acyclicity for direct images.

Everything below lives in the namespace `Stacks.EtaleCohomology`.

## Main results

* `quasiIso_of_forall_quasiIso_map`: a morphism of complexes is a quasi-isomorphism as soon as
  its images under a family of exact functors jointly reflecting isomorphisms are.
* `isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_natCast_eq_zero`:
  [Stacks, Tag 095U] for sheaves of `Λ`-modules over a torsion ring, through
  `rightDerivedEtaleModuleDirectImageForgetUnivIso`.
* `quasiIso_etaleModuleDirectImage_map_of_rightAcyclic`: the statement above.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Quasi-isomorphisms are detected by a jointly conservative family of exact functors -/

section Locality

variable {A : Type*} [Category* A] [Abelian A] {ι : Type*} {B : ι → Type*}
  [∀ i, Category* (B i)] [∀ i, Abelian (B i)] (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
  [∀ i, (F i).PreservesHomology]

/-- **Quasi-isomorphisms are detected by a jointly conservative family of exact functors.** If
the functors `F i` preserve homology and jointly reflect isomorphisms, a morphism of complexes
whose images under all `F i` are quasi-isomorphisms is a quasi-isomorphism: on each homology
object, `F i` of the map is the map on homology of the image. -/
theorem quasiIso_of_forall_quasiIso_map
    (hF : ∀ {X Y : A} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (h : ∀ i, QuasiIso (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  refine hF _ fun i => ?_
  have hi := (quasiIso_iff _).1 (h i) n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff] at hi
  let ψ := (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map φ
  change IsIso (ShortComplex.homologyMap ((F i).mapShortComplex.map ψ)) at hi
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso (F i)) ψ).1 hi

end Locality

/-! ### Higher direct images of sheaves of modules -/

section Modules

variable (Λ : Type u) [Ring Λ]

/-- Sheaves of `Λ`-modules on a small étale site have enough injectives, stated at the
coefficient universe `u + 1` so that instance search does not have to solve
`max (u + 1) ?r = u + 1`. -/
instance etaleModules_enoughInjectives_univSelf (Z : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, u} Λ Z) :=
  etaleModules_enoughInjectives.{u, u} Λ Z

/-- Sheaves of `Λ`-modules on a small étale site form a Grothendieck abelian category, stated at
the coefficient universe `u + 1`. -/
instance etaleModules_isGrothendieckAbelian_univSelf (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (EtaleModules.{u, u} Λ Z) :=
  etaleModules_isGrothendieckAbelian.{u, u} Λ Z

/-- If `m • 1 = 0` in `Λ` with `m > 0`, the underlying abelian sheaf of every sheaf of
`Λ`-modules is torsion: it is annihilated by `m`. -/
theorem torsionSheafProperty_etaleModuleForgetUniv_obj_of_natCast_eq_zero (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) {Z : Scheme.{u}} (G : EtaleModules.{u, u} Λ Z) :
    Stacks.Torsion.torsionSheafProperty Z.smallEtaleTopology
      ((etaleModuleForgetAb.{u, u} Λ Z).obj G) := by
  intro U x
  refine ⟨⊤, Z.smallEtaleTopology.top_mem U, fun V g _ => ⟨m, hm, ?_⟩⟩
  show m • (G.obj.map g.op x : G.obj.obj (Opposite.op V)) = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 095U] for sheaves of `Λ`-modules over a torsion ring**: for `f` proper with
fibres of dimension `≤ n`, `R^q f_* G = 0` for every sheaf of `Λ`-modules `G` and `q > 2n`. -/
theorem isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_natCast_eq_zero [IsProper f]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (n : ℕ)
    (hfib : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n) (G : EtaleModules.{u, u} Λ X)
    (q : ℕ) (hq : 2 * n < q) :
    IsZero (((etaleModuleDirectImage.{u, u} Λ f).rightDerived q).obj G) := by
  have h := (isZero_rightDerived_etaleAbelianDirectImage_of_isProper f n hfib _
    (torsionSheafProperty_etaleModuleForgetUniv_obj_of_natCast_eq_zero Λ m hm hΛ G) q hq).of_iso
    ((rightDerivedEtaleModuleDirectImageForgetUnivIso Λ f q).app G)
  rw [IsZero.iff_id_eq_zero]
  exact (etaleModuleForgetAb.{u, u} Λ Y).map_injective (by simpa using h.eq_of_src _ _)

/-- **Complexes of `h_*`-acyclic sheaves compute `Rh_*` for `h` proper and `Λ` torsion**
(the core of case (b) of [Stacks, Tag 0F7G]). Let `h : Y ⟶ Z` be proper, `Λ` a ring with
`m • 1 = 0` for some `m > 0`, and `P` a complex of sheaves of `Λ`-modules on `Y_étale` whose terms
have no higher direct images along `h`. Then `h_*` carries every quasi-isomorphism `s : P ⟶ J` to
a K-injective complex to a quasi-isomorphism.

Over each affine open `U` of `Z` the restriction of `h_*(s)` is the direct image along
`h_U : Y ×_Z U ⟶ U` of the restriction of `s` (`etaleRestrictionPushforwardIsoOfIsPullback`); the
restriction of `J` is K-injective, extension by zero being an exact left adjoint of restriction,
and the restrictions of the terms of `P` are `h_{U,*}`-acyclic. The fibres of `h_U` have bounded
dimension ([Stacks, Tag 0A3V]), so `h_{U,*}` has finite cohomological dimension on sheaves of
`Λ`-modules ([Stacks, Tag 095U]) and complexes of acyclics compute it ([Stacks, Tag 07K7]).
Quasi-isomorphy is local on `Z` (`quasiIso_of_forall_quasiIso_map`). -/
theorem quasiIso_etaleModuleDirectImage_map_of_rightAcyclic {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    [IsProper h] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    {P J : CochainComplex (EtaleModules.{u, u} Λ Y) ℤ}
    (hP : ∀ (i : ℤ) (p : ℕ), 0 < p →
      IsZero (((etaleModuleDirectImage.{u, u} Λ h).rightDerived p).obj (P.X i)))
    (s : P ⟶ J) [QuasiIso s] (hJ : J.IsKInjective) :
    QuasiIso (((etaleModuleDirectImage.{u, u} Λ h).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  let 𝒰 := Z.affineCover
  have hcov : Z.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (𝒰.f i) :=
    coversTop_smallEtaleObj_of_jointlySurjective (fun i ↦ 𝒰.f i) fun z ↦ ⟨_, 𝒰.covers z⟩
  refine quasiIso_of_forall_quasiIso_map (fun i ↦ etaleModuleRestriction.{u, u} Λ (𝒰.f i))
    (fun φ hφ ↦ isIso_of_isIso_etaleRestrictionAt (A := ModuleCat.{u + 1} Λ) φ
      (fun i ↦ 𝒰.f i) hcov hφ) _ fun i ↦ ?_
  let j := 𝒰.f i
  let hU := pullback.snd h j
  let pY := pullback.fst h j
  have upper : IsPullback hU pY j h := (IsPullback.of_hasPullback h j).flip
  have : Etale pY := inferInstance
  let r' := etaleModuleRestriction.{u, u} Λ pY
  let HU := etaleModuleDirectImage.{u, u} Λ hU
  let e : r' ⋙ HU ≅ etaleModuleDirectImage.{u, u} Λ h ⋙ etaleModuleRestriction.{u, u} Λ j :=
    etaleRestrictionPushforwardIsoOfIsPullback (A := ModuleCat.{u + 1} Λ) upper
  -- the restriction of `J` is K-injective
  have hJ' : CochainComplex.IsKInjective ((r'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    have := hJ
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact r'
      (etaleModuleExtensionByZero.{u, u} Λ pY) (etaleModuleExtensionByZeroAdj.{u, u} Λ pY) J
  -- restriction preserves injective objects, hence acyclicity for direct images
  have : r'.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleModuleExtensionByZeroAdj.{u, u} Λ pY)
  have : (etaleModuleRestriction.{u, u} Λ j).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hL : ∀ (n : ℤ) (p : ℕ), 0 < p →
      IsZero ((HU.rightDerived p).obj
        (((r'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)) :=
    fun n p hp ↦ ((etaleModuleRestriction.{u, u} Λ j).map_isZero (hP n p hp)).of_iso
      ((Functor.rightDerivedSquareIsoOfExact (etaleModuleDirectImage.{u, u} Λ h)
        (etaleModuleRestriction.{u, u} Λ j) r' HU e.symm p).app (P.X n)).symm
  -- finite cohomological dimension over the affine `U`
  have : CompactSpace (𝒰.X i) := inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le hU
  have hdim : ∀ (M : EtaleModules.{u, u} Λ (pullback h j)) (p : ℕ), 2 * d < p →
      IsZero ((HU.rightDerived p).obj M) := fun M p hp ↦
    isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_natCast_eq_zero Λ hU m hm hΛ d hd
      M p hp
  have hU' := Stacks.ExactCompDerived.quasiIso_map_of_rightAcyclic_of_bounded.{u + 1} HU (2 * d)
    hdim hL ((r'.mapHomologicalComplex (ComplexShape.up ℤ)).map s) hJ'
  have hU'' : QuasiIso (((r' ⋙ HU).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := hU'
  show QuasiIso (((etaleModuleDirectImage.{u, u} Λ h ⋙
    etaleModuleRestriction.{u, u} Λ j).mapHomologicalComplex (ComplexShape.up ℤ)).map s)
  refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).1 hU''
  exact Arrow.isoMk ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app J)
    ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.naturality s).symm

end Modules

end Stacks.EtaleCohomology

end
