module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineGlobalPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSpacesEtaleGlobalVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedUnitDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionCounitTruncations

/-!
# The derived functors of the ringed point of global sections of an affine algebraic space

Let `p : (X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)` be the morphism to the ringed point of global
sections of an affine algebraic space `X` (`AlgebraicGeometry.BigFppfSpaceSite.affinePointHom`).
Its pullback `p^*` is exact, so `Lp^*` is computed degreewise and commutes with cohomology
sheaves. The following facts on `Lp^* ⊣ Rp_*` do not involve unbounded complexes:

* the higher cohomology of a quasi-coherent module vanishes over the images of the affine étale
  charts, and in particular `R^q p_* 𝓕 = H^q(X, 𝓕) = 0` for `q > 0` and `𝓕` quasi-coherent
  (Stacks 03DW);
* the derived unit `M[0] ⟶ Rp_* Lp^* M[0]` is invertible for every module `M` on the point;
* the derived counit `Lp^* Rp_* 𝓕[n] ⟶ 𝓕[n]` is invertible for every quasi-coherent `𝓕`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_spacesEtale_of_isQuasicoherentOnSite`:
  the module-valued higher cohomology of a quasi-coherent module over the image of an affine
  chart vanishes.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_homology_affinePointHom_derivedPushforward_single`:
  `H^q(Rp_*(𝓕[0])) = 0` for `q > 0` and `𝓕` quasi-coherent.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction`
  `.derivedPullbackIsoMapDerivedCategoryOfExact`: for an exact pullback, and so for `p^*`,
  `Lp^*` is the functor `p^*` induces on derived categories.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_affinePointDerivedAdjunction_unit_app_single` and
  `AlgebraicGeometry.BigFppfSpaceSite.isIso_affinePointDerivedAdjunction_counit_app_singleFunctor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard


attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- The modules on the ringed spaces-étale site at the universe `u + 1` of its objects and
morphisms have enough injectives, the category being Grothendieck abelian there. -/
theorem enoughInjectives_spacesEtaleModules :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O)) := by
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)) :=
    SheafOfModules.isGrothendieckAbelianU.{u + 1, u + 1, u + 1} _
  exact IsGrothendieckAbelian.enoughInjectives.{u + 1}

attribute [local instance] enoughInjectives_spacesEtaleModules

/-- **The higher cohomology of a quasi-coherent module vanishes over the image of an affine
chart**, read as the module-valued right derived functors of the sections over that object. -/
theorem isZero_rightDerived_evaluation_spacesEtale_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O))
    (hM : M.IsQuasicoherentOnSite) (U : SpacesEtale B S hS Y)
    (hU : U ∈ SpacesEtale.affineChartImages B S hS Y) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O) (op U)).rightDerived p).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n + 1 := ⟨p - 1, by omega⟩
  have h := SpacesEtale.isZero_sheafH'_of_isZero_cechCohomology B S hS Y
    ((SheafOfModules.toSheaf.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O)).obj M)
    (fun hW E hfin haff hcov q hq ↦
      SmallEtale.isZero_cechCohomology_comparisonCoefficients B S hS Y M hM hW E hfin haff hcov
        q hq) U hU (n + 1) (Nat.succ_pos n)
  have : HasExt.{u + 1} (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O)) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _
  exact
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
    (SpacesEtale.topology B S hS Y) _ U n M h

end AlgebraicGeometry.Space

/-! ### Derived pullback along a morphism with exact pullback -/

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w

variable {X Y : AlgebraicGeometry.RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **For an exact pullback, `Lf^*` is the functor `f^*` induces on derived categories.** -/
def derivedPullbackIsoMapDerivedCategoryOfExact :
    derivedPullback f ≅ f.pullbackTopos.mapDerivedCategory :=
  Stacks.Homology.leftDerivedIsoMapDerivedCategory f.pullbackTopos (derivedPullback f)
    (derivedPullbackComparison f)

/-- **For an exact pullback, `H^q(Lf^* K) ≅ f^* H^q(K)`, naturally in `K`.** -/
def derivedPullbackHomologyIsoOfExact (q : ℤ) :
    derivedPullback f ⋙ DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ f.pullbackTopos :=
  Functor.isoWhiskerRight (derivedPullbackIsoMapDerivedCategoryOfExact f) _ ≪≫
    f.pullbackTopos.mapDerivedCategoryHomologyIso q

/-- **For an exact pullback, `Lf^*(M[n]) ≅ (f^*M)[n]`, naturally in `M`.** -/
def derivedPullbackSingleIsoOfExact (n : ℤ) :
    DerivedCategory.singleFunctor _ n ⋙ derivedPullback f ≅
      f.pullbackTopos ⋙ DerivedCategory.singleFunctor _ n :=
  Functor.isoWhiskerLeft _ (derivedPullbackIsoMapDerivedCategoryOfExact f) ≪≫
    f.pullbackTopos.mapDerivedCategorySingleFunctor n

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- For an exact pullback, `Lf^*` carries a morphism invertible on `H^q` to one. -/
theorem isIso_homologyMap_derivedPullback_map_of_exact {K L : DerivedCategory
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (g : K ⟶ L) (q : ℤ)
    (hg : IsIso ((DerivedCategory.homologyFunctor _ q).map g)) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map ((derivedPullback f).map g)) := by
  have h := (derivedPullbackHomologyIsoOfExact f q).hom.naturality g
  simp only [Functor.comp_map] at h
  rw [← isIso_comp_right_iff _ ((derivedPullbackHomologyIsoOfExact f q).hom.app L), h]
  infer_instance

section Pushforward

omit [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

variable [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`H^p(Rf_*(M[0]))` is the classical `R^pf_*M`**, so it vanishes when the latter does. -/
theorem isZero_homology_derivedPushforward_single_of_isZero_rightDerived
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℕ)
    (h : IsZero ((f.pushforwardTopos.rightDerived p).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
      ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  IsZero.of_iso h
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived f.pushforwardTopos
      (derivedPushforward f) (derivedPushforwardUnit f) (exists_quasiIso_isKInjective X) p).app M)

end Pushforward

section Counit

variable [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **The counit of `Lf^* ⊣ Rf_*` is invertible at every object whose cohomology satisfies `P`**,
for an exact pullback, as soon as it is so at modules satisfying `P` placed in one degree and
`Rf_*` keeps `D^{≤ c}` on objects whose cohomology satisfies `P`. -/
theorem isIso_derivedPullbackPushforwardAdjunctionOfExact_counit_app_of_homologyIn
    (P : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [P.IsClosedUnderIsomorphisms]
    (hε : ∀ M, P M → ∀ n : ℤ, IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((DerivedCategory.singleFunctor _ n).obj M)))
    (hGLE : ∀ Y, Stacks.DerivedCategory.AdjunctionUnitTruncations.HomologyIn P Y → ∀ c : ℤ,
      Y.IsLE c → ((derivedPushforward f).obj Y).IsLE c)
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : Stacks.DerivedCategory.AdjunctionUnitTruncations.HomologyIn P K) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) := by
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardTopos
      (derivedPushforward f) (derivedPushforwardUnit f)
  have _ : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact f)
  exact Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_counit_app_of_homologyIn
    (derivedPullbackPushforwardAdjunctionOfExact f) P hε
    (fun g q hg ↦ isIso_homologyMap_derivedPullback_map_of_exact f g q hg)
    (fun Y n hY ↦ Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj f Y n hY)
    hGLE K hK

end Counit

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace AlgebraicGeometry.BigFppfSpaceSite

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

attribute [local instance] Space.enoughInjectives_spacesEtaleModules

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces} (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ X)

/-- The final object `affinePoint` is the image of an affine chart. -/
theorem affinePoint_mem_affineChartImages :
    affinePoint T V₀ hV₀ e ∈ Space.SpacesEtale.affineChartImages T.schemeSite S T.scheme_mem X :=
  ⟨Space.representingChart T.schemeSite S T.scheme_mem X V₀
      ((ObjectProperty.ι _).mapIso e.symm), hV₀,
    ⟨(isTerminal_affinePoint T V₀ hV₀ e).uniqueUpToIso
      (Space.isTerminal_comparisonFunctor_representingChart T.schemeSite S T.scheme_mem X V₀
        ((ObjectProperty.ι _).mapIso e.symm))⟩⟩

/-- **`R^q p_* 𝓕 = H^q(X, 𝓕) = 0` for `q > 0` and `𝓕` quasi-coherent.** -/
theorem isZero_rightDerived_affinePointHom_pushforward
    (M : SheafOfModules.{u + 1} (spacesEtaleRing T X)) (hM : M.IsQuasicoherentOnSite)
    (p : ℕ) (hp : 0 < p) :
    haveI := RingedSite.Hom.pushforwardTopos_additive
      (RingedSite.toGlobalPoint (X := Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
        (isTerminal_affinePoint T V₀ hV₀ e))
    IsZero (((affinePointHom T V₀ hV₀ e).pushforwardTopos.rightDerived p).obj M) := by
  have := RingedSite.globalPointFunctor_isContinuous
    (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) (affinePoint T V₀ hV₀ e)
  have : (SheafOfModules.pushforward.{u + 1} (F := RingedSite.globalPointFunctor
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) (affinePoint T V₀ hV₀ e))
      (affinePointHom T V₀ hV₀ e).fSharpRing).Additive :=
    ⟨by intros; rfl⟩
  exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (RingedSite.globalPointFunctor (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
      (affinePoint T V₀ hV₀ e)) (spacesEtaleRing T X)
    (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.globalPoint
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) (affinePoint T V₀ hV₀ e)).O)
    (affinePointHom T V₀ hV₀ e).fSharpRing p M
    (fun V ↦ ⟨⊤, by rw [Sieve.generate_top]; exact GrothendieckTopology.top_mem _ V,
      fun _ _ _ ↦
        Space.isZero_rightDerived_evaluation_spacesEtale_of_isQuasicoherentOnSite _ _ _ _ M hM _
          (affinePoint_mem_affineChartImages T V₀ hV₀ e) p hp⟩)

/-! ### `Lp^* ⊣ Rp_*` at objects placed in one degree -/

section Derived

/-- The direct image along `p` is additive. -/
instance affinePointHom_pushforwardTopos_additive :
    (affinePointHom T V₀ hV₀ e).pushforwardTopos.Additive :=
  RingedSite.Hom.pushforwardTopos_additive
    (RingedSite.toGlobalPoint (X := Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
      (isTerminal_affinePoint T V₀ hV₀ e))

/-- `Lp^*` exists, `p^*` being exact. -/
instance affinePointHom_hasLeftDerivedFunctor :
    (pullbackOnHomotopy (affinePointHom T V₀ hV₀ e)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact (affinePointHom T V₀ hV₀ e)

/-- **`Lp^* ⊣ Rp_*`.** -/
abbrev affinePointDerivedAdjunction :=
  derivedPullbackPushforwardAdjunctionOfExact (affinePointHom T V₀ hV₀ e)



/-- **`H^q(Rp_*(𝓕[0])) = 0` for `q > 0` and `𝓕` quasi-coherent.** -/
theorem isZero_homology_affinePointHom_derivedPushforward_single
    (M : SheafOfModules.{u + 1} (spacesEtaleRing T X)) (hM : M.IsQuasicoherentOnSite)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
      ((derivedPushforward (affinePointHom T V₀ hV₀ e)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  isZero_homology_derivedPushforward_single_of_isZero_rightDerived (affinePointHom T V₀ hV₀ e) M p
    (isZero_rightDerived_affinePointHom_pushforward T V₀ hV₀ e M hM p hp)

/-- **The derived unit `M[0] ⟶ Rp_* Lp^*(M[0])` is invertible** for every module `M` on the
point. -/
theorem isIso_affinePointDerivedAdjunction_unit_app_single
    (N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.globalPoint (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
        (affinePoint T V₀ hV₀ e)).O)) :
    IsIso ((affinePointDerivedAdjunction T V₀ hV₀ e).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  have := isIso_affinePointHom_unit T V₀ hV₀ e
  refine isIso_derivedUnit_app_singleFunctor_obj_of_isZero (affinePointHom T V₀ hV₀ e) N
    inferInstance (fun p hp ↦ ?_)
  exact (isZero_homology_affinePointHom_derivedPushforward_single T V₀ hV₀ e _
    (isQuasicoherentOnSite_affinePointHom_pullbackTopos_obj T V₀ hV₀ e N) p hp).of_iso
    ((DerivedCategory.homologyFunctor _ (p : ℤ)).mapIso
      ((derivedPushforward (affinePointHom T V₀ hV₀ e)).mapIso
        ((derivedPullbackSingleIsoOfExact (affinePointHom T V₀ hV₀ e) 0).app N)))

/-- **The derived unit `M[n] ⟶ Rp_* Lp^*(M[n])` is invertible** for every module `M` on the point
and every `n`. -/
theorem isIso_affinePointDerivedAdjunction_unit_app_singleFunctor
    (N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.globalPoint (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
        (affinePoint T V₀ hV₀ e)).O)) (n : ℤ) :
    IsIso ((affinePointDerivedAdjunction T V₀ hV₀ e).unit.app
      ((DerivedCategory.singleFunctor _ n).obj N)) := by
  have := isIso_affinePointDerivedAdjunction_unit_app_single T V₀ hV₀ e N
  have := Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift
    (affinePointHom T V₀ hV₀ e)
  have : IsIso ((affinePointDerivedAdjunction T V₀ hV₀ e).unit.app
      (((DerivedCategory.singleFunctors _).functor 0 ⋙ shiftFunctor _ (-n)).obj N)) :=
    Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_shift
      _ (affinePointDerivedAdjunction T V₀ hV₀ e) ((DerivedCategory.singleFunctor _ 0).obj N) (-n)
  exact Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_of_iso
    (affinePointDerivedAdjunction T V₀ hV₀ e)
    (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app N).symm

/-- **The derived counit `Lp^* Rp_*(𝓕[n]) ⟶ 𝓕[n]` is invertible** for every quasi-coherent `𝓕`
and every `n`. -/
theorem isIso_affinePointDerivedAdjunction_counit_app_singleFunctor
    (N : SheafOfModules.{u + 1} (spacesEtaleRing T X)) (hN : N.IsQuasicoherentOnSite) (n : ℤ) :
    IsIso ((affinePointDerivedAdjunction T V₀ hV₀ e).counit.app
      ((DerivedCategory.singleFunctor _ n).obj N)) := by
  let adj := affinePointDerivedAdjunction T V₀ hV₀ e
  let M := (affinePointHom T V₀ hV₀ e).pushforwardTopos.obj N
  have := isIso_affinePointDerivedAdjunction_unit_app_singleFunctor T V₀ hV₀ e M n
  have hc : IsIso (adj.counit.app ((derivedPullback (affinePointHom T V₀ hV₀ e)).obj
      ((DerivedCategory.singleFunctor _ n).obj M))) := by
    have h := adj.left_triangle_components ((DerivedCategory.singleFunctor _ n).obj M)
    rw [← isIso_comp_left_iff ((derivedPullback (affinePointHom T V₀ hV₀ e)).map
      (adj.unit.app ((DerivedCategory.singleFunctor _ n).obj M))), h]
    exact IsIso.id _
  have := isIso_affinePointHom_counit_app T V₀ hV₀ e N hN
  refine Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_counit_app_of_iso_of_isIso adj
    ((DerivedCategory.singleFunctor _ n).mapIso
        (asIso
          ((affinePointHom T V₀ hV₀ e).pullbackPushforwardAdjunctionTopos.counit.app N)).symm ≪≫
      ((derivedPullbackSingleIsoOfExact (affinePointHom T V₀ hV₀ e) n).app M).symm) hc

end Derived

end AlgebraicGeometry.BigFppfSpaceSite

end
