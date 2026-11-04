module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiAffine
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiOpenSquare
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso

/-!
# `Lf^*` and the unit of `Lf^* ⊣ Rf_*` for the morphism of 070U, by restriction to affine opens

Let `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of [Stacks, Tag 070U] on a chosen big site
and `K` an object of `D_QCoh(S)`, represented by a K-flat complex `P` with flat terms
([Stacks, Tag 06YS]), so that `Lf^*K` is represented by `f^*P` ([Stacks, Tag 06YY]). Both
assertions of [Stacks, Tag 070W] about `Lf^*` are local on `S`, and are checked here over the
affine opens `g : Spec A ⟶ S`:

* adequacy of `Hⁱ(f^*P)` can be tested on its restrictions to the big sites over the `Spec A`
  ([Stacks, Tag 06VK]); the restriction is `Hⁱ(f_A^*(P|_{Spec A}))`, by the commutation
  `j^* f^* ≅ f_A^* g^*`, and `P|_{Spec A}` is again K-flat with flat terms
  ([Stacks, Tag 0G7E]) with quasi-coherent cohomology, so this is the affine case;
* the unit is the complex map `P ⟶ f_*f^*P ⟶ f_*I` for a K-injective resolution `f^*P ⟶ I`, its
  invertibility on cohomology sheaves is local on `S`, and over `Spec A` it is, up to the base
  change isomorphisms of the open square, the unit over `Spec A` at `P|_{Spec A}` computed with the
  K-injective resolution `I|_{Spec A}` ([Stacks, Tag 08FI]), which is the affine case.

## Main results

* `Stacks.Adequate.BigSite.isAdequate_homology_derivedZariskiPullback`: `Lf^*` carries
  `D_QCoh(S)` into `D_Adeq(𝒪)`.
* `Stacks.Adequate.BigSite.isIso_derivedZariskiAdjunction_unit_app`: the unit of the derived
  adjunction is invertible on `D_QCoh(S)`.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {τ : CoveringTopology} (𝒮 : AlgebraicGeometry.BigSite.{u} τ) {S T : Scheme.{u}}
  (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮) (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮)
  (g : T ⟶ S) [IsOpenImmersion g]

/-! ### Exactness of restriction to an open subscheme -/

/-- The pullback of modules along the open immersion `g`, on the small Zariski sites, is
additive. -/
instance additive_zariskiOpenPullback : (zariskiOpenHom g).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (zariskiOpenHom g)

/-- The pullback of modules along `g` preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_zariskiOpenPullback :
    PreservesFiniteColimits (zariskiOpenHom g).toModulesHom.pullbackModules :=
  have := (RingedToposHom.pullbackAdjPushforwardModules
    (zariskiOpenHom g)).leftAdjoint_preservesColimits.{0, 0}
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The pullback of modules along `g` preserves finite limits: it is isomorphic to restriction to
the open subscheme `T`, a pushforward. -/
instance preservesFiniteLimits_zariskiOpenPullback :
    PreservesFiniteLimits (zariskiOpenHom g).toModulesHom.pullbackModules :=
  have : PreservesFiniteLimits (zariskiOpenRestrictFunctor g) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  preservesFiniteLimits_of_natIso (zariskiOpenPullbackIso g).symm

/-! ### K-flat models -/

/-- Every object of `D(𝒪_S)` is the class of a K-flat complex with flat terms
([Stacks, Tag 06YS]). -/
theorem exists_isKFlat_model (X : Scheme.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O))]
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O))) :
    ∃ P : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)) ℤ,
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := X.zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P) ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  obtain ⟨N, hN, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := X.zariskiRingedSite.toRingedTopos) (DerivedCategory.Qh.objPreimage K)
  have hs' : IsIso (DerivedCategory.Qh.map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
  exact ⟨N.as, hN, ⟨@asIso _ _ _ _ (DerivedCategory.Qh.map s) hs' ≪≫
    DerivedCategory.Qh.objObjPreimageIso K⟩⟩

/-! ### `Lf^*` restricted to an affine open -/

/-- The comparison of the pullback of a complex to the big site over `S`, restricted to the big
site over `T`, with the pullback to the big site over `T` of its restriction to `T`. -/
def openSquarePullbackComplexHom
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ) :
    ((BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.toModulesHom.pullbackModules
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
          |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f n := (openSquarePullbackHom 𝒮 hS hT g).app (P.X n)
  comm' i j _ := ((openSquarePullbackHom 𝒮 hS hT g).naturality (P.d i j)).symm

/-- The comparison `Stacks.Adequate.openSquarePullbackComplexHom` is an isomorphism, since it is
one in every degree. -/
instance isIso_openSquarePullbackComplexHom
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ) :
    IsIso (openSquarePullbackComplexHom 𝒮 hS hT g P) := by
  have : ∀ n, IsIso ((openSquarePullbackComplexHom 𝒮 hS hT g P).f n) := fun n ↦
    NatIso.isIso_app_of_isIso (openSquarePullbackHom 𝒮 hS hT g) (P.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The pullback of a complex to the big site over `S`, restricted to the big site over `T`, is
the pullback to the big site over `T` of its restriction to `T`. -/
def openSquarePullbackComplexIso
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ) :
    ((BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.toModulesHom.pullbackModules
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      ((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
          |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  asIso (openSquarePullbackComplexHom 𝒮 hS hT g P)

/-- **Adequacy of `Hⁱ(Lf^*K)` over an affine open.** Let `P` be a K-flat complex with flat terms
and quasi-coherent cohomology. The restriction to the big site over an affine open `Spec A` of
the cohomology of `f^*P` is the cohomology of `f_A^*(P|_{Spec A})`, which is adequate by the affine
case. -/
theorem isAdequate_openRestrict_homology {A : CommRingCat.{u}}
    (hT : (Spec A).size < AlgebraicGeometry.cutoff τ 𝒮) (g : Spec A ⟶ S) [IsOpenImmersion g]
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := S.zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P))
    (hPq : ∀ n, SheafOfModules.isQuasicoherent S.ringCatSheaf (P.homology n)) (i : ℤ) :
    IsAdequate.{u, u} (BigSite.ofAmbient 𝒮 (Spec A) hT) ((openRestrict 𝒮 hS hT g).obj
      ((((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology i)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (BigSite.ofAmbient 𝒮 (Spec A) hT).ringedSite.toRingedTopos.O))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (Spec A).ringCatSheaf)
  let r := zariskiOpenHom g
  let P' := (r.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP' : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := (Spec A).zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P') :=
    Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy r _ hP
  let E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P')
  have hE : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) n).obj
          E) := by
    intro n
    have : (P.homology n).IsQuasicoherent := hPq n
    exact (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
      (((Stacks.Homology.exactHomologyIso r.toModulesHom.pullbackModules n).app P ≪≫
          (zariskiOpenPullbackIso g).app (P.homology n)).symm ≪≫
        ((HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app P').symm ≪≫
        ((DerivedCategory.homologyFunctorFactorsh _ n).app _).symm)
      (Scheme.Modules.isQuasicoherent_restrictFunctor g (P.homology n))
  have hL := (BigSite.ofAmbient 𝒮 (Spec A) hT).isAdequate_homology_derivedZariskiPullback_of_affine
    E hE i
  let d := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback
    (BigSite.ofAmbient 𝒮 (Spec A) hT).zariskiRingedToposHom
  have hc : IsIso (d.comparison.app ((HomotopyCategory.quotient _ _).obj P')) :=
    d.isIso_comparison _ hP'
  exact (adequate.{u, u} _).prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 (Spec A) hT).ringedSite.toRingedTopos.O)) i).mapIso
        (@asIso _ _ _ _ (d.comparison.app ((HomotopyCategory.quotient _ _).obj P')) hc ≪≫
          (DerivedCategory.quotientCompQhIso _).app _) ≪≫
      (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (BigSite.ofAmbient 𝒮 (Spec A) hT).ringedSite.toRingedTopos.O)) i).app _ ≪≫
      (HomologicalComplex.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (BigSite.ofAmbient 𝒮 (Spec A) hT).ringedSite.toRingedTopos.O))
          (ComplexShape.up ℤ) i).mapIso
        (openSquarePullbackComplexIso 𝒮 hS hT g P) ≪≫
      (Stacks.Homology.exactHomologyIso (openRestrict 𝒮 hS hT g) i).app _) hL

/-- The affine open cover of `S`, as a jointly surjective family. -/
theorem iUnion_range_affineOpenCover (X : Scheme.{u}) :
    (⋃ j : ULift.{u + 1} X.affineOpenCover.I₀, Set.range (X.affineOpenCover.f j.down)) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨i, y, hy⟩ := X.affineOpenCover.openCover.exists_eq x
  exact Set.mem_iUnion.mpr ⟨⟨i⟩, y, hy⟩

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W]: `Lf^*` carries `D_QCoh(S)` into `D_Adeq(𝒪)`**, for the morphism `f` of
[Stacks, Tag 070U] on a chosen big site. On a K-flat model `P` of `K` with flat terms, `Lf^*K` is
`f^*P`; adequacy of its cohomology is local on `S`, and over an affine open it is the affine
case, `Stacks.Adequate.BigSite.isAdequate_homology_derivedZariskiPullback_of_affine`. -/
theorem BigSite.isAdequate_homology_derivedZariskiPullback (B : BigSite τ S)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)))
    (hK : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (i : ℤ) :
    IsAdequate.{u, u} B ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) i).obj
        (B.derivedZariskiPullback.obj K)) := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isKFlat_model S K
  have hPq : ∀ n, SheafOfModules.isQuasicoherent S.ringCatSheaf (P.homology n) := fun n ↦
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactorsh _ n).app _ ≪≫
        (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app P) (hK n)
  let f := (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom
  let d := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback f
  have hc : IsIso (d.comparison.app ((HomotopyCategory.quotient _ _).obj P)) :=
    d.isIso_comparison _ hP
  have hX := isAdequate_of_openRestrict 𝒮 hS
    (fun j : ULift.{u + 1} S.affineOpenCover.I₀ ↦ Spec (S.affineOpenCover.X j.down))
    (fun j ↦ Scheme.size_lt_of_isOpenImmersion (S.affineOpenCover.f j.down) hS)
    (fun j ↦ S.affineOpenCover.f j.down) (iUnion_range_affineOpenCover S) _
    (fun j ↦ isAdequate_openRestrict_homology 𝒮 hS _ (S.affineOpenCover.f j.down) P hP hPq i)
  exact (adequate.{u, u} _).prop_of_iso
    (((DerivedCategory.homologyFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) i).mapIso
        ((BigSite.ofAmbient 𝒮 S hS).derivedZariskiPullback.mapIso e.symm ≪≫
          @asIso _ _ _ _ (d.comparison.app ((HomotopyCategory.quotient _ _).obj P)) hc ≪≫
          (DerivedCategory.quotientCompQhIso _).app _) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _).symm) hX

/-! ### The unit restricted to an affine open -/

/-- The base change transformation of the open square, applied degreewise to a complex. -/
def openSquareBaseChangeComplex
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) ℤ) :
    ((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ⟶
      ((BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f n := (openSquareBaseChange 𝒮 hS hT g).app (I.X n)
  comm' i j _ := ((openSquareBaseChange 𝒮 hS hT g).naturality (I.d i j)).symm

/-- The base change transformation of the open square, applied degreewise to a complex, is an
isomorphism, since it is one in every degree. -/
instance isIso_openSquareBaseChangeComplex
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) ℤ) :
    IsIso (openSquareBaseChangeComplex 𝒮 hS hT g I) := by
  have : ∀ n, IsIso ((openSquareBaseChangeComplex 𝒮 hS hT g I).f n) := fun n ↦
    isIso_openSquareBaseChange_app 𝒮 hS hT g (I.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

omit [IsOpenImmersion g] in
/-- **The restriction of the unit to `T` is the unit over `T`**, at the level of complexes: for a
complex `P` of `𝒪_S`-modules and `s : f^*P ⟶ I`, restricting `P ⟶ f_*f^*P ⟶ f_*I` to `T` and
following it with the base change isomorphism is the unit `P|_T ⟶ f_{T,*}f_T^*(P|_T)` followed
by `f_{T,*}` of `f_T^*(P|_T) ≅ (f^*P)|_T ⟶ I|_T`. -/
theorem openSquare_unitComplex
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ)
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) ℤ)
    (s : (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶ I) :
    ((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((BigSite.ofAmbient 𝒮 S hS).zariskiUnitComplex P ≫
          ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).map s) ≫ openSquareBaseChangeComplex 𝒮 hS hT g I =
      (BigSite.ofAmbient 𝒮 T hT).zariskiUnitComplex
          (((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (openSquarePullbackComplexHom 𝒮 hS hT g P ≫
            ((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have h₁ := (openSquareBaseChange 𝒮 hS hT g).naturality (s.f n)
  have h₂ := openSquare_unit 𝒮 hS hT g (P.X n)
  simp only [Functor.comp_map] at h₁
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Functor.map_comp,
    Category.assoc, openSquareBaseChangeComplex, BigSite.zariskiUnitComplex,
    openSquarePullbackComplexHom]
  rw [h₁]
  exact (reassoc_of% h₂) _

/-- **The unit of `Lf^* ⊣ Rf_*`, restricted to an affine open, is a quasi-isomorphism.** Let `P`
be a K-flat complex with flat terms and quasi-coherent cohomology, and `s : f^*P ⟶ I` a
quasi-isomorphism to a K-injective complex. Over an affine open `Spec A` the complex map
`P ⟶ f_*f^*P ⟶ f_*I` restricts, up to the base change isomorphism, to the unit over `Spec A`
followed by `f_{A,*}` of a K-injective resolution, which is a quasi-isomorphism by the affine
case. -/
theorem isIso_homologyMap_zariskiOpenPullback_unitComplex {A : CommRingCat.{u}}
    (hT : (Spec A).size < AlgebraicGeometry.cutoff τ 𝒮) (g : Spec A ⟶ S) [IsOpenImmersion g]
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := S.zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P))
    (hPq : ∀ n, SheafOfModules.isQuasicoherent S.ringCatSheaf (P.homology n))
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) ℤ)
    [I.IsKInjective]
    (s : (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶ I) (hs : QuasiIso s) (n : ℤ) :
    IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map
      (((zariskiOpenHom g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((BigSite.ofAmbient 𝒮 S hS).zariskiUnitComplex P ≫
          ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).map s))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (BigSite.ofAmbient 𝒮 (Spec A) hT).ringedSite.toRingedTopos.O))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (Spec A).ringCatSheaf)
  let r := zariskiOpenHom g
  let P' := (r.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP' : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := (Spec A).zariskiRingedSite.toRingedTopos) ((HomotopyCategory.quotient _ _).obj P') :=
    Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy r _ hP
  have hE : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Spec A).zariskiRingedSite.toRingedTopos.O)) n).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P'))) := by
    intro n
    have : (P.homology n).IsQuasicoherent := hPq n
    exact (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
      (((Stacks.Homology.exactHomologyIso r.toModulesHom.pullbackModules n).app P ≪≫
          (zariskiOpenPullbackIso g).app (P.homology n)).symm ≪≫
        ((HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app P').symm ≪≫
        ((DerivedCategory.homologyFunctorFactorsh _ n).app _).symm)
      (Scheme.Modules.isQuasicoherent_restrictFunctor g (P.homology n))
  have : CochainComplex.IsKInjective
      (((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_openRestrict 𝒮 hS hT g I
  have := hs
  have hs' : QuasiIso (openSquarePullbackComplexHom 𝒮 hS hT g P ≫
      ((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
    inferInstance
  have hU := ((BigSite.ofAmbient 𝒮 (Spec A) hT).isIso_derivedZariskiAdjunction_unit_iff P' hP' _
    _ hs').1 ((BigSite.ofAmbient 𝒮 (Spec A) hT).isIso_derivedZariskiAdjunction_unit_app_of_affine
      _ hE)
  have key := openSquare_unitComplex 𝒮 hS hT g P I s
  have h₁ : IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map
      ((r.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((BigSite.ofAmbient 𝒮 S hS).zariskiUnitComplex P ≫
          ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).map s) ≫ openSquareBaseChangeComplex 𝒮 hS hT g I)) := by
    rw [key]
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  rw [Functor.map_comp] at h₁
  exact IsIso.of_isIso_comp_right _
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map
      (openSquareBaseChangeComplex 𝒮 hS hT g I))

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W]: the unit of `Lf^* ⊣ Rf_*` is invertible on `D_QCoh(S)`**, for the
morphism `f` of [Stacks, Tag 070U] on a chosen big site; that is, `Rf_* Lf^* ≅ id` there. On a
K-flat model `P` of `K` with flat terms and a K-injective resolution `f^*P ⟶ I`, the unit is the
complex map `P ⟶ f_*f^*P ⟶ f_*I`, whose invertibility on cohomology sheaves is local on `S`; over
an affine open it is the affine case. -/
theorem BigSite.isIso_derivedZariskiAdjunction_unit_app (B : BigSite τ S)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)))
    (hK : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K) :
    IsIso (B.derivedZariskiAdjunction.unit.app K) := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isKFlat_model S K
  have hPq : ∀ n, SheafOfModules.isQuasicoherent S.ringCatSheaf (P.homology n) := fun n ↦
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactorsh _ n).app _ ≪≫
        (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app P) (hK n)
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  let X := (((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules
    |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  obtain ⟨I, hI, ⟨e'⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X))
  have := hI
  obtain ⟨t, ht⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X) I).2 e'.inv
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective t
  have h0 : IsIso
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    ht ▸ Iso.isIso_inv e'
  have hs : QuasiIso s :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 ((DerivedCategory.isIso_Qh_map_iff _).1 h0)
  refine ((BigSite.ofAmbient 𝒮 S hS).isIso_derivedZariskiAdjunction_unit_iff P hP I s hs).2 ?_
  refine (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 ?_
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ (fun j ↦ S.affineOpenCover.f j)
    (fun x ↦ S.affineOpenCover.openCover.exists_eq x) fun j ↦ ?_
  have h := isIso_homologyMap_zariskiOpenPullback_unitComplex 𝒮 hS
    (Scheme.size_lt_of_isOpenImmersion (S.affineOpenCover.f j) hS) (S.affineOpenCover.f j) P hP
    hPq I s hs n
  have h' := (NatIso.isIso_map_iff (Stacks.Homology.exactHomologyIso
    (zariskiOpenHom (S.affineOpenCover.f j)).toModulesHom.pullbackModules n) _).1 h
  exact (NatIso.isIso_map_iff (zariskiOpenPullbackIso (S.affineOpenCover.f j)) _).1 h'

end Stacks.Adequate

end
