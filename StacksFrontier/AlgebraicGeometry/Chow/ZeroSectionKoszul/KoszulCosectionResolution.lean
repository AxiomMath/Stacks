module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.ExteriorPowerResolution
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.KoszulCosection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex of a cosection resolving a closed subscheme

Let `Y` be a scheme, `ℰ` an `𝒪_Y`-module, `φ : ℰ ⟶ 𝒪_Y` a cosection and `i : Z ⟶ Y` a closed
immersion. This file gives a criterion, checked on stalks, for the Koszul complex

  `⋯ ⟶ ⋀²ℰ ⟶ ℰ ⟶ 𝒪_Y`

of `φ` to be a resolution of `i_*𝒪_Z`, and packages the conclusion as a representation of
`i_*𝒪_Z ∈ D(𝒪_Y)` by the exterior powers of `ℰ` in the sense of
`Stacks.Chow.ExteriorPowerResolution`. Write `ψ_x : ℰ_x ⟶ 𝒪_{Y,x}` for the stalk of `φ`. The
criterion asks:

* exactness in positive degrees, at every point: either `ψ_x` takes the value `1`, or `ℰ_x` has
  a basis on which `ψ_x` is a Koszul-regular sequence;
* in degree zero, at every point: the image of `ψ_x` is the stalk of the ideal sheaf of `Z`,
  i.e. a germ of a function lies in the image of `ψ_x` exactly when its image in `i_*𝒪_Z`
  vanishes near `x`.

The second condition says that `𝒪_Y ⟶ i_*𝒪_Z` is a cokernel of `φ` on stalks, hence a cokernel
(Stacks Tag 01AG); the first is exactness of the stalk Koszul complexes
(`AlgebraicGeometry.Scheme.Modules.koszulChainComplex_exactAt_succ_of_forall`). A chain complex
in nonnegative homological degrees augmented to an object and exact there is a resolution of it,
and reindexing cohomologically puts `⋀ⁿℰ` in degree `-n`.

## Main definitions

* `Stacks.Chow.ExteriorPowerResolution.ofKoszul`: the resolution by exterior powers obtained
  from an exact augmented Koszul complex.
* `Stacks.Chow.ExteriorPowerResolution.ofClosedImmersion`: the resolution of `i_*𝒪_Z` from the
  stalkwise criterion.

## Main results

* `Stacks.Chow.quasiIso_koszulAugmentation`: an augmentation of the Koszul complex, exact in
  degree zero and onto, with the complex exact in positive degrees, is a quasi-isomorphism.
* `Stacks.Chow.exact_unitToPushforwardUnit`: the degree-zero criterion.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {Y : Scheme.{u}} {ℰ : Y.Modules} {φ : ℰ ⟶ SheafOfModules.unit Y.ringCatSheaf}

/-! ### An augmented Koszul complex is a resolution -/

section Augmentation

variable {F : Y.Modules} (ε : exteriorPower ℰ ((0 : ℕ) : ℤ) ⟶ F)
  (hε : koszulDifferential ℰ φ 0 ≫ ε = 0)

/-- The augmentation `K(φ) ⟶ F[0]` of the Koszul complex given by a morphism `⋀⁰ℰ ⟶ F` killing
the image of the first differential. -/
def koszulAugmentation : koszulChainComplex ℰ φ ⟶
    (HomologicalComplex.single Y.Modules (ComplexShape.down ℕ) 0).obj F :=
  HomologicalComplex.mkHomToSingle (K := koszulChainComplex ℰ φ) ε (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    rw [koszulChainComplex_d]
    exact hε)

include hε in
/-- **An exact augmentation of the Koszul complex is a quasi-isomorphism.** If
`⋀¹ℰ ⟶ ⋀⁰ℰ ⟶ F ⟶ 0` is exact and the Koszul complex is exact in positive degrees, then the
augmentation `K(φ) ⟶ F[0]` is a quasi-isomorphism. -/
theorem quasiIso_koszulAugmentation
    (hex : (ShortComplex.mk (koszulDifferential ℰ φ 0) ε hε).Exact) (hepi : Epi ε)
    (hK : ∀ n : ℕ, (koszulChainComplex ℰ φ).ExactAt (n + 1)) :
    QuasiIso (koszulAugmentation ε hε) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · have hf : (koszulAugmentation ε hε).f 0 =
          ε ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 F).inv :=
        HomologicalComplex.mkHomToSingle_f _ _
      refine ⟨?_, ?_⟩
      · refine (ShortComplex.exact_iff_of_iso ?_).2 hex
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 F) ?_ ?_
        · change 𝟙 _ ≫ koszulDifferential ℰ φ 0 = (koszulChainComplex ℰ φ).d 1 0 ≫ 𝟙 _
          rw [Category.comp_id, Category.id_comp]
          exact (koszulChainComplex_d ℰ φ 0).symm
        · change 𝟙 _ ≫ ε = (koszulAugmentation ε hε).f 0 ≫ _
          simp [hf]
          rfl
      · change Epi ((koszulAugmentation ε hε).f 0)
        exact hf ▸ epi_comp ε _
    · exact (koszulChainComplex ℰ φ).shape 0 0 (by simp)
    · rfl
    · rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact hK n
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (Nat.succ_ne_zero n)

/-- **The resolution by exterior powers given by an exact augmented Koszul complex.** The Koszul
complex of `φ`, reindexed cohomologically so that `⋀ⁿℰ` sits in degree `-n`, represents
`F ∈ D(𝒪_Y)` as soon as `⋀¹ℰ ⟶ ⋀⁰ℰ ⟶ F ⟶ 0` is exact and the Koszul complex is exact in
positive degrees. -/
def ExteriorPowerResolution.ofKoszul
    (hex : (ShortComplex.mk (koszulDifferential ℰ φ 0) ε hε).Exact) (hepi : Epi ε)
    (hK : ∀ n : ℕ, (koszulChainComplex ℰ φ).ExactAt (n + 1)) :
    ExteriorPowerResolution ((DerivedCategory.singleFunctor Y.Modules 0).obj F) ℰ where
  complex := (koszulChainComplex ℰ φ).extend ComplexShape.embeddingDownNat
  termIso n := (koszulChainComplex ℰ φ).extendXIso ComplexShape.embeddingDownNat (by simp)
  isZero_of_pos m hm := (koszulChainComplex ℰ φ).isZero_extend_X _ m fun i hi => by
    simp only [ComplexShape.embeddingDownNat_f] at hi
    omega
  iso := by
    have := quasiIso_koszulAugmentation ε hε hex hepi hK
    have : QuasiIso (HomologicalComplex.extendMap (koszulAugmentation ε hε)
        ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
    exact ⟨asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap (koszulAugmentation ε hε)
        ComplexShape.embeddingDownNat)) ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso _ F 0 0 (by simp)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app F).symm⟩

end Augmentation

/-! ### The cokernel of a cosection, on stalks -/

section ClosedImmersion

variable (φ) {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- **The degree-zero criterion.** If at every point the image of `ψ_x` is the set of germs of
functions whose image in `i_*𝒪_Z` vanishes near `x`, then `ℰ ⟶ 𝒪_Y ⟶ i_*𝒪_Z` is exact. -/
theorem exact_unitToPushforwardUnit
    (h : ∀ (x : Y) (U : Y.Opens) (hx : x ∈ U) (a : Γ(Y, U)),
      TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).val.presheaf U x hx
          ((ClosedImmersionCoherentImage.unitToPushforwardUnit i).val.app (Opposite.op U) a) = 0 ↔
        TopCat.Presheaf.germ Y.sheaf.obj U x hx a ∈ LinearMap.range (koszulStalkDual φ x)) :
    ∃ hφ : φ ≫ ClosedImmersionCoherentImage.unitToPushforwardUnit i = 0,
      (ShortComplex.mk φ _ hφ).Exact := by
  set M := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  set ε := ClosedImmersionCoherentImage.unitToPushforwardUnit i
  have hφ : φ ≫ ε = 0 := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    refine TopCat.Presheaf.section_ext ⟨M.val.presheaf, M.isSheaf⟩ U.unop _ _ fun x hx => ?_
    refine ((h x U.unop hx _).2 ⟨_, koszulStalkDual_germ φ x U.unop hx m⟩).trans ?_
    exact (map_zero _).symm
  refine ⟨hφ, ?_⟩
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact Y.ringCatSheaf
    (ShortComplex.mk φ ε hφ)).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact (PresheafOfModules.stalkMapL x φ.val) (PresheafOfModules.stalkMapL x ε.val)
  intro y
  obtain ⟨U, hx, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (SheafOfModules.unit Y.ringCatSheaf).val.presheaf y
  refine (Iff.of_eq (congrArg (fun z => z = 0)
    (PresheafOfModules.stalkMapL_germ x ε.val U hx a))).trans ?_
  refine (h x U hx a).trans ?_
  rw [← Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv_germ Y.sheaf x U hx a]
  exact exists_congr fun _ =>
    (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv Y.sheaf x).injective.eq_iff

/-- **The Koszul complex of a cosection resolving a closed subscheme.** For a closed immersion
`i : Z ⟶ Y` and a cosection `φ : ℰ ⟶ 𝒪_Y`, suppose that at every point `x` of `Y`

* either `ψ_x` takes the value `1`, or `ℰ_x` has a basis on which `ψ_x` is a Koszul-regular
  sequence, and
* the image of `ψ_x` consists of the germs of the functions whose image in `i_*𝒪_Z` vanishes near
  `x`.

Then the Koszul complex of `φ`, with `⋀ⁿℰ` in degree `-n`, represents `i_*𝒪_Z` in `D(𝒪_Y)`. -/
@[sga "6 III 1.1.2", sga "6 VIII 1.4" "partial"]
def ExteriorPowerResolution.ofClosedImmersion (r : ℕ)
    (hA : ∀ x : Y, (∃ e, koszulStalkDual φ x e = 1) ∨
      ∃ b : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)
          ↑(TopCat.Presheaf.stalk ℰ.val.presheaf x),
        Koszul.IsKoszulRegular fun j => koszulStalkDual φ x (b j))
    (hH : ∀ (x : Y) (U : Y.Opens) (hx : x ∈ U) (a : Γ(Y, U)),
      TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).val.presheaf U x hx
          ((ClosedImmersionCoherentImage.unitToPushforwardUnit i).val.app (Opposite.op U) a) = 0 ↔
        TopCat.Presheaf.germ Y.sheaf.obj U x hx a ∈ LinearMap.range (koszulStalkDual φ x)) :
    ExteriorPowerResolution ((DerivedCategory.singleFunctor Y.Modules 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ℰ :=
  let β := (SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit
  let ε := ClosedImmersionCoherentImage.unitToPushforwardUnit i
  let α := (SheafOfModules.algebras _ ℰ).exteriorGeneratorIso
  have hφ := (exact_unitToPushforwardUnit φ i hH).1
  have hex := (exact_unitToPushforwardUnit φ i hH).2
  have hkey : α.hom ≫ koszulDifferential ℰ φ 0 ≫ β.hom = φ :=
    (congrArg (· ≫ koszulDifferential ℰ φ 0 ≫ β.hom)
      (SheafOfModules.algebras _ ℰ).exteriorGeneratorIso_hom).trans
      (exteriorGenerator_comp_koszulDifferential_zero ℰ φ)
  have hd : koszulDifferential ℰ φ 0 ≫ β.hom = α.inv ≫ φ :=
    (Iso.inv_hom_id_assoc α _).symm.trans (congrArg (α.inv ≫ ·) hkey)
  have hε : koszulDifferential ℰ φ 0 ≫ β.hom ≫ ε = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ε) hd).trans
      ((Category.assoc _ _ _).trans ((congrArg (α.inv ≫ ·) hφ).trans comp_zero)))
  let e : ShortComplex.mk (koszulDifferential ℰ φ 0) (β.hom ≫ ε) hε ≅ ShortComplex.mk φ ε hφ :=
    ShortComplex.isoMk α.symm β (Iso.refl _) hd.symm (by simp)
  ExteriorPowerResolution.ofKoszul (β.hom ≫ ε) hε ((ShortComplex.exact_iff_of_iso e).2 hex)
    (@epi_comp _ _ _ _ _ β.hom inferInstance ε
      (ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i))
    (koszulChainComplex_exactAt_succ_of_forall φ hA)

end ClosedImmersion

end Stacks.Chow

end
