module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal

/-!
# Direct image along an affine morphism is t-exact and conservative

Let `f : W ⟶ Y` be an affine morphism of schemes.

*Conservativity.* If `M` is a quasi-coherent `𝒪_W`-module with `f_*M = 0`, then `M = 0`. The
inverse images of the affine opens of `Y` are affine opens of `W` covering it, the sections of
`f_*M` over an affine open `V` of `Y` are the sections of `M` over `f⁻¹V`, and a quasi-coherent
module on an affine scheme with no global sections vanishes.

*T-exactness.* If `E` is an object of `D(𝒪_W)` whose cohomology sheaves are quasi-coherent, then
`H^i(Rf_*E) ≅ f_*H^i(E)` for every `i`, with no boundedness hypothesis on `E`. Fix `i` and cut
`E` down to a single sheaf placed in degree `i` by the two canonical truncations, neither of which
changes `H^i(Rf_*-)`: from below because `Rf_*` does not raise cohomological degree on complexes
with quasi-coherent cohomology ([Stacks, Tag 08D5] part (2) for an affine morphism), from above
because `Rf_*` does not lower it. What is left is `τ_{≤ i}τ_{≥ i}E ≅ H^i(E)[-i]`, and on a
single quasi-coherent sheaf the higher direct images vanish ([Stacks, Tag 01XC]), so
`Rf_*(H^i(E)[-i]) = (f_*H^i(E))[-i]`.

Together the two give the vanishing criterion `H^i(Rf_*E) = 0 ↔ H^i(E) = 0`.

The remaining assertion of t-exactness — that the canonical comparison `f_*K ⟶ Rf_*K` is
invertible for a complex `K` of quasi-coherent modules — is
`AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom`, [Stacks, Tag 0G9N] for an
affine morphism, and is used here rather than reproved.

## Main results

All names below are in the namespace `Stacks.AlgebraicGeometry.AffinePushforwardTExactness`.

* `isZero_of_isZero_pushforward_of_isAffineHom` — `f_*` is conservative on quasi-coherent
  `𝒪_W`-modules.
* `derivedPushforwardSingleIso` and `homologyDerivedPushforwardSingleIso` — `(f_*M)[-n] ≅
  Rf_*(M[-n])` and `H^n(Rf_*(M[-n])) ≅ f_*M` for `M` quasi-coherent.
* `homologyDerivedPushforwardIso` — `H^i(Rf_*E) ≅ f_*H^i(E)`.
* `isZero_homology_derivedPushforward_iff` — `H^i(Rf_*E) = 0 ↔ H^i(E) = 0`.

## Implementation notes

*The model of the derived categories is pinned.* Every input — [Stacks, Tag 0G9N] and the two
bounds of [Stacks, Tag 08D5] for an affine morphism — is available only at
`CategoryTheory.HasDerivedCategory.standard`, so the statements below are read there as well, and
the category of modules is spelled `SheafOfModules (structureSheafRing W.toRingedSpace)`, which is
the spelling of those inputs. The instance is declared with priority `10000`: the import closure
contains the locally small instance `SheafOfModules.hasDerivedCategory` and at equal priority
instance search would pick that one, making the statements mention a model their inputs are not
stated at.

*Conservativity is stated twice.* `AlgebraicGeometry.Scheme.Modules W` and
`SheafOfModules (structureSheafRing W.toRingedSpace)` are definitionally equal but carry separately
declared instances which instance search does not cross, so the statement whose inputs are in the
first spelling is recorded there and transported once, by hand, to the second, where the derived
statements use it.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforwardTExactness

attribute [local instance 10000] HasDerivedCategory.standard

variable {W Y : Scheme.{u}}

/-! ### Conservativity of the direct image -/

/-- **The direct image along an affine morphism is conservative on quasi-coherent modules.** If
`f : W ⟶ Y` is affine and `M` is a quasi-coherent `𝒪_W`-module with `f_*M = 0`, then `M = 0`. -/
theorem isZero_of_isZero_pushforward_of_isAffineHom (f : W ⟶ Y) [IsAffineHom f] (M : W.Modules)
    (hM : M.IsQuasicoherent) (h : IsZero ((Scheme.Modules.pushforward f).obj M)) : IsZero M := by
  classical
  choose U hUaff hUmem _hUsub using fun w : W =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base w) (U := ⊤) trivial
  have hcover : ⨆ w : W, f ⁻¹ᵁ U w = ⊤ :=
    eq_top_iff.2 fun w _ => Opens.mem_iSup.2 ⟨w, hUmem w⟩
  refine TopDegreeBaseChange.isZero_of_isZero_restrict_cover
    (fun w : W => f ⁻¹ᵁ U w) hcover M fun w => ?_
  have : IsAffine (f ⁻¹ᵁ U w : Scheme) := (hUaff w).preimage f
  have hsec : IsZero ((SheafOfModules.evaluation Y.ringCatSheaf (op (U w))).obj
      ((Scheme.Modules.pushforward f).obj M)) := Functor.map_isZero _ h
  have himg : ((f ⁻¹ᵁ U w).ι ''ᵁ (⊤ : (f ⁻¹ᵁ U w : Scheme).Opens)) = f ⁻¹ᵁ U w := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  refine TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _
    (ModuleCat.isZero_iff_subsingleton.mpr ?_)
  show Subsingleton (M.val.obj (op ((f ⁻¹ᵁ U w).ι ''ᵁ (⊤ : (f ⁻¹ᵁ U w : Scheme).Opens))))
  rw [himg]
  exact (ModuleCat.isZero_iff_subsingleton.mp hsec :)

/-- **Conservativity of the direct image, in the spelling the derived statements use.** This is
`isZero_of_isZero_pushforward_of_isAffineHom` with the category of `𝒪_W`-modules spelled
`SheafOfModules (structureSheafRing W.toRingedSpace)`. -/
theorem isZero_of_isZero_modulePushforward_of_isAffineHom (f : W ⟶ Y) [IsAffineHom f]
    (M : SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) (hM : M.IsQuasicoherent)
    (h : IsZero ((modulePushforward f.toLRSHom.toShHom).obj M)) : IsZero M :=
  isZero_of_isZero_pushforward_of_isAffineHom f (M : W.Modules) hM h

/-! ### The derived direct image of a single quasi-coherent sheaf -/

/-- Every term of the complex `M[-n]` concentrated in degree `n` is quasi-coherent when `M` is:
the term in degree `n` is `M`, and the others are zero objects. -/
theorem isQuasicoherent_singleFunctor_obj_X (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) (hM : M.IsQuasicoherent) (k : ℤ) :
    (((CochainComplex.singleFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) n).obj M).X k).IsQuasicoherent := by
  have hP : (SheafOfModules.isQuasicoherent (structureSheafRing W.toRingedSpace)).ContainsZero :=
    containsZero_isQuasicoherent W
  by_cases hk : k = n
  · subst hk
    exact (SheafOfModules.isQuasicoherent (structureSheafRing W.toRingedSpace)).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k M).symm hM
  · exact (SheafOfModules.isQuasicoherent (structureSheafRing W.toRingedSpace)).prop_of_iso
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) n M k hk).isoZero.symm (ObjectProperty.prop_zero _)

/-- **The derived direct image of a quasi-coherent sheaf placed in one degree is its ordinary
direct image placed there**: `(f_*M)[-n] ≅ Rf_*(M[-n])` for `f` affine and `M` quasi-coherent.
This is [Stacks, Tag 01XC] read in the unbounded derived category. -/
def derivedPushforwardSingleIso (f : W ⟶ Y) [IsAffineHom f] (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) (hM : M.IsQuasicoherent) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj
        ((modulePushforward f.toLRSHom.toShHom).obj M) ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) n).obj M) :=
  let P := modulePushforward f.toLRSHom.toShHom
  let K : CochainComplex (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) ℤ :=
    (CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) n).obj M
  have := AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom f K
    (isQuasicoherent_singleFunctor_obj_X n M hM)
  (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).app (P.obj M) ≪≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) n).app M)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))).app
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (DerivedCategory.Qh.mapIso
      ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).symm ≪≫
    asIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing W.toRingedSpace))
        (ComplexShape.up ℤ)).obj K)) ≪≫
    (derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing W.toRingedSpace))).app K ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) n).app M).symm)

/-- **The direct image is the only cohomology sheaf of the derived direct image of a single
sheaf**: `H^n(Rf_*(M[-n])) ≅ f_*M` for `f` affine and `M` quasi-coherent. -/
def homologyDerivedPushforwardSingleIso (f : W ⟶ Y) [IsAffineHom f] (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) (hM : M.IsQuasicoherent) :
    (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) n).obj M)) ≅
      (modulePushforward f.toLRSHom.toShHom).obj M :=
  ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).mapIso
      (derivedPushforwardSingleIso f n M hM)).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).app
      ((modulePushforward f.toLRSHom.toShHom).obj M)

/-! ### T-exactness -/

/-- **The direct image along an affine morphism commutes with cohomology on complexes with
quasi-coherent cohomology**: `H^i(Rf_*E) ≅ f_*H^i(E)`, with no boundedness hypothesis on `E`.
This is the t-exactness of `Rf_* : D_QCoh(𝒪_W) ⥤ D_QCoh(𝒪_Y)` for an affine morphism. -/
def homologyDerivedPushforwardIso (f : W ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent) (i : ℤ) :
    (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj E) ≅
      (modulePushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E) := by
  have hP := containsZero_isQuasicoherent W
  let PA := SheafOfModules.isQuasicoherent (structureSheafRing W.toRingedSpace)
  let HA :=
    DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i
  let HB :=
    DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hcoh₁ : ∀ j : ℤ, PA ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) j).obj E₁) := fun j =>
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj _ _ _ _ PA _ hP E hcoh i j
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have hcoh₂ : ∀ j : ℤ, PA ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) j).obj E₂) := fun j =>
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj _ _ _ _ PA _ hP E₁ hcoh₁ i j
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  let M := (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose
  let e : E₂ ≅ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj M :=
    (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose_spec.some
  let eM : HA.obj E₂ ≅ M := HA.mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).app M
  have hM : M.IsQuasicoherent := PA.prop_of_iso eM (hcoh₂ i)
  have hπ := AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncGEπ
    f E hcoh i i le_rfl
  have hι := AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncLEι
    f E₁ i i le_rfl
  have hgπ := DerivedCategory.isIso_homologyFunctor_map_truncGEπ i i le_rfl E
  have hgι := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι E₁ i i le_rfl
  let eE : HA.obj E ≅ M :=
    asIso (HA.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)) ≪≫
      (asIso (HA.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))).symm ≪≫ eM
  exact asIso (HB.map ((derivedPushforward f.toLRSHom.toShHom).map
        ((DerivedCategory.TStructure.t.truncGEπ i).app E))) ≪≫
      (asIso (HB.map ((derivedPushforward f.toLRSHom.toShHom).map
        ((DerivedCategory.TStructure.t.truncLEι i).app E₁)))).symm ≪≫
      HB.mapIso ((derivedPushforward f.toLRSHom.toShHom).mapIso e) ≪≫
      homologyDerivedPushforwardSingleIso f i M hM ≪≫
      ((modulePushforward f.toLRSHom.toShHom).mapIso eE).symm

/-! ### The vanishing criterion -/

/-- **A degree in which the cohomology of `E` vanishes is one in which the cohomology of `Rf_*E`
vanishes**, for `f` affine and `E` with quasi-coherent cohomology. -/
theorem isZero_homology_derivedPushforward_of_isZero_homology (f : W ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E)) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj E)) :=
  (Functor.map_isZero (modulePushforward f.toLRSHom.toShHom) h).of_iso
    (homologyDerivedPushforwardIso f E hcoh i)

/-- **A degree in which the cohomology of `Rf_*E` vanishes is one in which the cohomology of `E`
vanishes**, for `f` affine and `E` with quasi-coherent cohomology: `H^i(Rf_*E) = f_*H^i(E)` and
`f_*` is conservative on quasi-coherent modules. -/
theorem isZero_homology_of_isZero_homology_derivedPushforward (f : W ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E) :=
  isZero_of_isZero_modulePushforward_of_isAffineHom f _ (hcoh i)
    (h.of_iso (homologyDerivedPushforwardIso f E hcoh i).symm)

/-- **The derived direct image along an affine morphism detects vanishing of cohomology**:
`H^i(Rf_*E) = 0` exactly when `H^i(E) = 0`, for `E` with quasi-coherent cohomology. -/
theorem isZero_homology_derivedPushforward_iff (f : W ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E) :=
  ⟨fun h => isZero_homology_of_isZero_homology_derivedPushforward f E hcoh h,
    fun h => isZero_homology_derivedPushforward_of_isZero_homology f E hcoh h⟩

end Stacks.AlgebraicGeometry.AffinePushforwardTExactness

end
