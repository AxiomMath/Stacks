module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineSource.Basic

/-!
# Pullback of ampleness along a quasi-affine morphism, in the unit-isomorphic case

Stacks Tag 0892 part (2) says that the pullback of an ample invertible module along a quasi-affine
morphism is ample, and Stacks Tag 0893 that relative ampleness is preserved by base change. This
file proves both **for an invertible module isomorphic to the structure sheaf**, where the
ampleness theory of this repository is unconditional, and generalises Stacks Tag 0891 to that
case on the way.

The restriction to unit-isomorphic modules is not cosmetic: see *What is not done*.

## Main results

* `Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule`:
  **Stacks Tag 0891 for any invertible module isomorphic to `𝒪_X`**, and in the vocabulary of the
  class `AlgebraicGeometry.IsQuasiAffineHom` rather than of an unfolded quantifier over affine
  opens. The library's form of Tag 0891,
  `Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff`, is the case `L = 𝒪_X` with the
  right-hand side unfolded.
* `Stacks.AmplePullback.isAmple_modulePullback_of_isQuasiAffineHom_of_iso_unitModule`:
  **Stacks Tag 0892 part (2) for `M` isomorphic to `𝒪_S`.** The pullback of such an ample module
  along a quasi-affine morphism is ample. Unconditional.
* `Stacks.AmplePullback.isRelativelyAmple_modulePullback_of_iso_unitModule`:
  **Stacks Tag 0893 for `L` isomorphic to `𝒪_X`, for an affine `f`.** The hypothesis that `f` is
  affine is what makes the base change quasi-affine; see *What is not done*.
* `Stacks.AmplePullback.isAmple_tensorUnit_modulePullback_of_iso_unitModule`:
  **Stacks Tag 0892 part (1) for `L` isomorphic to `𝒪_X` and `M` isomorphic to `𝒪_S`**, with the
  threshold `0`: every pullback power may be used, not merely the large ones, because the module
  in question is again isomorphic to `𝒪_X`.

## The route

Every statement below is Stacks Tag 01QE — `Stacks.Ample.isQuasiAffine_iff_isAmple`, which this
repository proves with no hypothesis — read through
`Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule`, which frees it from the
requirement that the module be `𝒪_X` on the nose. For a module isomorphic to the structure sheaf,
ampleness *is* quasi-affineness of the scheme; so a statement about pullbacks of such modules is
a statement about quasi-affineness of a source, and that is
`Stacks.QuasiAffineSource.isQuasiAffine_of_isQuasiAffineHom`.

The pullback stays unit-isomorphic because `Stacks.RelativeAmple.pullbackUnitModuleIso` is
`f^* 𝒪_S ≅ 𝒪_X` and `f^*` carries `L ≅ 𝒪_S` to `f^* L ≅ f^* 𝒪_S`; invertibility of the pullback
is Stacks Tag 0B8L as the instance
`Stacks.InvertiblePullback.isInvertibleModule_pullback`, so it is never written down.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)

## What is not done

**Neither tag is proved in general.** The general statements need material this repository does
not have, and the missing inputs are named rather than assumed:

* Tag 0892 part (2) for a general ample `M` needs, as in the source, part (1) together with
  Stacks Tag 01PT (`L` is ample if and only if `L ^⊗ n` is, for `n ≥ 1`). Part (1) in turn needs
  the section-extension lemma of the source — Properties of Schemes, Lemma 28.18.2(2): a section
  of `L ^⊗ n` over `X_t` extends to a global section of `L ^⊗ n ⊗ f^* M ^⊗ em` after multiplying
  by a power of `f^* t` — and the eventual global generation of Properties of Schemes,
  Proposition 28.27.13. None of the three is in the tree: no declaration carries Tag 01PT, and
  neither Tag 01Q1 nor Tag 01Q3 is attached anywhere either. The route taken here replaces the
  whole of the source argument by Tag 01QE, which is available only when the module is
  unit-isomorphic.
* Tag 0893 in general needs **base-change stability of quasi-affine morphisms** (so that
  `AlgebraicGeometry.IsQuasiAffineHom (pullback.snd f g)` follows from
  `AlgebraicGeometry.IsQuasiAffineHom f`) for the unit-isomorphic case, and Stacks Tag 01VJ —
  relative ampleness may be checked on an affine open covering of the base — for the general one.
  Neither is in the tree. The affine case is the one proved below, because
  `AlgebraicGeometry.IsAffineHom` *is* stable under base change in Mathlib.
* The nonvanishing-locus comparison of Stacks Tag 0H78, `X'_{f^* s} = f^{-1}(X_s)`, **is now
  proved and tagged**: `Stacks.NonvanishingPullback.preimage_nonvanishingLocus_lrs`, at the full
  generality of Remark 17.25.11 — locally ringed spaces, arbitrary `L`, no invertibility — with
  the scheme form `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`. It discharges the
  premise
  `Stacks.AmpleLocallyClosed.SectionPullbackCompatible`. The former claim that it "is still
  missing, and it is what the general proofs of both tags need" is withdrawn.
* Consequently the neighbouring claim that **nothing here addresses Stacks Tag 09MS** because its
  easy direction "inherits the same gap" is false in its reason. That direction needs only that a
  closed immersion is *affine*: 0H78 gives `Z_{i^* s} = i^{-1}(X_s)` and `IsAffineOpen.preimage`
  makes it affine, with surjectivity and Noetherianness unused. It is proved in
  `../AmpleClosedImmersion/`, and the general affine-morphism form in `../AmplePullback/`.

**Nothing here addresses Stacks Tag 09MS**, ampleness along a surjective closed immersion of
Noetherian schemes. Its easy direction is Tag 0892 part (2) for a closed immersion, so it
inherits the same gap; its converse is not of this kind at all. The source argument filters the
ideal by its powers, forms the twisted exact sequences `0 → I ⊗ L ^⊗ n → L ^⊗ n → i_* i^* L ^⊗ n
→ 0`, and kills the obstruction class in `H^1(Z, I ⊗ i^* L ^⊗ n)` using that the boundary map of
the direct sum over all `n` is a derivation (Cohomology, Lemma 20.25.5) together with Cohomology
of Schemes, Lemma 30.17.4, finishing with Serre's criterion in the form of Cohomology of Schemes,
Lemma 30.13.3. Coherent cohomology of schemes, `H^1` of a quasi-coherent module and that
criterion are all absent from this repository, so no part of the converse is reachable here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe v u w

namespace Stacks.AmplePullback

open Stacks.Ample Stacks.RelativeAmple Stacks.QuasiAffineSource

variable {X S : Scheme.{u}}

/-! ### The pullback of a unit-isomorphic module -/

/-- The pullback of an invertible module isomorphic to `𝒪_S` is isomorphic to `𝒪_X`: apply `f^*`
to the isomorphism and compose with `Stacks.RelativeAmple.pullbackUnitModuleIso`. -/
def modulePullbackIsoUnitModule (f : X ⟶ S) (M : S.Modules) (e : M ≅ unitModule S) :
    (modulePullback f.toLRSHom.toShHom).obj M ≅ unitModule X :=
  (modulePullback f.toLRSHom.toShHom).mapIso e ≪≫ pullbackUnitModuleIso f

/-! ### Stacks Tag 0891 for a unit-isomorphic module -/

/-- **Stacks Tag 0891 for any invertible module isomorphic to `𝒪_X`, and with the right-hand side
read as a class.** Such a module is ample relative to `f` exactly when `f` is quasi-affine.

The library's form of Tag 0891, `Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff`, is the case
`L = 𝒪_X` with the right-hand side written out as a quantifier over affine opens of the base;
`AlgebraicGeometry.isQuasiAffineHom_iff` is what identifies that quantifier with the class. -/
theorem isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (e : L ≅ unitModule X) :
    IsRelativelyAmple f L ↔ IsQuasiAffineHom f := by
  rw [isQuasiAffineHom_iff]
  have key (V : S.Opens) (hV : IsAffineOpen V) := isQuasiAffine_iff_isAmple_of_iso_unitModule _ _
    (modulePullbackIsoUnitModule (f ⁻¹ᵁ V).ι L e)
  exact ⟨fun h V hV => (key V hV).mpr (h.2 V hV), fun h =>
    ⟨quasiCompact_of_forall_isQuasiAffine_preimage f h, fun V hV => (key V hV).mp (h V hV)⟩⟩

/-- A unit-isomorphic invertible module on the source of a quasi-affine morphism is relatively
ample. -/
theorem isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule (f : X ⟶ S) [IsQuasiAffineHom f]
    (L : X.Modules) [IsInvertibleModule X L] (e : L ≅ unitModule X) :
    IsRelativelyAmple f L :=
  (isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule f L e).mpr inferInstance

/-! ### Stacks Tag 0892 part (2) for a unit-isomorphic module -/

/-- A unit-isomorphic invertible module on the source of a quasi-affine morphism into a scheme with
an ample unit-isomorphic invertible module is ample. -/
private theorem isAmple_of_isQuasiAffineHom_of_iso_unitModule (f : X ⟶ S) [IsQuasiAffineHom f]
    (M : S.Modules) [IsInvertibleModule S M] (eM : M ≅ unitModule S) (hM : IsAmple S M)
    (N : X.Modules) [IsInvertibleModule X N] (eN : N ≅ unitModule X) : IsAmple X N := by
  have hS : S.IsQuasiAffine := (isQuasiAffine_iff_isAmple_of_iso_unitModule S M eM).mpr hM
  exact (isQuasiAffine_iff_isAmple_of_iso_unitModule X N eN).mp
    (isQuasiAffine_of_isQuasiAffineHom f)

/-- **Stacks Tag 0892 part (2) for an invertible module isomorphic to `𝒪_S`.** The pullback of
such an ample module along a quasi-affine morphism is ample.

Ampleness of `M` makes `S` quasi-affine by Stacks Tag 01QE; a quasi-affine morphism into a
quasi-affine scheme has quasi-affine source
(`Stacks.QuasiAffineSource.isQuasiAffine_of_isQuasiAffineHom`); and the pullback is again
unit-isomorphic, so Tag 01QE reads back. -/
theorem isAmple_modulePullback_of_isQuasiAffineHom_of_iso_unitModule (f : X ⟶ S)
    [IsQuasiAffineHom f] (M : S.Modules) [IsInvertibleModule S M] (e : M ≅ unitModule S)
    (hM : IsAmple S M) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj M) := by
  exact isAmple_of_isQuasiAffineHom_of_iso_unitModule f M e hM _ (modulePullbackIsoUnitModule f M e)

/-- **Stacks Tag 0892 part (2) for the structure sheaf.** The pullback of `𝒪_S` along a
quasi-affine morphism is ample as soon as `𝒪_S` is. -/
theorem isAmple_modulePullback_unitModule_of_isQuasiAffineHom (f : X ⟶ S) [IsQuasiAffineHom f]
    (hS : IsAmple S (unitModule S)) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj (unitModule S)) :=
  isAmple_modulePullback_of_isQuasiAffineHom_of_iso_unitModule f _ (Iso.refl _) hS

/-! ### Stacks Tag 0893 for a unit-isomorphic module, along an affine morphism -/

/-- **Stacks Tag 0893 for an invertible module isomorphic to `𝒪_X`, along an affine `f`.**
Relative ampleness of such a module is preserved by an arbitrary base change of an affine
morphism.

The hypothesis `hL` is not used: for an affine `f` the conclusion of Tag 0891 holds on both sides
of the base change, since `AlgebraicGeometry.IsAffineHom` is stable under base change and an
affine morphism is quasi-affine. It is kept in the statement because it is the hypothesis of the
tag, and dropping it would change what the statement says about the general case. -/
theorem isRelativelyAmple_modulePullback_of_iso_unitModule {S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) [IsAffineHom f] (L : X.Modules) [IsInvertibleModule X L]
    (e : L ≅ unitModule X) (_hL : IsRelativelyAmple f L) :
    IsRelativelyAmple (pullback.snd f g)
      ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj L) := by
  have halong : MorphismProperty.IsStableUnderBaseChangeAlong (C := Scheme.{u}) @IsAffineHom g :=
    ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  have hbc : IsAffineHom (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) f g inferInstance
  exact (isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule (pullback.snd f g) _
    (modulePullbackIsoUnitModule (pullback.fst f g) L e)).mpr inferInstance

/-! ### Stacks Tag 0892 part (1) for unit-isomorphic modules -/

section Monoidal

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

open MonoidalCategory Stacks.SheafOfModules.TensorSheafification

/-- **The tensor product of two modules isomorphic to the structure sheaf is isomorphic to the
structure sheaf**, in the `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling. Stated
at the generality of an arbitrary site, which is the generality at which the monoidal structure of
`Stacks.SheafInternalHom.monoidalCategory` is available as an instance. -/
def tensorSheafIsoUnit {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (A B : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (eA : A ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))
    (eB : B ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        (A)).obj (B)) ≅
      𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) := by
  letI : MonoidalCategory (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) :=
    Stacks.SheafInternalHom.monoidalCategory 𝒪 h𝒪
  exact (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 A B).symm ≪≫
    MonoidalCategory.tensorIso eA eB ≪≫ λ_ _

variable (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule S M]
  (eL : L ≅ unitModule X) (eM : M ≅ unitModule S)

/-- The module `L ⊗ f^*(M ^⊗ a)`, written with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` so that no monoidal instance is needed to
state it. This is the object Stacks Tag 0892 part (1) concludes about. -/
def tensorPullbackPow (a : ℤ) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
      ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj (L)).obj
    (((modulePullback f.toLRSHom.toShHom).obj (tensorPowModule S M a))))

include eL eM in
/-- `L ⊗ f^*(M ^⊗ a) ≅ 𝒪_X` when `L ≅ 𝒪_X` and `M ≅ 𝒪_S`: every tensor power of `M` is `𝒪_S` by
`Stacks.RelativeAmple.tensorPowModuleIsoUnitModule`, its pullback is `𝒪_X` by
`Stacks.RelativeAmple.pullbackUnitModuleIso`, and a unitor finishes. -/
def tensorPullbackPowIsoUnitModule (a : ℤ) : tensorPullbackPow f L M a ≅ unitModule X :=
  tensorSheafIsoUnit X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
      ((modulePullback f.toLRSHom.toShHom).obj (tensorPowModule S M a))
      (eL ≪≫ unitModuleIsoTensorUnit X)
      (modulePullbackIsoUnitModule f (tensorPowModule S M a)
        (tensorPowModuleIsoUnitModule S M eM a) ≪≫ unitModuleIsoTensorUnit X) ≪≫
    (unitModuleIsoTensorUnit X).symm

include eL eM in
omit [IsInvertibleModule X L] in
/-- `L ⊗ f^*(M ^⊗ a)` is invertible: it is isomorphic to the monoidal unit. -/
theorem isInvertibleModule_tensorPullbackPow (a : ℤ) :
    IsInvertibleModule X (tensorPullbackPow f L M a) :=
  AlgebraicGeometry.SheafOfModules.isInvertible_of_iso_unit _ _ _
    (tensorPullbackPowIsoUnitModule f L M eL eM a ≪≫ unitModuleIsoTensorUnit X)

/-- **Stacks Tag 0892 part (1) for `L` isomorphic to `𝒪_X` and `M` isomorphic to `𝒪_S`, in every
degree.** For such modules no threshold is needed: `L ⊗ f^*(M ^⊗ a)` is again isomorphic to
`𝒪_X`, and it is ample because `X` is quasi-affine — which is what relative ampleness of `L` and
ampleness of `M` say in this case. -/
theorem isAmple_tensorPullbackPow_of_iso_unitModule (hL : IsRelativelyAmple f L)
    (hM : IsAmple S M) (a : ℤ) :
    letI := isInvertibleModule_tensorPullbackPow f L M eL eM a
    IsAmple X (tensorPullbackPow f L M a) := by
  have hf : IsQuasiAffineHom f :=
    (isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule f L eL).mp hL
  have := isInvertibleModule_tensorPullbackPow f L M eL eM a
  exact isAmple_of_isQuasiAffineHom_of_iso_unitModule f M eM hM _
    (tensorPullbackPowIsoUnitModule f L M eL eM a)

/-- **Stacks Tag 0892 part (1) for unit-isomorphic modules, in the shape of the tag**: a
threshold beyond which every pullback power works. The threshold is `0`. -/
theorem exists_isAmple_tensorPullbackPow_of_iso_unitModule (hL : IsRelativelyAmple f L)
    (hM : IsAmple S M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a →
      letI := isInvertibleModule_tensorPullbackPow f L M eL eM (a : ℤ)
      IsAmple X (tensorPullbackPow f L M (a : ℤ)) :=
  ⟨0, fun a _ => isAmple_tensorPullbackPow_of_iso_unitModule f L M eL eM hL hM (a : ℤ)⟩

end Monoidal

end Stacks.AmplePullback

end
