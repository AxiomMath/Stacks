module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekProper
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of a proper morphism

Clauses (2) and (4)(c) of [Stacks, Section 0AU3]. Let `S` be a Noetherian scheme and
`f : X ⟶ Y` a proper morphism of `FTS S`, with `f^!` computed at any compactification `j`.

* (2) `f^!` is the restriction to `D⁺_QCoh(𝒪_Y)` of the right adjoint `a` of
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and `Rf_* R𝓗om(K, f^!M) ≅ R𝓗om(Rf_*K, M)` for
  `K ∈ D⁻_Coh(𝒪_X)` and `M ∈ D⁺_QCoh(𝒪_Y)`.
* (4)(c) for a dualizing complex `ω_Y` and `ω_X = f^!ω_Y`,
  `Rf_* R𝓗om(K, ω_X) ≅ R𝓗om(Rf_*K, ω_Y)` for `K ∈ D⁻_Coh(𝒪_X)`.

The first assertion of (2) is the independence of `f^!` of the compactification on `D⁺_QCoh`
([Stacks, Tag 0AA0], `Stacks.Duality.DominatingCompactification.upperShriekPlusIso`) together
with `f^! = a` at the identity compactification (`Stacks.Duality.upperShriekProperAdjunction`).
The duality isomorphism is the sheafy trace of [Stacks, Tag 0B6H], invertible by
[Stacks, Tag 0GEW] (`Stacks.Duality.sheafyTraceIsoStd`).

The derived internal Homs and `Rf_*` are read at the standard model of the derived categories,
at which [Stacks, Tag 0GEW] is proved, and `f^!` at the locally small one; the two are compared
along the identity-on-objects equivalence `Stacks.Duality.TwistedInverseImageDuality.comparison`.

## Main results

* `Stacks.Duality.upperShriekPlusIsoRightAdjointOfIsProper` — `f^! ≅ a` on `D⁺_QCoh`.
* `Stacks.Duality.sheafHomUpperShriekIsoOfIsProper` — the duality isomorphism.
* `Stacks.Duality.upperShriek_rightAdjoint_and_duality_of_isProper` — clause (2).
* `Stacks.Duality.nonempty_sheafHomDualizingIsoOfIsProper` — clause (4)(c).

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open TwistedInverseImageDuality (Std sheafHom push comparison qcoh rightAdjointStd)

/-- Tensoring with a fixed object of `D_QCoh(𝒪_Z)` on the right, read in `D(𝒪_Z)`, is the derived
tensor product with its underlying object. -/
def quasiCoherentDerivedTensorFlipCompιIso (Z : Scheme.{u}) (W : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedTensor Z).flip.obj W ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ (derivedTensor Z).flip.obj W.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ L} g => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    change ((derivedTensor Z).map g.hom).app W.obj ≫ ((derivedTensor Z).obj L.obj).map (𝟙 W.obj) =
      ((derivedTensor Z).map g.hom).app W.obj
    rw [CategoryTheory.Functor.map_id, Category.comp_id])

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) [IsProper f.left]
  (j : CompactificationOf (Over.mk f.left))

/-- For a proper morphism `f` of `FTS S` and any compactification `j`, the upper shriek functor
`f^! : D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` is the restriction to `D⁺_QCoh(𝒪_Y)` of any right adjoint `a`
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
def upperShriekPlusIsoRightAdjointOfIsProper
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
    (adj : DerivedPushforward.qcqsRestrictedDerivedPushforward f.left ⊣ a) :
    upperShriekPlus f j ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ a :=
  Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso f j
      (properCompactification f)) (ObjectProperty.ι _) ≪≫
    ObjectProperty.liftCompιIso _ _ _ ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((upperShriekProperAdjunction f).rightAdjointUniq adj)

/-- An object of `D(𝒪_Y)` bounded below at the standard model is bounded below at the locally
small model. -/
theorem isBoundedBelow_comparison_functor_obj {Z : Scheme.{u}} (M : Std Z)
    (hM : @DerivedCategoryB.IsBoundedBelow Z.Modules _ _
      (PerfectApproximation.standardModel Z) M) :
    DerivedCategoryB.IsBoundedBelow ((comparison Z).functor.obj M) := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n, fun i hi => (PerfectApproximation.isZero_homology_standard_iff M i).1 (hn i hi)⟩

/-- `f^!M`, read at the standard model, is `a(M)` read at the standard model, for `f` proper and
`M` bounded below with quasi-coherent cohomology. -/
def upperShriekObjStdIsoRightAdjointStd (M : (qcoh Y.left).FullSubcategory)
    (hM : @DerivedCategoryB.IsBoundedBelow Y.left.Modules _ _
      (PerfectApproximation.standardModel Y.left) M.obj) :
    (comparison X.left).inverse.obj
        ((upperShriek f j).obj ⟨(comparison Y.left).functor.obj M.obj, M.property⟩).obj ≅
      (rightAdjointStd f.left).obj M :=
  (comparison X.left).inverse.mapIso ((ObjectProperty.ι _).mapIso
    ((upperShriekPlusIsoRightAdjointOfIsProper f j _
      (twistedInverseImageAdjunction f.left
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left))).app
      ⟨⟨_, M.property⟩, isBoundedBelow_comparison_functor_obj M.obj hM⟩))

/-- **The duality isomorphism of clause (2) of [Stacks, Section 0AU3].** For a proper morphism
`f : X ⟶ Y` of `FTS S`, any compactification `j`, `K ∈ D⁻_Coh(𝒪_X)` and `M ∈ D⁺_QCoh(𝒪_Y)`,

`Rf_* R𝓗om_{𝒪_X}(K, f^!M) ≅ R𝓗om_{𝒪_Y}(Rf_*K, M)`.

It is the sheafy trace map of [Stacks, Tag 0B6H], an isomorphism by [Stacks, Tag 0GEW], composed
with `f^!M ≅ a(M)`. The derived internal Homs and `Rf_*` are read at the standard model and
`f^!M` through the identity-on-objects comparison of the two models. -/
def sheafHomUpperShriekIsoOfIsProper (K : Std X.left) (hK : minusCoh X.left K)
    (M : (qcoh Y.left).FullSubcategory)
    (hM : @DerivedCategoryB.IsBoundedBelow Y.left.Modules _ _
      (PerfectApproximation.standardModel Y.left) M.obj) :
    (push f.left).obj (((sheafHom X.left).obj (op K)).obj ((comparison X.left).inverse.obj
        ((upperShriek f j).obj ⟨(comparison Y.left).functor.obj M.obj, M.property⟩).obj)) ≅
      ((sheafHom Y.left).obj (op ((push f.left).obj K))).obj M.obj :=
  (push f.left).mapIso (((sheafHom X.left).obj (op K)).mapIso
      (upperShriekObjStdIsoRightAdjointStd f j M hM)) ≪≫
    sheafyTraceIsoStd f.left K hK M hM

/-- **Stacks Project, Section 0AU3, clause (2).** Let `S` be a Noetherian scheme and let
`f : X ⟶ Y` be a proper morphism of `FTS S`, with `f^!` computed at any compactification `j`.
Then `f^!` is the restriction of the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` to
`D⁺_QCoh(𝒪_Y)`, and there is a canonical isomorphism

`Rf_* R𝓗om_{𝒪_X}(K, f^!M) ≅ R𝓗om_{𝒪_Y}(Rf_*K, M)`

for all `K ∈ D⁻_Coh(𝒪_X)` and `M ∈ D⁺_QCoh(𝒪_Y)`:

1. `f^!` carries `D⁺_QCoh(𝒪_Y)` into `D⁺_QCoh(𝒪_X)`;
2. for every right adjoint `a` of `Rf_*`, the functor `f^! : D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` is
   isomorphic to the restriction of `a`;
3. the isomorphism, `Stacks.Duality.sheafHomUpperShriekIsoOfIsProper`, with the derived internal
   Homs and `Rf_*` read at the standard model. -/
@[stacks 0AU3 "clause (2) in full: for a proper morphism f of FTS S and any compactification, \
  f^! carries D^+_QCoh into D^+_QCoh and is the restriction to D^+_QCoh of every right adjoint of \
  Rf_* on D_QCoh, and Rf_* RHom(K, f^! M) = RHom(Rf_* K, M) for K in D^-_Coh(O_X) and M in \
  D^+_QCoh(O_Y) (the sheafy trace of Tag 0B6H, invertible by Tag 0GEW)"]
theorem upperShriek_rightAdjoint_and_duality_of_isProper :
    (∀ M : quasiCoherentDerivedCategory Y.left, DerivedCategoryB.IsBoundedBelow M.obj →
        DerivedCategoryB.IsBoundedBelow ((upperShriek f j).obj M).obj) ∧
      (∀ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
          (_ : DerivedPushforward.qcqsRestrictedDerivedPushforward f.left ⊣ a),
        Nonempty (upperShriekPlus f j ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ a)) ∧
      ∀ (K : Std X.left) (_ : minusCoh X.left K) (M : (qcoh Y.left).FullSubcategory)
        (_ : @DerivedCategoryB.IsBoundedBelow Y.left.Modules _ _
          (PerfectApproximation.standardModel Y.left) M.obj),
        Nonempty ((push f.left).obj (((sheafHom X.left).obj (op K)).obj
            ((comparison X.left).inverse.obj
              ((upperShriek f j).obj ⟨(comparison Y.left).functor.obj M.obj, M.property⟩).obj)) ≅
          ((sheafHom Y.left).obj (op ((push f.left).obj K))).obj M.obj) :=
  ⟨fun M hM => isBoundedBelow_upperShriek_obj f j M hM,
    fun a adj => ⟨upperShriekPlusIsoRightAdjointOfIsProper f j a adj⟩,
    fun K hK M hM => ⟨sheafHomUpperShriekIsoOfIsProper f j K hK M hM⟩⟩

open UpperShriekDuality in
/-- **The duality isomorphism of clause (4)(c) of [Stacks, Section 0AU3].** For a proper morphism
`f : X ⟶ Y` of `FTS S`, a dualizing complex `ω_Y` on `Y`, `ω_X = f^!ω_Y` (at any
compactification) and `K ∈ D⁻_Coh(𝒪_X)`,

`Rf_* R𝓗om_{𝒪_X}(K, ω_X) ≅ R𝓗om_{𝒪_Y}(Rf_*K, ω_Y)`.

This is clause (2) at `M = ω_Y`, which is bounded below with coherent cohomology. -/
def sheafHomDualizingIsoOfIsProper {ω : Std Y.left} (hω : TwistedInverseImageDuality.IsDualizing ω)
    (K : Std X.left) (hK : minusCoh X.left K) :
    (push f.left).obj (((sheafHom X.left).obj (op K)).obj (upperShriekDualizing f j hω)) ≅
      ((sheafHom Y.left).obj (op ((push f.left).obj K))).obj ω :=
  sheafHomUpperShriekIsoOfIsProper f j K hK (TwistedInverseImageDuality.dualizingObject hω)
    (isBoundedBelow_of_isDualizing_std hω)

open UpperShriekDuality in
/-- **Stacks Project, Section 0AU3, clause (4)(c).** Let `S` be a Noetherian scheme, let
`f : X ⟶ Y` be a proper morphism of `FTS S`, let `ω_Y` be a dualizing complex on `Y` and
`ω_X = f^!ω_Y` (at any compactification). Then
`Rf_* R𝓗om_{𝒪_X}(K, ω_X) ≅ R𝓗om_{𝒪_Y}(Rf_*K, ω_Y)` for `K ∈ D⁻_Coh(𝒪_X)`. -/
@[stacks 0AU3 "clause (4)(c): for a proper morphism f : X to Y of FTS S, a dualizing complex \
  omega_Y on Y and omega_X = f^! omega_Y at any compactification, Rf_* RHom(K, omega_X) = \
  RHom(Rf_* K, omega_Y) for K in D^-_Coh(O_X); clause (2) at M = omega_Y"]
theorem nonempty_sheafHomDualizingIsoOfIsProper {ω : Std Y.left}
    (hω : TwistedInverseImageDuality.IsDualizing ω) (K : Std X.left) (hK : minusCoh X.left K) :
    Nonempty ((push f.left).obj (((sheafHom X.left).obj (op K)).obj
        (upperShriekDualizing f j hω)) ≅
      ((sheafHom Y.left).obj (op ((push f.left).obj K))).obj ω) :=
  ⟨sheafHomDualizingIsoOfIsProper f j hω K hK⟩

end Stacks.Duality

end
