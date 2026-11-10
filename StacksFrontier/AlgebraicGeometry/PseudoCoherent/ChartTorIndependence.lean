module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor independence at an affine-space chart

Let `f : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes with `X` and `S'` Tor independent over
`S`. For an affine open `V` of `S`, an affine open `V' ⊆ g⁻¹(V)` of `S'`, an affine open
`U ⊆ f⁻¹(V)` of `X` and a morphism `i : U ⟶ 𝔸(ι; V)` over `V` factoring `f|_U`, the schemes `U`
and `𝔸(ι; V')` are Tor independent over `𝔸(ι; V)`. This is the form in which the Tor
independence hypothesis of Stacks 09UR enters the proof of that lemma, so discharging it turns
the conditional statement of 09UR into the statement of the source.

## Main definitions

There are no new definitions.

## Main results

* `Algebra.torIndependent_of_isPushout_of_flat`: Tor independence of a `P`-algebra `A` and an
  `R`-algebra `S` over `R` ascends to Tor independence of `A` and the pushout `P'` of `P` and `S`
  over `P`, when `P` is flat over `R`.
* `AlgebraicGeometry.Scheme.Hom.chartTorIndependence_of_torIndependent`: Tor independence of `X`
  and `S'` over `S` implies the chart form
  `AlgebraicGeometry.Scheme.Hom.ChartTorIndependence`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependent`
  (Stacks 09UR): relative `m`-pseudo-coherence is preserved by a Tor-independent base change.

## Implementation notes

The ring-theoretic core is the first result. Extension of scalars along a flat `R ⟶ P` is exact
and preserves projectives, so it carries a projective resolution of `S` over `R` to a projective
resolution of `P ⊗[R] S` over `P`; tensoring that with `A` over `P` returns the complex computing
`Tor^R_*(A, S)`, which identifies the two families of Tor modules. The module structures on the
two sides of the auxiliary isomorphisms comparing `A ⊗[P] (P ⊗[R] M)` with `A ⊗[R] M` agree only
after unfolding the functors that produce them, so each such step is named by an explicit
equivalence (`restrictTensorIso`, `extendScalarsCarrierAddEquiv`, `tensorObjCarrierAddEquiv`)
rather than left to unification.

The geometric step is a pair of transports along `AlgebraicGeometry.torIndependent_congr`. Every
scheme occurring in the chart condition is affine, so by `AlgebraicGeometry.torIndependent_tfae`
both the hypothesis and the conclusion are conditions on rings of global sections: the hypothesis
is read on `Γ(V)`, `Γ(U)` and `Γ(V')` using `AlgebraicGeometry.Scheme.Hom.resLE_app_top` to
match `AlgebraicGeometry.Scheme.Hom.appLE` with the sections of the restricted morphisms, and the
conclusion is read on `Γ(𝔸(ι; V))` and `Γ(𝔸(ι; V'))` using
`AlgebraicGeometry.AffineSpace.isoOfIsAffine` to present them as polynomial rings. Mathlib
supplies the pushout square of polynomial rings and the freeness of a polynomial ring over its
coefficients.

Stacks 0E23 is no longer carried.  It is proved —
`AlgebraicGeometry.derivedBaseChangeIsoOfTorIndependent` — so Stacks 09UR is unconditional and
the tag for it sits on
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependent` below.

## References

* [The Stacks Project, Lemma 37.59.15 (09UR)](https://stacks.math.columbia.edu/tag/09UR)
* [The Stacks Project, Lemma 36.22.9 (0E23)](https://stacks.math.columbia.edu/tag/0E23)
* [The Stacks Project, Lemma 15.65.4 (0FXV)](https://stacks.math.columbia.edu/tag/0FXV)
* [The Stacks Project, Lemma 15.62.1 (08HW)](https://stacks.math.columbia.edu/tag/08HW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section FlatPushout

variable (R P A S P' : Type u) [CommRing R] [CommRing P] [CommRing A] [CommRing S]
  [CommRing P'] [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
  [Algebra R S] [Algebra R P'] [Algebra P P'] [Algebra S P']
  [IsScalarTower R P P'] [IsScalarTower R S P']

/-- Extension of scalars along `R ⟶ P` carries the `R`-module `S` to `P'`, when `P'` is the
pushout of `P` and `S` over `R`. -/
private def pushoutModuleIso [Algebra.IsPushout R P S P'] :
    (ModuleCat.extendScalars (algebraMap R P)).obj (ModuleCat.of R S) ≅
      ModuleCat.of P P' :=
  PseudoCoherence.extendScalarsAlgebraMapObjIso (ModuleCat.of R S) ≪≫
    (Algebra.IsPushout.equiv R P S P').toLinearEquiv.toModuleIso

/-- The `R`-module `A`, as the restriction of scalars along `R ⟶ P` of the `P`-module `A`. -/
private def restrictScalarsLinearEquiv :
    (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A) ≃ₗ[R] A :=
  { toFun := fun a => (a : A)
    invFun := fun a => (a : (ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P A))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r a => IsScalarTower.algebraMap_smul P r (show A from a) }

/-- For an `R`-module `M`, the `P`-module `A ⊗[P] (P ⊗[R] M)` is `A ⊗[R] M` as an
`R`-module. -/
private def restrictTensorIso (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P (TensorProduct R A M)) ≅
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).obj M := by
  let eA := restrictScalarsLinearEquiv R P A
  let X := (ModuleCat.restrictScalars (algebraMap R P)).obj
    (ModuleCat.of P (TensorProduct R A M))
  let e₀ : X ≃ₗ[R] ModuleCat.of R (TensorProduct R A M) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r z
        induction z using TensorProduct.inductionOn with
        | tmul a m =>
            change ((algebraMap R P r) • a) ⊗ₜ[R] m = (r • a) ⊗ₜ[R] m
            rw [IsScalarTower.algebraMap_smul P r a]
        | add x y hx hy =>
            change (algebraMap R P r) • (x + y) = r • (x + y)
            rw [smul_add, smul_add]
            exact congrArg₂ (fun x y => x + y) hx hy }
  exact (e₀.trans (TensorProduct.congr eA.symm (LinearEquiv.refl R M))).toModuleIso

/-- The carrier of `(ModuleCat.extendScalars (algebraMap R P)).obj M`, named as the tensor
product it is: `ModuleCat.ExtendScalars.obj'` wraps `P ⊗[R] M` with `P` carrying the module
structure restricted along `algebraMap R P`, and the elaborator sees that only after unfolding
the functor. Going through this equivalence states additivity in the second tensor factor
without such an unfolding. -/
private def extendScalarsCarrierAddEquiv (M : ModuleCat.{u} R) :
    TensorProduct R ↑((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P P)) ↑M ≃+
      ↑((ModuleCat.extendScalars (algebraMap R P)).obj M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The carrier of `A ⊗[P] ((ModuleCat.extendScalars (algebraMap R P)).obj M)`, named as the
tensor product it is. As with `extendScalarsCarrierAddEquiv`, going through this equivalence
states additivity in an element of that carrier without unfolding the functors that build it. -/
private def tensorObjCarrierAddEquiv (M : ModuleCat.{u} R) :
    TensorProduct P ↑(ModuleCat.of P A) ↑((ModuleCat.extendScalars (algebraMap R P)).obj M) ≃+
      ↑((ModuleCat.extendScalars (algebraMap R P) ⋙ tensorLeft (ModuleCat.of P A) ⋙
          ModuleCat.restrictScalars (algebraMap R P)).obj M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Cancelling the intermediate base change: `A ⊗[P] (P ⊗[R] -)` is `A ⊗[R] -` on
`R`-modules. -/
private def cancelBaseChangeNatIso :
    ModuleCat.extendScalars (algebraMap R P) ⋙ tensorLeft (ModuleCat.of P A) ⋙
        ModuleCat.restrictScalars (algebraMap R P) ≅
      tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A)) := by
  refine NatIso.ofComponents (fun M ↦ ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
      ((tensorLeft (ModuleCat.of P A)).mapIso
        (PseudoCoherence.extendScalarsAlgebraMapObjIso M))) ≪≫
    ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R P P A M).toModuleIso) ≪≫
    restrictTensorIso R P A M) ?_
  intro M N f
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨z, rfl⟩ := (tensorObjCarrierAddEquiv R P A M).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      obtain ⟨m, rfl⟩ := (extendScalarsCarrierAddEquiv R P M).surjective m
      induction m using TensorProduct.inductionOn with
      | tmul p x => rfl
      | add x y hx hy =>
          rw [map_add, TensorProduct.tmul_add, map_add]
          simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hx hy
  | add x y hx hy =>
      rw [map_add]
      simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hx hy

/-- **Tor independence ascends along a flat base extension.** Let `R ⟶ P` be flat, let `A` be a
`P`-algebra and let `P'` be the pushout of `P` and an `R`-algebra `S` over `R`. If `A` and `S`
are Tor independent over `R`, then `A` and `P'` are Tor independent over `P`.

A projective resolution of `S` over `R` extends to a projective resolution of `P'` over `P`,
because extension of scalars along a flat map is exact and preserves projectives; tensoring it
with `A` over `P` gives back the complex computing `Tor^R_*(A, S)`. -/
theorem Algebra.torIndependent_of_isPushout_of_flat [Module.Flat R P] [Algebra.IsPushout R P S P']
    (h : Algebra.TorIndependent R A S) : Algebra.TorIndependent P A P' := by
  intro i hi
  let F := ModuleCat.extendScalars (algebraMap R P)
  let _ : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R P))
  let Q₀ := projectiveResolution (ModuleCat.of R S)
  let Q := F.mapProjectiveResolution Q₀
  refine IsZero.of_iso ?_ (((Tor (ModuleCat P) i).obj (ModuleCat.of P A)).mapIso
    (pushoutModuleIso R P S P')).symm
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj (tensorLeft (ModuleCat.of P A)) i)
  rw [ModuleCat.isZero_iff_subsingleton]
  let eA := (restrictScalarsLinearEquiv R P A).toModuleIso
  have hz : IsZero (((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P A))).leftDerived i).obj (ModuleCat.of R S)) :=
    IsZero.of_iso (h i hi) (((Tor (ModuleCat R) i).mapIso eA).app (ModuleCat.of R S))
  have hz₀ : IsZero
      ((((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Q₀.complex).homology i) :=
    hz.of_iso (Q₀.isoLeftDerivedObj
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A))) i).symm
  let G := ModuleCat.restrictScalars (algebraMap R P)
  let C := ((tensorLeft (ModuleCat.of P A)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  change Subsingleton (G.obj (C.homology i))
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((hz₀.of_iso (HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (cancelBaseChangeNatIso R P A)
        (ComplexShape.down ℕ)).app Q₀.complex) i)).of_iso
      ((ShortComplex.mapHomologyIso (C.sc i) G).symm ≪≫
        HomologicalComplex.homologyMapIso
          (Iso.refl ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) i))

end FlatPushout

/-! ### The global sections of an affine-space chart -/

namespace AlgebraicGeometry

open MvPolynomial

/-- **The sections of affine space over an affine base.** For `V` affine the ring of global
sections of `𝔸(ι; V)` is the polynomial ring on `ι` over `Γ(V, ⊤)`, by the identification of
`𝔸(ι; V)` with the spectrum of that polynomial ring. -/
private def affineSpaceΓIso (ι : Type u) (V : Scheme.{u}) [IsAffine V] :
    CommRingCat.of (MvPolynomial ι Γ(V, ⊤)) ≅ Γ(𝔸(ι; V), ⊤) where
  hom := (Scheme.ΓSpecIso _).inv ≫ (AffineSpace.isoOfIsAffine ι V).hom.appTop
  inv := (AffineSpace.isoOfIsAffine ι V).inv.appTop ≫ (Scheme.ΓSpecIso _).hom
  hom_inv_id := by
    have h : (AffineSpace.isoOfIsAffine ι V).hom.appTop ≫
        (AffineSpace.isoOfIsAffine ι V).inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, (AffineSpace.isoOfIsAffine ι V).inv_hom_id]
      simp
    rw [Category.assoc, ← Category.assoc _ _ (Scheme.ΓSpecIso _).hom, h, Category.id_comp,
      Iso.inv_hom_id]
  inv_hom_id := by
    have h : (AffineSpace.isoOfIsAffine ι V).inv.appTop ≫
        (AffineSpace.isoOfIsAffine ι V).hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, (AffineSpace.isoOfIsAffine ι V).hom_inv_id]
      simp
    rw [Category.assoc, ← Category.assoc _ _ (AffineSpace.isoOfIsAffine ι V).hom.appTop,
      Iso.hom_inv_id, Category.id_comp, h]

private theorem affineSpaceΓIso_hom (ι : Type u) (V : Scheme.{u}) [IsAffine V] :
    (affineSpaceΓIso ι V).hom =
      CommRingCat.ofHom (eval₂Hom ((𝔸(ι; V) ↘ V).appTop).hom (AffineSpace.coord V)) := by
  change (Scheme.ΓSpecIso _).inv ≫ (AffineSpace.isoOfIsAffine ι V).hom.appTop = _
  rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]

private theorem affineSpaceΓIso_hom_C (ι : Type u) (V : Scheme.{u}) [IsAffine V]
    (r : Γ(V, ⊤)) :
    (affineSpaceΓIso ι V).hom (C r) = (𝔸(ι; V) ↘ V).appTop r := by
  rw [affineSpaceΓIso_hom]
  simp

private theorem affineSpaceΓIso_hom_X (ι : Type u) (V : Scheme.{u}) [IsAffine V] (i : ι) :
    (affineSpaceΓIso ι V).hom (X i) = AffineSpace.coord V i := by
  rw [affineSpaceΓIso_hom]
  simp

/-- **A morphism of affine bases acts on the sections of affine space by coefficients.** The ring
map induced by `AffineSpace.map ι q` on global sections is the coefficientwise map, read through
the identification of those sections with polynomial rings. -/
private theorem affineSpaceΓIso_map {V V' : Scheme.{u}} [IsAffine V] [IsAffine V']
    (ι : Type u) (q : V' ⟶ V) :
    (affineSpaceΓIso ι V).hom ≫ (AffineSpace.map ι q).appTop =
      CommRingCat.ofHom (MvPolynomial.map (q.appTop).hom) ≫ (affineSpaceΓIso ι V').hom := by
  have hover : (𝔸(ι; V) ↘ V).appTop ≫ (AffineSpace.map ι q).appTop =
      (q.appTop) ≫ (𝔸(ι; V') ↘ V').appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, AffineSpace.map_over]
  ext1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · have h := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hover) r
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h ⊢
    rw [affineSpaceΓIso_hom_C, h, MvPolynomial.map_C, affineSpaceΓIso_hom_C]
  · simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom]
    rw [affineSpaceΓIso_hom_X, MvPolynomial.map_X, affineSpaceΓIso_hom_X]
    exact AffineSpace.map_appTop_coord q i

/-- Restriction to the whole of both schemes is the map on global sections. -/
private theorem appLE_top_top {Y Z : Scheme.{u}} (k : Y ⟶ Z) (h : (⊤ : Y.Opens) ≤ k ⁻¹ᵁ ⊤) :
    k.appLE ⊤ ⊤ h = k.appTop :=
  Scheme.Hom.appLE_eq_app k

/-- Restricting `f.appLE V U h` to `Γ(U, ⊤)` is the map on global sections of `f.resLE V U h`. -/
private theorem appLE_topIso_inv_eq_resLE_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (U : X.Opens) (h : U ≤ f ⁻¹ᵁ V) :
    f.appLE V U h ≫ U.topIso.inv = V.topIso.inv ≫ (f.resLE V U h).appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- An equality of composites of morphisms of commutative rings, evaluated at an element. -/
private theorem comp_apply_eq_of_comp_eq {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : B ⟶ D}
    {f' : A ⟶ C} {g' : C ⟶ D} (h : f ≫ g = f' ≫ g') (x : A) :
    g.hom (f.hom x) = g'.hom (f'.hom x) := by
  simpa using DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h) x

/-- **Tor independence on the rings of sections.** If `X` and `S'` are Tor independent over `S`,
then for affine opens `U ⊆ f⁻¹(V)` and `V' ⊆ g⁻¹(V)` the rings `Γ(U)` and `Γ(V')` are Tor
independent over `Γ(V)`. -/
private theorem torIndependent_sections_of_torIndependent {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (htor : TorIndependent f g) (V : S.affineOpens) (V' : S'.affineOpens)
    (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI := (g.resLE V.1 V'.1 hV').appTop.hom.toAlgebra
    letI := (f.resLE V.1 U.1 hUV).appTop.hom.toAlgebra
    Algebra.TorIndependent Γ((V.1 : Scheme.{u}), ⊤) Γ((U.1 : Scheme.{u}), ⊤)
      Γ((V'.1 : Scheme.{u}), ⊤) := by
  let := (g.resLE V.1 V'.1 hV').appTop.hom.toAlgebra
  let := (f.resLE V.1 U.1 hUV).appTop.hom.toAlgebra
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let : Algebra Γ(S, V.1) Γ(S', V'.1) := (g.appLE V.1 V'.1 hV').hom.toAlgebra
  have hCrit := ((torIndependent_tfae f g).out 1 2).mp htor
  have hbig : Algebra.TorIndependent Γ(S, V.1) Γ(X, U.1) Γ(S', V'.1) :=
    hCrit U.1 U.2 V'.1 V'.2 V.1 V.2 hUV hV'
  refine (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).1
    ((torIndependent_congr Γ(S, V.1) Γ(X, U.1) Γ(S', V'.1) _ _ _
      (V.1.topIso).symm.commRingCatIsoToRingEquiv
      (U.1.topIso).symm.commRingCatIsoToRingEquiv
      (V'.1.topIso).symm.commRingCatIsoToRingEquiv ?_ ?_).mp
      ((RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).2 hbig))
  · exact comp_apply_eq_of_comp_eq (appLE_topIso_inv_eq_resLE_appTop f V.1 U.1 hUV)
  · exact comp_apply_eq_of_comp_eq (appLE_topIso_inv_eq_resLE_appTop g V.1 V'.1 hV')

/-- **Tor independence of affine schemes is Tor independence of their rings of sections.** -/
private theorem torIndependent_of_isAffine {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsAffine Z] (a : X ⟶ Z) (b : Y ⟶ Z) (ha : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)
    (hb : (⊤ : Y.Opens) ≤ b ⁻¹ᵁ ⊤) :
    letI := (a.appLE ⊤ ⊤ ha).hom.toAlgebra
    letI := (b.appLE ⊤ ⊤ hb).hom.toAlgebra
    Algebra.TorIndependent Γ(Z, ⊤) Γ(X, ⊤) Γ(Y, ⊤) → TorIndependent a b := by
  intro h
  refine ((torIndependent_tfae a b).out 3 1).mp ?_
  exact ⟨PUnit, fun _ => ⊤, by simp, fun _ => isAffineOpen_top _, fun _ =>
    ⟨PUnit, fun _ => ⊤, by simp, fun _ => isAffineOpen_top _,
      PUnit, fun _ => ⊤, by simp, fun _ => isAffineOpen_top _, fun _ _ => h⟩⟩

/-! ### Tor independence at an affine-space chart -/

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **Tor independence passes to an affine-space chart.** Let `U` be an affine open of `X` inside
`f⁻¹(V)` for an affine open `V` of `S`, let `V'` be an affine open of `S'` inside `g⁻¹(V)`, and
let `i : U ⟶ 𝔸(ι; V)` be a morphism over `V` factoring `f|_U`. If `X` and `S'` are Tor
independent over `S`, then `U` and `𝔸(ι; V')` are Tor independent over `𝔸(ι; V)`.

Everything in sight is affine, so by `AlgebraicGeometry.torIndependent_tfae` both the hypothesis
and the conclusion are statements about rings of sections: the hypothesis gives Tor independence
of `Γ(U)` and `Γ(V')` over `Γ(V)`, and the conclusion is Tor independence of `Γ(U)` and
`Γ(V')[ι]` over `Γ(V)[ι]`. The polynomial ring is free over `Γ(V)`, and `Γ(V')[ι]` is its base
change along `Γ(V) ⟶ Γ(V')`, so `Algebra.torIndependent_of_isPushout_of_flat` is exactly the
passage between the two. -/
private theorem torIndependent_affineSpaceChart {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (htor : TorIndependent f g) (V : S.affineOpens) (V' : S'.affineOpens)
    (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (ι : Type u)
    (i : (U.1 : Scheme.{u}) ⟶ 𝔸(ι; (V.1 : Scheme.{u})))
    (hio : i ≫ 𝔸(ι; (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u}) = f.resLE V.1 U.1 hUV) :
    TorIndependent i (AffineSpace.map ι (g.resLE V.1 V'.1 hV')) := by
  have hVa : IsAffine (V.1 : Scheme.{u}) := V.2
  have hV'a : IsAffine (V'.1 : Scheme.{u}) := V'.2
  have hUa : IsAffine (U.1 : Scheme.{u}) := U.2
  set q : (V'.1 : Scheme.{u}) ⟶ (V.1 : Scheme.{u}) := g.resLE V.1 V'.1 hV'
  set fU : (U.1 : Scheme.{u}) ⟶ (V.1 : Scheme.{u}) := f.resLE V.1 U.1 hUV with hfU
  set r := AffineSpace.map ι q with hr
  have hiLE : (⊤ : (U.1 : Scheme.{u}).Opens) ≤ i ⁻¹ᵁ ⊤ := by simp
  have hrLE : (⊤ : (𝔸(ι; (V'.1 : Scheme.{u}))).Opens) ≤ r ⁻¹ᵁ ⊤ := by simp
  -- The algebra structures on the five rings of sections.
  let algRvRv' : Algebra Γ((V.1 : Scheme.{u}), ⊤) Γ((V'.1 : Scheme.{u}), ⊤) :=
    (q.appTop).hom.toAlgebra
  let algRvU : Algebra Γ((V.1 : Scheme.{u}), ⊤) Γ((U.1 : Scheme.{u}), ⊤) :=
    (fU.appTop).hom.toAlgebra
  let algPU : Algebra Γ(𝔸(ι; (V.1 : Scheme.{u})), ⊤) Γ((U.1 : Scheme.{u}), ⊤) :=
    (i.appLE ⊤ ⊤ hiLE).hom.toAlgebra
  let algPP' : Algebra Γ(𝔸(ι; (V.1 : Scheme.{u})), ⊤) Γ(𝔸(ι; (V'.1 : Scheme.{u})), ⊤) :=
    (r.appLE ⊤ ⊤ hrLE).hom.toAlgebra
  let algMvU : Algebra (MvPolynomial ι Γ((V.1 : Scheme.{u}), ⊤)) Γ((U.1 : Scheme.{u}), ⊤) :=
    ((i.appLE ⊤ ⊤ hiLE).hom.comp
      (affineSpaceΓIso ι (V.1 : Scheme.{u})).hom.hom).toAlgebra
  have hbase : (𝔸(ι; (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u})).appTop ≫ i.appTop =
      fU.appTop := by
    rw [← Scheme.Hom.comp_appTop, hio, hfU]
  have towerU : IsScalarTower Γ((V.1 : Scheme.{u}), ⊤)
      (MvPolynomial ι Γ((V.1 : Scheme.{u}), ⊤)) Γ((U.1 : Scheme.{u}), ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change (fU.appTop).hom x =
      (i.appLE ⊤ ⊤ hiLE).hom ((affineSpaceΓIso ι (V.1 : Scheme.{u})).hom (MvPolynomial.C x))
    rw [affineSpaceΓIso_hom_C, appLE_top_top]
    exact (comp_apply_eq_of_comp_eq hbase x).symm
  -- Tor independence ascends to the polynomial rings.
  have htorMv : Algebra.TorIndependent (MvPolynomial ι Γ((V.1 : Scheme.{u}), ⊤))
      Γ((U.1 : Scheme.{u}), ⊤) (MvPolynomial ι Γ((V'.1 : Scheme.{u}), ⊤)) :=
    Algebra.torIndependent_of_isPushout_of_flat Γ((V.1 : Scheme.{u}), ⊤)
      (MvPolynomial ι Γ((V.1 : Scheme.{u}), ⊤)) Γ((U.1 : Scheme.{u}), ⊤)
      Γ((V'.1 : Scheme.{u}), ⊤) (MvPolynomial ι Γ((V'.1 : Scheme.{u}), ⊤))
      (torIndependent_sections_of_torIndependent f g htor V V' hV' U hUV)
  -- Transport to the sections of the two affine spaces.
  have htorP : Algebra.TorIndependent Γ(𝔸(ι; (V.1 : Scheme.{u})), ⊤)
      Γ((U.1 : Scheme.{u}), ⊤) Γ(𝔸(ι; (V'.1 : Scheme.{u})), ⊤) := by
    refine (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).1
      ((torIndependent_congr _ _ _ _ _ _
        (affineSpaceΓIso ι (V.1 : Scheme.{u})).commRingCatIsoToRingEquiv
        (RingEquiv.refl Γ((U.1 : Scheme.{u}), ⊤))
        (affineSpaceΓIso ι (V'.1 : Scheme.{u})).commRingCatIsoToRingEquiv ?_ ?_).mp
        ((RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).2 htorMv))
    · exact fun _ => rfl
    · have hcomm : CommRingCat.ofHom (MvPolynomial.map (q.appTop).hom) ≫
          (affineSpaceΓIso ι (V'.1 : Scheme.{u})).hom =
          (affineSpaceΓIso ι (V.1 : Scheme.{u})).hom ≫ r.appLE ⊤ ⊤ hrLE := by
        rw [appLE_top_top, hr, affineSpaceΓIso_map]
      exact comp_apply_eq_of_comp_eq hcomm
  -- Read the conclusion off the affine criterion.
  exact torIndependent_of_isAffine i r hiLE hrLE htorP

/-- **Tor independence passes to every affine-space chart.** This is the hypothesis of
Stacks 09UR in the form the proof of that lemma uses it. -/
public theorem Scheme.Hom.chartTorIndependence_of_torIndependent {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (htor : TorIndependent f g) : f.ChartTorIndependence g :=
  fun V V' hV' U hUV _ i _ hio =>
    torIndependent_affineSpaceChart f g htor V V' hV' U hUV _ i hio

/-! ### Stacks 09UR -/

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **Stacks 09UR.** Let `f : X ⟶ S` be locally of finite type, let `E` be an object of `D(𝒪_X)`
which is `m`-pseudo-coherent relative to `S`, and let `g : S' ⟶ S` be a morphism of schemes. If
`S'` and `X` are Tor independent over `S`, then the derived pullback of `E` to `X ×_S S'` is
`m`-pseudo-coherent relative to `S'`.

This is `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts`
with its chart hypothesis discharged by
`AlgebraicGeometry.Scheme.Hom.chartTorIndependence_of_torIndependent`, so the Tor independence
assumed here is the one the source assumes.

No hypothesis beyond the source's is assumed. Stacks 0E23, the base change isomorphism stated
as `AlgebraicGeometry.DerivedBaseChangeIsoOfTorIndependent`, is proved —
`AlgebraicGeometry.derivedBaseChangeIsoOfTorIndependent`, from
`Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeMap_of_torIndependent` — so
it is not needed as a hypothesis here. The tag for Stacks 09UR sits here rather than on
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts`,
because the source's hypothesis is Tor independence of `X` and `S'` over `S`, which is what this
statement assumes; the chart form that one assumes is strictly stronger-looking and is derived
here by `AlgebraicGeometry.Scheme.Hom.chartTorIndependence_of_torIndependent`. -/
@[stacks 09UR, sga "6 III 1.10", sga "6 III 1.8" "special case"]
public theorem Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (htor : TorIndependent f g) (hE : f.IsPseudoCoherentFrom E m) :
    (pullback.snd f g).IsPseudoCoherentFrom
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj E) m :=
  Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts f g E m
    (f.chartTorIndependence_of_torIndependent g htor) hE

end AlgebraicGeometry

end
