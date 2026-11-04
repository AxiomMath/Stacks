module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.RingTheory.Artinian.Basic

/-!
# Faithfully flat base change is injective on Picard groups

Let `A → B` be a faithfully flat ring map and let `X` be a scheme over `A` which is
quasi-compact and quasi-separated and whose ring of global functions `R = H⁰(X, 𝒪_X)` is
semi-local. [Stacks, Tag 0CDY](https://stacks.math.columbia.edu/tag/0CDY) says that the
pullback map `Pic(X) → Pic(X_B)` is injective. This file proves it.

The argument is the source's. Let `L` be an invertible `𝒪_X`-module whose pullback to `X_B` is
trivial, and put `M = H⁰(X, L)`, `N = H⁰(X, L^{⊗ -1})`. Tag 0CDX says that `M` and `N` are
invertible `R`-modules and that the multiplication `M ⊗_R N → R` is an isomorphism. Since `R`
is semi-local, `M ≅ R` and `N ≅ R` by Tag 02M9; choosing generators `s ∈ M` and `t ∈ N`, the
product `s t ∈ R` is the image of a generator of `M ⊗_R N` under an isomorphism onto `R`, hence
a unit. A global section of an invertible module whose product with a global section of the
inverse is a unit vanishes nowhere, so by the trivialization clause of Tag 01CY it trivializes
the module; thus `L` is trivial and its Picard class is zero.

## Main results

* `Stacks.SheafOfModules.nonempty_iso_unit_of_tensorPairing_eq_unitSection`: a global section
  of an invertible module on a ringed space with local stalks which pairs to `1` with a global
  section of a tensor inverse trivializes the module. This is the global form of the
  trivialization clause of Tag 01CY.
* `Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_of_isUnit_globalSectionsMulNegOne`: the
  same statement for a scheme, with the pairing written as the multiplication
  `H⁰(X, L) × H⁰(X, L^{⊗ -1}) → H⁰(X, 𝒪_X)` of Tag 01CU in degrees `(1, -1)`.
* `Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_of_isTrivial_pullback_of_semilocal`:
  under the hypotheses of Tag 0CDY, an invertible `𝒪_X`-module whose pullback to `X_B` is
  trivial is itself trivial. This is the content of Tag 0CDY, before it is read in the Picard
  group.
* `Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_faithfullyFlat`:
  **Stacks Project, Tag 0CDY.** The pullback map `Pic(X) → Pic(X_B)` is injective.
* `Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_fieldExtension`:
  **Stacks Project, Tag 0CC5.** The same for a field extension `k'/k` in place of a faithfully
  flat ring map: the pullback map `Pic(X) → Pic(X_{k'})` is injective.
* `Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional`:
  Tag 0CC5 with its parenthetical hypothesis `dim_k H⁰(X, 𝒪_X) < ∞` in place of semi-locality.

## Implementation notes

**The Picard group and its pullback.** The group is `Stacks.Picard.ofScheme`, the isomorphism
classes of invertible `𝒪_X`-modules of Tag 01CX, and the pullback map is
`Stacks.Picard.schemePullbackClassHom`. Injectivity is proved through the kernel: the class of
the structure sheaf is `0` by definition of that group, so a class in the kernel is the class
of an invertible module whose pullback is isomorphic to `𝒪_{X_B}`, which is the triviality
hypothesis Tag 0CDX takes.

**Semi-locality is spelled `Finite (MaximalSpectrum R)`**, as in Mathlib's
`Module.free_of_flat_of_finrank_eq` and in `Module.free_of_flat_of_preconnectedSpace`. The step
"a semi-local ring has trivial Picard group, so an invertible module over it is isomorphic to
the ring", which is the first assertion of Tag 02M9, is Mathlib's
`Module.Invertible.free_iff_linearEquiv` together with its `Subsingleton (CommRing.Pic R)`
instance for a semi-local ring; no rank computation appears here.

**The field-extension case.** A field extension `k'/k` is a ring map `k →+* k'`, and such a map
is faithfully flat because `k'` is a nonzero free `k`-module; so Tag 0CC5 is Tag 0CDY at
`A = k`, `B = k'`. Its parenthetical sufficient condition for semi-locality is Tag 00J6 followed
by Tag 00J7: a finite-dimensional `k`-algebra is Artinian, and an Artinian ring has finitely many
maximal ideals. The `k`-algebra structure that `dim_k H⁰(X, 𝒪_X) < ∞` refers to is the one the
structure morphism puts on global sections, `globalSectionsAlgebra`.

**Two invertibility classes.** The Picard group of Tag 01CX and the nonvanishing locus of Tag
01CY are stated for `Stacks.SheafOfModules.IsInvertible`, while the Tag 01CX multiplication of
Tag 0CDX is stated for `AlgebraicGeometry.SheafOfModules.IsInvertible`. The two are bridged by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, used here in both directions.

**The pairing.** `Stacks.SheafOfModules.tensorPairing` takes an arbitrary trivialization
`ψ : L ⊗ N ≅ 𝒪_X` of a tensor product and reads it on sections. At
`N = L^{⊗ -1}` and `ψ = Stacks.SheafOfModules.Invertible.mulNegOneIso` it *is*
`Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne`, by
`Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify`: the two spellings of the sheafified
sectionwise tensor product agree definitionally, so no comparison map intervenes.

## References

* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 0CDY](https://stacks.math.columbia.edu/tag/0CDY)
* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 00J6](https://stacks.math.columbia.edu/tag/00J6)
* [Stacks Project, Tag 00J7](https://stacks.math.columbia.edu/tag/00J7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)
open Stacks.SheafOfModules.Invertible

namespace Stacks.SheafOfModules

/-- **A global section pairing to `1` trivializes an invertible module.** Let `L` be an
invertible sheaf of modules on a ringed space whose stalks are local rings, let `ψ` trivialize
`L ⊗ N`, and let `s` and `b` be global sections of `L` and of `N` whose product under `ψ` is
the unit section. Then `L` is isomorphic to the structure sheaf.

This is the trivialization clause of [Stacks, Tag 01CY] in global form: the pairing exhibits
every point as a point of the nonvanishing locus of `s`, so multiplication by `s` is bijective
on the sections over every open. -/
theorem nonempty_iso_unit_of_tensorPairing_eq_unitSection
    {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    {L N : _root_.SheafOfModules.{u} (structureSheafRing X)}
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing X))
    (s : L.val.obj (op ⊤)) (b : N.val.obj (op ⊤))
    (h : tensorPairing ψ ⊤ s b = unitSection X ⊤) :
    Nonempty (L ≅ _root_.SheafOfModules.unit (structureSheafRing X)) := by
  have hall : ∀ x : X.carrier, x ∈ nonvanishingLocus L (sectionsOfTop L s) := fun x =>
    (mem_nonvanishingLocus_iff ψ (sectionsOfTop L s) x).2
      ⟨⊤, Opens.mem_top x, b, by rw [sectionsOfTop_eval_top]; exact h⟩
  have hiso : IsIso (L.unitHomEquiv.symm (sectionsOfTop L s)) := by
    refine isIso_of_isIso_val_app _ fun A => ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_smul_eval_of_le_nonvanishingOpen L (sectionsOfTop L s) A.unop
      (fun y _ => hall y)
  exact ⟨(asIso (L.unitHomEquiv.symm (sectionsOfTop L s))).symm⟩

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.PicardBaseChange

/-- A linear automorphism of a commutative ring, viewed as a module over itself, carries `1` to
a unit: it is multiplication by that value, and the inverse automorphism supplies an inverse. -/
theorem isUnit_linearEquiv_one {R : Type u} [CommRing R] (g : R ≃ₗ[R] R) : IsUnit (g 1) := by
  have h : g 1 * g.symm 1 = 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, g.symm_apply_apply]
  exact IsUnit.of_mul_eq_one _ h

variable {X : Scheme.{u}} (L : X.Modules)
  [hL : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- The multiplication of a global section of `L` against a global section of `L^{⊗ -1}` is
linear in the second argument. -/
theorem globalSectionsMulNegOne_smul_right (s : Γ(L, ⊤)) (c : Γ(X, ⊤))
    (t : Γ(tensorPowerModule L (-1), ⊤)) :
    globalSectionsMulNegOne L s (c • t) = c * globalSectionsMulNegOne L s t := by
  rw [← globalSectionsMulNegOneLinear_tmul, ← globalSectionsMulNegOneLinear_tmul,
    TensorProduct.tmul_smul, map_smul, smul_eq_mul]

/-- **A global section of an invertible module whose product with a global section of the
inverse is a unit trivializes the module.** The multiplication is the one of [Stacks, Tag 01CU]
in degrees `(1, -1)`, which is the multiplication [Stacks, Tag 0CDX] asserts to be an
isomorphism; this is the step by which [Stacks, Tag 0CDY] passes from a unit of
`H⁰(X, 𝒪_X)` to a trivialization of `L`. -/
theorem isTrivial_of_isUnit_globalSectionsMulNegOne (s : Γ(L, ⊤))
    (t : Γ(tensorPowerModule L (-1), ⊤))
    (hst : IsUnit (globalSectionsMulNegOne L s t)) :
    _root_.AlgebraicGeometry.SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property L := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  obtain ⟨u, hu⟩ := hst
  refine Stacks.SheafOfModules.nonempty_iso_unit_of_tensorPairing_eq_unitSection
    (X := X.toRingedSpace) (mulNegOneIso X.presheaf X.ringCatSheaf.property L)
    s (((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • t) ?_
  rw [show Stacks.SheafOfModules.tensorPairing
        (mulNegOneIso X.presheaf X.ringCatSheaf.property L) ⊤ s
        (((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • t)
      = globalSectionsMulNegOne L s (((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • t) from
    Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify X.presheaf
      X.ringCatSheaf.property L (op ⊤) s _]
  rw [globalSectionsMulNegOne_smul_right, ← hu]
  exact u.inv_mul

/-- **An invertible module that becomes trivial after a faithfully flat base change is
trivial**, when `X` is quasi-compact and quasi-separated over `A` and `H⁰(X, 𝒪_X)` is
semi-local. This is the content of [Stacks, Tag 0CDY]: the global sections of `L` and of
`L^{⊗ -1}` are invertible `H⁰(X, 𝒪_X)`-modules with an isomorphism onto `H⁰(X, 𝒪_X)` given by
multiplication (Tag 0CDX), semi-locality makes both free of rank one (Tag 02M9), and the
product of two generators is therefore a unit. -/
theorem isTrivial_of_isTrivial_pullback_of_semilocal
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (MaximalSpectrum Γ(X, ⊤))]
    (hLtriv : _root_.AlgebraicGeometry.SheafOfModules.IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L)) :
    _root_.AlgebraicGeometry.SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property L := by
  obtain ⟨e, he⟩ :=
    exists_mulEquiv_globalSections_of_faithfullyFlat_trivialization φ hφ f L hLtriv
  have hinvM : Module.Invertible Γ(X, ⊤) Γ(L, ⊤) :=
    invertible_globalSections_of_faithfullyFlat_trivialization φ hφ f L hLtriv
  have hinvN : Module.Invertible Γ(X, ⊤) Γ(tensorPowerModule L (-1), ⊤) :=
    invertible_globalSections_tensorInverse_of_faithfullyFlat_trivialization φ hφ f L hLtriv
  obtain ⟨eM⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Γ(X, ⊤) Γ(L, ⊤))
  obtain ⟨eN⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Γ(X, ⊤) Γ(tensorPowerModule L (-1), ⊤))
  refine isTrivial_of_isUnit_globalSectionsMulNegOne L (eM.symm 1) (eN.symm 1) ?_
  rw [← he]
  have hg : ((TensorProduct.lid Γ(X, ⊤) Γ(X, ⊤)).symm.trans
        ((TensorProduct.congr eM.symm eN.symm).trans e)) 1
      = e ((eM.symm 1) ⊗ₜ[Γ(X, ⊤)] (eN.symm 1)) := by
    simp
  rw [← hg]
  exact isUnit_linearEquiv_one _

variable (X) in
/-- **Stacks Project, Tag 0CDY.** Let `A → B` be a faithfully flat ring map and let `X` be a
scheme over `A` which is quasi-compact and quasi-separated and whose ring of global functions
`H⁰(X, 𝒪_X)` is semi-local. Then the pullback map `Pic(X) → Pic(X_B)` is injective. -/
@[stacks 0CDY]
theorem injective_picardPullback_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (MaximalSpectrum Γ(X, ⊤))] :
    Function.Injective (Stacks.Picard.schemePullbackClassHom
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  obtain ⟨M, hM⟩ : ∃ M : Stacks.SheafOfModules.InvertibleModules X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace),
      Stacks.SheafOfModules.picardClass X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)
        M.obj M.property = a :=
    ⟨Stacks.Picard.picardRepresentative X.toRingedSpace a,
      Stacks.Picard.classOf_picardRepresentative X.toRingedSpace a⟩
  have hinvAG : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.property M.obj :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ M.property
  have hzero : ∀ Y : Scheme.{u}, (0 : Stacks.Picard.ofScheme Y) =
      Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
        (_root_.SheafOfModules.unit _)
        (Stacks.SheafOfModules.isInvertible_unit _ _) := fun _ => rfl
  have hpull : _root_.AlgebraicGeometry.SheafOfModules.IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj M.obj) := by
    refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
      (Stacks.RingedSpace.modulePullback_isInvertible_of
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).toLRSHom.toShHom M.obj M.property)
      (Stacks.SheafOfModules.isInvertible_unit _ _)).1 ?_
    rw [← Stacks.Picard.pullbackClass_classOf
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).toLRSHom.toShHom M.obj M.property,
      hM, ← hzero]
    exact ha
  have htriv := isTrivial_of_isTrivial_pullback_of_semilocal M.obj φ hφ f hpull
  rw [← hM, hzero X]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ M.property
    (Stacks.SheafOfModules.isInvertible_unit _ _)).2 htriv

/-- A ring map from a field to a nonzero commutative ring is faithfully flat: the target is a
nonzero free module over the field. In particular a field extension `k'/k` is faithfully flat. -/
@[ega "0 6.4.2" "special case", ega "IV 8.1.2" "partial", ega "IV 9.1.3" "more general"]
theorem faithfullyFlat_of_field {k R : Type u} [Field k] [CommRing R] [Nontrivial R]
    (φ : k →+* R) : φ.FaithfullyFlat :=
  let : Algebra k R := φ.toAlgebra
  (RingHom.faithfullyFlat_algebraMap_iff (R := k) (S := R)).mpr inferInstance

/-- A finite-dimensional algebra over a field is semi-local: it is Artinian
([Stacks, Tag 00J6]) and an Artinian ring has only finitely many maximal ideals
([Stacks, Tag 00J7]). -/
theorem finite_maximalSpectrum_of_finiteDimensional (k R : Type u) [Field k] [CommRing R]
    [Algebra k R] [FiniteDimensional k R] : Finite (MaximalSpectrum R) :=
  have : IsArtinianRing R := finite_dimensional_algebra_is_artinian k R
  inferInstance

/-- The algebra structure that a morphism `f : X ⟶ Spec k` puts on the global functions
`H⁰(X, 𝒪_X)`, namely the one given by the ring map `k = H⁰(Spec k, 𝒪) → H⁰(X, 𝒪_X)` on global
sections. -/
@[instance_reducible]
def globalSectionsAlgebra {k : Type u} [CommRing k] (f : X ⟶ Spec (.of k)) :
    Algebra k Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra

variable (X) in
/-- **Stacks Project, Tag 0CC5.** Let `k'/k` be a field extension and let `X` be a scheme over
`k` such that (1) `X` is quasi-compact and quasi-separated, and (2) `R = H⁰(X, 𝒪_X)` is
semi-local. Then the pullback map `Pic(X) → Pic(X_{k'})` is injective. -/
@[stacks 0CC5 "The lemma proper; the parenthetical sufficient condition \
`dim_k H⁰(X, 𝒪_X) < ∞` for semi-locality is \
`injective_picardPullback_of_finiteDimensional`"]
theorem injective_picardPullback_of_fieldExtension
    {k k' : Type u} [Field k] [Field k'] (φ : k →+* k')
    (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (MaximalSpectrum Γ(X, ⊤))] :
    Function.Injective (Stacks.Picard.schemePullbackClassHom
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
  injective_picardPullback_of_faithfullyFlat X φ (faithfullyFlat_of_field φ) f

variable (X) in
/-- **Stacks Project, Tag 0CC5** with its parenthetical hypothesis: hypothesis (2) holds as soon
as `dim_k H⁰(X, 𝒪_X)` is finite, `H⁰(X, 𝒪_X)` being then Artinian and hence semi-local. -/
@[stacks 0CC5 "The parenthetical sufficient condition `dim_k H⁰(X, 𝒪_X) < ∞` for \
hypothesis (2); the lemma proper is `injective_picardPullback_of_fieldExtension`"]
theorem injective_picardPullback_of_finiteDimensional
    {k k' : Type u} [Field k] [Field k'] (φ : k →+* k')
    (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (hfd : letI := globalSectionsAlgebra f; FiniteDimensional k Γ(X, ⊤)) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
  let := globalSectionsAlgebra f
  have : FiniteDimensional k Γ(X, ⊤) := hfd
  have := finite_maximalSpectrum_of_finiteDimensional k Γ(X, ⊤)
  injective_picardPullback_of_fieldExtension X φ f

end Stacks.AlgebraicGeometry.PicardBaseChange

end
