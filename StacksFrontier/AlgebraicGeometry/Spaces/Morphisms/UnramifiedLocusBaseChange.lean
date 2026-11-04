module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified locus and base change

The locus of points at which a morphism of algebraic spaces locally of finite type is unramified
commutes with base change: for a cartesian square of algebraic spaces over `S`, the unramified
locus of the base change is the inverse image of the unramified locus of the morphism. This file
proves that comparison, together with the commutative algebra and the scheme-level statement it
rests on.

The comparison is the content of the second part of [Stacks Project, Tag 05W2]; the open
subspace it compares is part (1) of that tag, which is
`AlgebraicGeometry.Space.unramifiedLocus`. The statement here is deliberately left untagged: it
is an input, phrased as an equality of sets of points, and the tag belongs with the open
subspaces.

## Main definitions

No new definitions are introduced.

## Main results

* `Algebra.isUnramifiedAt_iff_of_isPushout`: for a base change of an algebra of finite type,
  unramifiedness at a prime and at its image agree.
* `AlgebraicGeometry.unramifiedAt_iff_isUnramifiedAt_primeIdealOf` and
  `AlgebraicGeometry.unramifiedAt_iff_formallyUnramified_stalkMap` read unramifiedness of a
  morphism of schemes locally of finite type at a point off any compatible pair of affine charts,
  and off the stalk map.
* `AlgebraicGeometry.unramifiedAt_isPullback_iff` is the comparison for morphisms of schemes.
* `AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty` identifies unramifiedness at
  a point with the germ property of Stacks 04R6 induced by unramifiedness.
* `AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback` is the comparison for
  morphisms of algebraic spaces, the second part of Stacks 05W2.

## Implementation notes

The ring-level comparison is the vanishing of a fibre of the module of differentials. The
unramified locus of an algebra is the complement of the support of its differentials
(`Algebra.unramifiedLocus_eq_compl_support`), the differentials of a base change are the base
change of the differentials (`KaehlerDifferential.tensorKaehlerEquiv`), and for an algebra of
finite type the support is detected by residue-field fibres, which a field extension does not
change because it is faithfully flat. The hypothesis of finite type is what makes the support
closed and is the reason the comparison needs it.

Passing from rings to schemes is the pattern of
`AlgebraicGeometry.quasiFiniteAt_isPullback_iff`: a cartesian square of affines is produced from
the chosen affine charts by `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`, its sections form a
pushout of rings by `AlgebraicGeometry.isPushout_appTop_of_isPullback`, and unramifiedness at a
point is read on the chart by `unramifiedAt_iff_isUnramifiedAt_primeIdealOf`. That chart
independence is itself proved through the stalk map, whose formal unramifiedness is the
chart-free form of the condition; it is also what makes restriction along an open immersion
invisible, which is what the germ description needs.

Passing from schemes to algebraic spaces is the pattern of
`AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback`: compatible surjective
étale charts of the cartesian square give a cartesian square of morphisms of schemes, a
field-valued point of the chart of the fibre product makes both squares into pointed charts whose
selected scheme points correspond, and unramifiedness of morphisms of schemes being étale local
on the source and target (Stacks 04QZ), unramifiedness at a point may be read off any one pointed
chart (Stacks 04NC).

## References

* [Stacks Project, Tag 01TM](https://stacks.math.columbia.edu/tag/01TM)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R6](https://stacks.math.columbia.edu/tag/04R6)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

/-! ### Base change of unramifiedness at a prime -/

/-- Being unramified at a prime is non-membership of the support of the module of
differentials. -/
private lemma Algebra.isUnramifiedAt_iff_notMem_support
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (q : Ideal A) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ↔
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) ∉ Module.support A Ω[A⁄R] := by
  rw [← Set.mem_compl_iff, ← Algebra.unramifiedLocus_eq_compl_support]
  exact Iff.rfl

/-- For an algebra essentially of finite type, being unramified at a prime is the vanishing of
the residue-field fibre of the module of differentials there. -/
private lemma Algebra.isUnramifiedAt_iff_not_nontrivial
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    (q : Ideal A) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ↔ ¬ Nontrivial (q.ResidueField ⊗[A] Ω[A⁄R]) := by
  rw [Algebra.isUnramifiedAt_iff_notMem_support,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]

section Pushout

variable {R S A C : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra S C] [Algebra A C]
    [IsScalarTower R A C] [IsScalarTower R S C]
    [Algebra.IsPushout R S A C] [Algebra.FiniteType R A]

omit [Algebra.FiniteType R A] in
/-- The residue-field fibre of `Ω[C⁄S]` at a prime of a base change is nontrivial exactly when
the residue-field fibre of `Ω[A⁄R]` at its image is: the differentials of a base change are the
base change of the differentials, and a field extension is faithfully flat. -/
private lemma Algebra.nontrivial_residueField_tensor_kaehler_iff
    (qA : Ideal A) [qA.IsPrime] (qC : Ideal C) [qC.IsPrime]
    (hq : qA = qC.comap (algebraMap A C)) :
    Nontrivial (qC.ResidueField ⊗[C] Ω[C⁄S]) ↔ Nontrivial (qA.ResidueField ⊗[A] Ω[A⁄R]) := by
  let inst : Algebra qA.ResidueField qC.ResidueField :=
    (Ideal.ResidueField.map qA qC (algebraMap A C) hq).toAlgebra
  have tower : IsScalarTower A qA.ResidueField qC.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    refine RingHom.ext fun x ↦ ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A C qC.ResidueField]
    exact (Ideal.ResidueField.map_algebraMap qA qC (algebraMap A C) hq x).symm
  let e₁ : qC.ResidueField ⊗[C] Ω[C⁄S] ≃ₗ[C] qC.ResidueField ⊗[C] (C ⊗[A] Ω[A⁄R]) :=
    _root_.TensorProduct.congr (LinearEquiv.refl C _)
      (KaehlerDifferential.tensorKaehlerEquiv R S A C).symm
  let e₂ := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A C qC.ResidueField
    qC.ResidueField Ω[A⁄R]
  let e₃ := (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A qA.ResidueField
    qC.ResidueField qC.ResidueField Ω[A⁄R]).symm
  rw [e₁.nontrivial_congr, e₂.nontrivial_congr, e₃.nontrivial_congr,
    Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]

/-- **Unramifiedness at a prime is invariant under base change.** For `C` the base change of an
algebra `A` of finite type over `R` along `R → S`, and a prime of `C` over a prime of `A`, the
base change is unramified at the first exactly when `A` is unramified at the second.

Both sides are the vanishing of a residue-field fibre of a module of differentials, and the two
fibres differ by the extension of residue fields, which is faithfully flat. -/
@[sga "1 I 3.5" "(iii), special case"]
theorem Algebra.isUnramifiedAt_iff_of_isPushout
    (qA : Ideal A) [qA.IsPrime] (qC : Ideal C) [qC.IsPrime]
    (hq : qA = qC.comap (algebraMap A C)) :
    Algebra.IsUnramifiedAt S qC ↔ Algebra.IsUnramifiedAt R qA := by
  have : Algebra.EssFiniteType S C :=
    (Algebra.EssFiniteType.iff_of_algEquiv (Algebra.IsPushout.equiv R S A C)).mp inferInstance
  rw [Algebra.isUnramifiedAt_iff_not_nontrivial (R := S) qC,
    Algebra.isUnramifiedAt_iff_not_nontrivial (R := R) qA,
    Algebra.nontrivial_residueField_tensor_kaehler_iff (R := R) (S := S) qA qC hq]

end Pushout

namespace AlgebraicGeometry

/-! ### Unramifiedness at a point of a scheme, read off charts and off the stalk -/

/-- For a morphism locally of finite type, unramifiedness at a point is unramifiedness of the
induced algebra of sections at the corresponding prime, on *any* compatible pair of affine
opens.

The forward direction goes through the stalk map, which the chart supplied by
`AlgebraicGeometry.UnramifiedAt` and the given chart both compute
(`AlgebraicGeometry.formallyUnramified_stalkMap_iff`). The backward direction shrinks the given
chart to a basic open on which the sections become genuinely unramified, by
`Algebra.exists_unramified_of_isUnramifiedAt`; finite type of the sections, which that needs, is
`AlgebraicGeometry.Scheme.Hom.finiteType_appLE`. -/
@[ega "IV 17.4.1" "more general", ega "IV 17.4.1.2" "a ⇔ e"]
theorem unramifiedAt_iff_isUnramifiedAt_primeIdealOf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (V : Y.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hU : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U) :
    UnramifiedAt f x ↔
      letI := (f.appLE V U e).hom.toAlgebra
      Algebra.IsUnramifiedAt Γ(Y, V) (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU e
  constructor
  · rintro ⟨U₀, hU₀, hx₀, V₀, hV₀, e₀, H⟩
    refine (formallyUnramified_stalkMap_iff V hV U hU e hx).mp ?_
    let : Algebra Γ(Y, V₀) Γ(X, U₀) := (f.appLE V₀ U₀ e₀).hom.toAlgebra
    have : Algebra.FormallyUnramified Γ(Y, V₀) Γ(X, U₀) := H.formallyUnramified
    exact (formallyUnramified_stalkMap_iff V₀ hV₀ U₀ hU₀ e₀ hx₀).mpr
      (Algebra.FormallyUnramified.comp Γ(Y, V₀) Γ(X, U₀) _)
  · intro hq
    have : Algebra.IsUnramifiedAt Γ(Y, V) (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hq
    obtain ⟨r, hr, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt (R := Γ(Y, V))
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    let e' : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans e
    refine ⟨X.basicOpen r, hU.basicOpen r, ?_, V, hV, e', ?_⟩
    · show (⟨x, hx⟩ : U).1 ∈ X.basicOpen r
      rw [← hU.fromSpec_primeIdealOf ⟨x, hx⟩]
      show hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]
      exact hr
    · have := hU.isLocalization_basicOpen r
      let : Algebra Γ(Y, V) Γ(X, X.basicOpen r) :=
        (f.appLE V (X.basicOpen r) e').hom.toAlgebra
      refine ⟨?_, f.finiteType_appLE hV (hU.basicOpen r) e'⟩
      have hur' := hur.formallyUnramified
      rw [← RingHom.formallyUnramified_algebraMap] at hur'
      rw [← RingHom.formallyUnramified_algebraMap]
      convert! RingHom.FormallyUnramified.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hur'
      ext
      dsimp
      rw [IsScalarTower.algebraMap_apply Γ(Y, V) Γ(X, U) (Localization _),
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).commutes]
      exact DFunLike.congr_fun
        (CommRingCat.hom_ext_iff.mp (f.appLE_map e (homOfLE (X.basicOpen_le r)).op).symm) _

/-- For a morphism locally of finite type, unramifiedness at a point is formal unramifiedness of
the stalk map there. -/
theorem unramifiedAt_iff_formallyUnramified_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔ (f.stalkMap x).hom.FormallyUnramified := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).2
  exact (unramifiedAt_iff_isUnramifiedAt_primeIdealOf f V hV U hU hUV hxU).trans
    (formallyUnramified_stalkMap_iff V hV U hU hUV hxU).symm

/-- Restricting a morphism locally of finite type to a compatible pair of opens does not change
where it is unramified. -/
theorem unramifiedAt_resLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (x : V.toScheme) :
    UnramifiedAt (f.resLE U V hVU) x ↔ UnramifiedAt f (V.ι x) := by
  have : LocallyOfFiniteType (f.resLE U V hVU) := instLocallyOfFiniteTypeResLE f V U hVU
  rw [unramifiedAt_iff_formallyUnramified_stalkMap, unramifiedAt_iff_formallyUnramified_stalkMap]
  exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap hVU x)

/-- The `appLE` of a morphism between the top opens is its `appTop`. -/
private lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ (by simp) = f.appTop := Scheme.Hom.appLE_eq_app f

/-- The `appTop` form of `AlgebraicGeometry.unramifiedAt_iff_isUnramifiedAt_primeIdealOf`, for an
affine scheme over an affine scheme. -/
theorem unramifiedAt_iff_isUnramifiedAt_primeIdealOf_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hY : IsAffineOpen (⊤ : Y.Opens)) (hX : IsAffineOpen (⊤ : X.Opens))
    (x : X) :
    UnramifiedAt f x ↔
      letI := f.appTop.hom.toAlgebra
      Algebra.IsUnramifiedAt Γ(Y, ⊤) (hX.primeIdealOf ⟨x, by simp⟩).asIdeal := by
  rw [← appLE_top_top]
  exact unramifiedAt_iff_isUnramifiedAt_primeIdealOf f (⊤ : Y.Opens) hY (⊤ : X.Opens) hX
    (by simp) (x := x) (by simp)

/-! ### Base change of unramifiedness at a point of a scheme -/

/-- The affine case: in a cartesian square of affine schemes, the base change of a morphism
locally of finite type is unramified at a point exactly when the original morphism is unramified
at its image.

The sections of a cartesian square of affines form a pushout of rings
(`AlgebraicGeometry.isPushout_appTop_of_isPullback`), so this is
`Algebra.isUnramifiedAt_iff_of_isPushout` read through
`AlgebraicGeometry.unramifiedAt_iff_isUnramifiedAt_primeIdealOf_top`. -/
private lemma unramifiedAt_isPullback_of_isAffine {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) [LocallyOfFiniteType f] (p : P) :
    UnramifiedAt f (fst p) ↔ UnramifiedAt snd p := by
  have : LocallyOfFiniteType snd :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h ‹LocallyOfFiniteType f›
  have : IsAffine P := IsAffine.of_isPullback h
  let hX : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let hY : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
  let hZ : IsAffineOpen (⊤ : Z.Opens) := isAffineOpen_top Z
  let hP : IsAffineOpen (⊤ : P.Opens) := isAffineOpen_top P
  let R := (Γ(Z, ⊤)).1
  let A := (Γ(X, ⊤)).1
  let B := (Γ(Y, ⊤)).1
  let C := (Γ(P, ⊤)).1
  let qA : Ideal A := (hX.primeIdealOf ⟨fst p, by simp⟩).asIdeal
  let qC : Ideal C := (hP.primeIdealOf ⟨p, by simp⟩).asIdeal
  algebraize [f.appTop.hom, g.appTop.hom, fst.appTop.hom, snd.appTop.hom]
  let : Algebra R C := (fst.appTop.hom.comp f.appTop.hom).toAlgebra
  let : IsScalarTower R A C := .of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R B C := .of_algebraMap_eq (by
    intro r
    have hcat : f.appTop ≫ fst.appTop = g.appTop ≫ snd.appTop := by
      simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h.w
    have hw := congrArg (fun k : Γ(Z, ⊤) ⟶ Γ(P, ⊤) => (CommRingCat.Hom.hom k) r) hcat
    simpa [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using hw)
  let : Algebra.IsPushout R B A C := by
    apply CommRingCat.isPushout_iff_isPushout.mp
    simpa [R, A, B, C, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      (isPushout_appTop_of_isPullback h).flip
  have : Algebra.FiniteType R A := by
    have hft := f.finiteType_appLE hZ hX (by simp)
    rwa [appLE_top_top] at hft
  have hcomap : qA = qC.comap (algebraMap A C) := by
    have hpoint := IsAffineOpen.comap_primeIdealOf_appLE ⊤ hX ⊤ hP
      (f := fst) (x := p) (by simp) (by simp)
    have hideal := congrArg (fun z : PrimeSpectrum A => z.asIdeal) hpoint
    simpa [qA, qC, appLE_top_top, RingHom.algebraMap_toAlgebra] using hideal.symm
  exact ((unramifiedAt_iff_isUnramifiedAt_primeIdealOf_top f hZ hX (fst p)).trans
    (Algebra.isUnramifiedAt_iff_of_isPushout (R := R) (S := B) (A := A) (C := C)
      qA qC hcomap).symm).trans
    (unramifiedAt_iff_isUnramifiedAt_primeIdealOf_top snd hY hP p).symm

/-- **The unramified locus of a morphism of schemes commutes with base change.** In a cartesian
square, the base change of a morphism locally of finite type is unramified at a point exactly
when the original morphism is unramified at its image.

Affine opens around the three images of the point cut out a cartesian square of affines
(`AlgebraicGeometry.Scheme.Hom.isPullback_resLE`), where the statement is
`unramifiedAt_isPullback_of_isAffine`; restricting to opens does not move the unramified locus
(`AlgebraicGeometry.unramifiedAt_resLE_iff`). -/
@[ega "IV 17.7.2" "more general",
  ega "IV 17.7.4" "(iv), special case",
  ega "IV 17.8.3" "more general", sga "3 VIB 2.8" "(v) ⇔ (vi), partial"]
theorem unramifiedAt_isPullback_iff {X Y Y' X' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [LocallyOfFiniteType f] (sq : IsPullback g' f' f g) (x' : X') :
    UnramifiedAt f' x' ↔ UnramifiedAt f (g' x') := by
  have hsquare : f (g' x') = g (f' x') := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : X' ⟶ Y => k x') sq.w
  obtain ⟨-, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g' x'))) isOpen_univ
  have hs'U : f' x' ∈ g ⁻¹ᵁ U := by
    show g (f' x') ∈ U
    exact hsquare ▸ hsU
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsU (f ⁻¹ᵁ U).2
  obtain ⟨-, ⟨W, hW, rfl⟩, hs'W, hWU⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hs'U (g ⁻¹ᵁ U).2
  let V' : X'.Opens := g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W
  let pV : Scheme.Opens.toScheme V := ⟨g' x', hxV⟩
  let p' : Scheme.Opens.toScheme V' := ⟨x', hxV, hs'W⟩
  have hres := Scheme.Hom.isPullback_resLE sq hWU hVU (UY := V') rfl
  have : LocallyOfFiniteType f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFiniteType f›
  have : IsAffine (Scheme.Opens.toScheme V) := hV
  have : IsAffine (Scheme.Opens.toScheme W) := hW
  have : IsAffine (Scheme.Opens.toScheme U) := hU
  have : LocallyOfFiniteType (f.resLE U V hVU) := instLocallyOfFiniteTypeResLE f V U hVU
  have hloc := unramifiedAt_isPullback_of_isAffine hres p'
  have hpointV : (g'.resLE V V' (by simp [V'])) p' = pV :=
    Subtype.ext (g'.coe_resLE_apply (e := by simp [V']) p')
  rw [hpointV] at hloc
  exact (unramifiedAt_resLE_iff f' W V' (by simp [V']) p').symm.trans
    (hloc.symm.trans (unramifiedAt_resLE_iff f U V hVU pV))

/-! ### The germ form of unramifiedness at a point of a scheme -/

/-- Unramifiedness of a morphism locally of finite type at a point of an open subscheme of its
source is unramifiedness of the morphism itself at the image point: the two stalk maps differ by
the isomorphism of stalks induced by the open immersion. -/
theorem unramifiedAt_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {W : X.Opens} (hW : Unramified (W.ι ≫ f)) (y : W.toScheme) : UnramifiedAt f (W.ι y) := by
  have hfu : FormallyUnramified (W.ι ≫ f) :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mp hW).2
  have hst := FormallyUnramified.stalkMap (W.ι ≫ f) y
  rw [Scheme.Hom.stalkMap_comp W.ι f y] at hst
  exact (unramifiedAt_iff_formallyUnramified_stalkMap f _).mpr
    ((RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ (W.ι.stalkMap y)).mp hst)

/-- A morphism of schemes locally of finite type is unramified at a point exactly when the germ
it defines there has a representative which is unramified.

Both directions are the open unramified locus of
`AlgebraicGeometry.isOpen_setOf_unramifiedAt`: it is an open neighbourhood of every point of
unramifiedness over which the morphism is unramified
(`AlgebraicGeometry.unramified_ι_comp_of_forall_unramifiedAt`), and conversely a representative
which is unramified is unramified at the point itself. -/
theorem unramifiedAt_iff_hasRepresentativeWithProperty {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔
      MorphismOfGerms.HasRepresentativeWithProperty
        (@AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
        (MorphismOfGerms.ofSchemeHom f x) := by
  constructor
  · intro hx
    let W : X.Opens := ⟨{y | UnramifiedAt f y}, isOpen_setOf_unramifiedAt f⟩
    have hWx : x ∈ W := hx
    exact ⟨{ source := W, mem_source := hWx, hom := W.ι ≫ f, map_point := rfl },
      MorphismOfGerms.mk_eq_mk_iff.mpr ⟨W, hWx, le_rfl, le_top, by simp⟩,
      unramified_ι_comp_of_forall_unramifiedAt f W fun y hy => hy⟩
  · rintro ⟨r, hr, hP⟩
    have hagree : r.AgreeNear
        ({ source := ⊤, mem_source := by simp, hom := X.topIso.hom ≫ f,
            map_point := rfl } : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) :=
      MorphismOfGerms.mk_eq_mk_iff.mp hr
    obtain ⟨W, hxW, hWr, hWtop, heq⟩ := hagree
    have hrestrict : W.ι ≫ f = X.homOfLE hWr ≫ r.hom := by
      rw [heq, ← Category.assoc]
      exact (congrArg (fun k => k ≫ f) (by simp : X.homOfLE hWtop ≫ X.topIso.hom = W.ι)).symm
    have hle : Unramified (X.homOfLE hWr) := by
      rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
      exact ⟨inferInstance, inferInstance⟩
    have hW : Unramified (W.ι ≫ f) := by
      rw [hrestrict]
      exact MorphismProperty.comp_mem @Unramified _ _ hle hP
    exact unramifiedAt_comp_ι f hW ⟨x, hxW⟩

/-! ### The unramified locus of a morphism of algebraic spaces commutes with base change -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Unramifiedness of a morphism of algebraic spaces over `S` at a point of its source is the
pointed-chart condition of Stacks 04NC for the germ property induced by unramifiedness of
morphisms of schemes.

The two sides are the same existential statement read with the point condition inside or outside
the witnessing open subspace. -/
theorem isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) :
    IsUnramifiedAt B S hS f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (MorphismOfGerms.HasRepresentativeWithProperty
          (@AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})) f x := by
  rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    (@AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget hX hY f x]
  exact ⟨fun ⟨U, hU, y, hy, hq⟩ => ⟨U, hU, ⟨y, hy⟩, hq⟩,
    fun ⟨U, hU, ⟨y, hy⟩, hq⟩ => ⟨U, hU, y, hy, hq⟩⟩

/-- Unramifiedness of a morphism of algebraic spaces at a point is unramifiedness at the selected
scheme point of the scheme morphism of any one pointed étale chart. -/
private theorem isUnramifiedAt_iff_unramifiedAt_of_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {x : points B S hS X} (c : EtaleChartAtPoint B S hS f x)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h)] :
    IsUnramifiedAt B S hS f x ↔
      UnramifiedAt ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) := by
  rw [isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY,
    unramifiedAt_iff_hasRepresentativeWithProperty]
  exact ⟨fun h => h c, fun h => (holdsOnEveryEtaleChartAtPoint_iff_some B S hS _
    (MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      unramified_isEtaleLocalOnSourceAndTarget) hX hY _ _).mpr ⟨c, h⟩⟩

/-- **Stacks 05W2, part (2).** For a morphism of algebraic spaces over `S` which is locally of
finite type, the locus of unramifiedness of a base change is the inverse image of the locus of
unramifiedness of the morphism.

Compatible surjective étale charts of the cartesian square
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`) give a chart `V` of the target, a
chart `U ⟶ V` of `f`, a chart `V' ⟶ V` of `g` and the induced chart `U' = U ×_V V' ⟶ V'` of the
base change, with `U'` an atlas of the fibre product. A field-valued point of `U'` lying over the
given point of `|X₁|` turns the two squares into pointed étale charts of `f'` at that point and
of `f` at its image, whose selected scheme points correspond under `U' ⟶ U`. Unramifiedness of
morphisms of schemes being étale local on the source and target (Stacks 04QZ), unramifiedness at
a point is the induced germ condition read in any one pointed chart (Stacks 04NC), so each side
becomes unramifiedness of a morphism of schemes at corresponding points of a cartesian square of
schemes, which is `AlgebraicGeometry.unramifiedAt_isPullback_iff`.

This statement is left untagged: tag 05W2 is carried by the open subspaces
`AlgebraicGeometry.Space.unramifiedLocus` and
`AlgebraicGeometry.Space.range_pointsMap_unramifiedLocus`. -/
theorem setOf_isUnramifiedAt_eq_preimage_of_isPullback
    {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    {x' | IsUnramifiedAt B S hS f'.hom x'} =
      pointsMap B S hS X₁.1 g'.hom ⁻¹' {x | IsUnramifiedAt B S hS f.hom x} := by
  let T := BigFppfOver.toScheme B S hS
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  have hQcomp := MorphismProperty.relative_isStableUnderComposition
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS f g
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heSnd : e.hom ≫ pullback.snd f.hom g.hom = f'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = pullback.snd f.hom g.hom := by
    rw [← heSnd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hAEtale := MorphismProperty.comp_mem _ a (pullback.snd v f.hom) haEtale
    (hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale)
  have hBEtale := MorphismProperty.comp_mem _ b (pullback.snd v g.hom) hbEtale
    (hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale)
  have hcXEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (c ≫ e.inv) :=
    have _ : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
    MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
  have hcommF : yoneda.map p ≫ v = (a ≫ pullback.snd v f.hom) ≫ f.hom := by
    calc yoneda.map p ≫ v = (a ≫ pullback.fst v f.hom) ≫ v := by rw [← hap]
      _ = (a ≫ pullback.snd v f.hom) ≫ f.hom := by
          simp only [Category.assoc, pullback.condition]
  have hcommF' : yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = (c ≫ e.inv) ≫ f'.hom := by
    calc yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = c ≫ pullback.snd f.hom g.hom := by
          simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f'.hom := by rw [Category.assoc, heInvSnd]
  have hpLFT : LocallyOfFiniteType (T.map p) :=
    hf U V (a ≫ pullback.snd v f.hom) v p hAEtale hvEtale hcommF
  have _ : LocallyOfFiniteType (T.map pV') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcharts hpLFT
  have hscheme : ∀ w : T.obj U',
      UnramifiedAt (T.map pV') w ↔ UnramifiedAt (T.map p) (T.map pU w) := fun w =>
    unramifiedAt_isPullback_iff hcharts w
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS (pullback f.hom g.hom)
      (isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property)
      U' c).mp hcSurj
      (pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      pointsMap B S hS X₁.1 e.hom x' := hz
  let chartF : EtaleChartAtPoint B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ pullback.snd v f.hom
      b := v
      h := p
      a_etale := hAEtale
      b_etale := hvEtale
      comm := hcommF
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U) (a ≫ pullback.snd v f.hom)
            ((FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            pointsMap B S hS (yoneda.obj U') (yoneda.map pU ≫ a ≫ pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        have h₂ : pointsMap B S hS (yoneda.obj U') (c ≫ pullback.fst f.hom g.hom)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₃ : pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ pullback.fst f.hom g.hom) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom (pullback.fst f.hom g.hom)) x').symm
        rw [h₁, ← hcX, h₂, hz', h₃, heFst] }
  let chartF' : EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ pullback.snd v g.hom
      h := pV'
      a_etale := hcXEtale
      b_etale := hBEtale
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U') (c ≫ e.inv)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) e.inv
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₂ : pointsMap B S hS (pullback f.hom g.hom) e.inv
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ e.inv) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom e.inv) x').symm
        rw [h₁, hz', h₂, e.hom_inv_id, pointsMap_id, id_eq] }
  have hsource : chartF.sourcePoint B S hS = T.map pU (chartF'.sourcePoint B S hS) := by
    show (T.map (r.value ≫ pU)) (IsLocalRing.closedPoint r.carrier) =
      T.map pU ((T.map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  constructor
  · intro h
    rw [isUnramifiedAt_iff_unramifiedAt_of_chart B S hS X₀.property Y₀.property chartF, hsource,
      ← hscheme]
    exact (isUnramifiedAt_iff_unramifiedAt_of_chart B S hS X₁.property Y₁.property chartF').mp h
  · intro h
    rw [isUnramifiedAt_iff_unramifiedAt_of_chart B S hS X₁.property Y₁.property chartF',
      hscheme, ← hsource]
    exact (isUnramifiedAt_iff_unramifiedAt_of_chart B S hS X₀.property Y₀.property chartF).mp h

end Space

end AlgebraicGeometry

end
