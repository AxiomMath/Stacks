module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.AlgebraicGeometry.FormalScheme.McQuillanFormalScheme
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakAffineFormalOpen
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernel
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# A weak ideal of definition which is not cut out by its sections

**Stacks 0AIV** asserts, for a formal scheme `𝔛` in the sense of McQuillan, a one-to-one
correspondence between the weak ideals of definition `ℐ ⊆ 𝒪_𝔛` and the thickenings `Z → h_𝔛`.
A weak ideal of definition that comes from a thickening is cut out by its sections over the affine
formal opens: over `𝔘 ≅ Spfw A` it is the kernel ideal sheaf of the quotient point
`Spec (A/ℐ(𝔘)) → 𝔘`; and when `𝔛` is a scheme `X`, a thickening `Z → X` is a closed immersion of
schemes, whose kernel ideal sheaf is quasi-coherent. As printed, with `ℐ` an arbitrary ideal sheaf,
the correspondence is false: a weak ideal of definition need be neither cut out in this way nor
quasi-coherent. This file gives a witness.

It lives on the pseudo-discretised spectrum `X = Spec R` of a local ring `R` with a nilpotent `ε`
and an element `t` of the maximal ideal such that no power of `t` kills `ε`; for instance
`R = ℤ₂[ε]`, the dual numbers over the `2`-adic integers, with `t = 2`. The ideal sheaf `ℐ`
consists of the sections whose germs are all nilpotent and whose germ at the closed point
vanishes. Over a quasi-compact open the sections of the pseudo-discretised structure sheaf are
discrete and the sections of `ℐ` are nilpotent, so `ℐ` is a weak ideal of definition. Its global
sections vanish, because every open neighbourhood of the closed point of a local spectrum is
everything, so the identity of `X` kills `ℐ(X)`; but over the basic open `D(t)`, which misses the
closed point, `ℐ` contains the image of `ε` in `R_t`, which is non-zero and not killed by the
identity. For the same reason `ℐ` is not quasi-coherent: the kernel ideal sheaf of a quasi-compact
morphism `Z → X` is generated over `D(t)` by its global sections, so with zero global sections it
vanishes over `D(t)`.

## Main definitions

* `AlgebraicGeometry.Scheme.nilpotentGermsVanishingAtIdeal`: the ideal of sections of `𝒪_X` over
  an open with nilpotent germs and vanishing germ at a point.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.nilpotentGermsVanishingAt`: these
  ideals, as an ideal sheaf on the pseudo-discretisation of `X`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isWeakAffineFormalOpen`: an affine open of a scheme is a weak
  affine formal open of its pseudo-discretisation.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isWeakIdealOfDefinitionOn_nilpotentGermsVanishingAt`: the ideal sheaf is a weak ideal of
  definition over the quasi-compact opens, hence over the weak affine formal opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.not_isCutOutOn_nilpotentGermsVanishingAt_closedPoint`: on the spectrum of a local ring as
  above it is not cut out by its sections over the weak affine formal opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.nilpotentGermsVanishingAt_closedPoint_ne_ker`: nor is it the kernel ideal sheaf of any
  quasi-compact morphism of schemes.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.exists_isWeakIdealOfDefinitionOn_forall_isThickening_ne_ker`: a scheme whose
  pseudo-discretisation, a McQuillan formal scheme, carries a weak ideal of definition which is
  not cut out by its sections over the weak affine formal opens and is the kernel of no
  thickening, so that the correspondence of Stacks 0AIV fails as printed.

## Implementation notes

The ideals are defined at the level of the scheme, as ideals of `Γ(X, U)` for `U : X.Opens`, and
their restriction and locality properties are proved there; the ideal sheaf on the
pseudo-discretisation reuses them, its rings of sections and restriction maps being those of `X`.

The source's thickenings `i : Z → h_𝔛` are morphisms from an algebraic space which are
representable, surjective closed immersions. When `𝔛` is a scheme `X`, `h_X` is representable,
so `Z` is a scheme and `i` a thickening of schemes; the statement quantifies over those, and the
kernel ideal sheaf is that of the induced morphism of locally topologically ringed spaces
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ker`).

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The ideal of sections at the level of the scheme -/

namespace Scheme

variable (X : Scheme.{u}) (x : X)

/-- The ideal of the sections of `𝒪_X` over `U` all of whose germs are nilpotent and whose germ
at the point `x` vanishes. -/
noncomputable def nilpotentGermsVanishingAtIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  (⨅ y : U,
      Ideal.comap (X.presheaf.germ U y.1 y.2).hom (_root_.nilradical (X.presheaf.stalk y.1))) ⊓
    ⨅ hx : x ∈ U, RingHom.ker (X.presheaf.germ U x hx).hom

variable {X x}

/-- A section lies in `X.nilpotentGermsVanishingAtIdeal x U` exactly when all its germs are
nilpotent and its germ at `x` vanishes. -/
theorem mem_nilpotentGermsVanishingAtIdeal {U : X.Opens} {s : Γ(X, U)} :
    s ∈ X.nilpotentGermsVanishingAtIdeal x U ↔
      (∀ y (hy : y ∈ U), IsNilpotent (X.presheaf.germ U y hy s)) ∧
        ∀ hx : x ∈ U, X.presheaf.germ U x hx s = 0 := by
  simp only [nilpotentGermsVanishingAtIdeal, Ideal.mem_inf, Ideal.mem_iInf, Ideal.mem_comap,
    RingHom.mem_ker, mem_nilradical, Subtype.forall]

/-- Restriction carries `X.nilpotentGermsVanishingAtIdeal x U` into the ideal over a smaller
open, the germs of a restriction being germs of the section. -/
theorem map_mem_nilpotentGermsVanishingAtIdeal {U V : X.Opens} (h : V ≤ U) {s : Γ(X, U)}
    (hs : s ∈ X.nilpotentGermsVanishingAtIdeal x U) :
    X.presheaf.map (homOfLE h).op s ∈ X.nilpotentGermsVanishingAtIdeal x V := by
  rw [mem_nilpotentGermsVanishingAtIdeal] at hs ⊢
  refine ⟨fun y hy => ?_, fun hx => ?_⟩ <;> rw [TopCat.Presheaf.germ_res_apply]
  exacts [hs.1 y (h hy), hs.2 (h hx)]

/-- Membership in `X.nilpotentGermsVanishingAtIdeal x U` is local: a section belonging to the
ideal near every point of its domain belongs to it, both conditions being on germs. -/
theorem mem_nilpotentGermsVanishingAtIdeal_of_locally {U : X.Opens} {s : Γ(X, U)}
    (hlocal : ∀ y ∈ U, ∃ (V : X.Opens) (h : V ≤ U),
      y ∈ V ∧ X.presheaf.map (homOfLE h).op s ∈ X.nilpotentGermsVanishingAtIdeal x V) :
    s ∈ X.nilpotentGermsVanishingAtIdeal x U := by
  rw [mem_nilpotentGermsVanishingAtIdeal]
  refine ⟨fun y hy => ?_, fun hx => ?_⟩
  · obtain ⟨V, hVU, hyV, hV⟩ := hlocal y hy
    simpa only [TopCat.Presheaf.germ_res_apply] using
      (mem_nilpotentGermsVanishingAtIdeal.mp hV).1 y hyV
  · obtain ⟨V, hVU, hxV, hV⟩ := hlocal x hx
    simpa only [TopCat.Presheaf.germ_res_apply] using
      (mem_nilpotentGermsVanishingAtIdeal.mp hV).2 hxV

/-- A section over a quasi-compact open in `X.nilpotentGermsVanishingAtIdeal x U` is nilpotent:
its germs are nilpotent, hence never units, so its basic open is empty. -/
theorem isNilpotent_of_mem_nilpotentGermsVanishingAtIdeal {U : X.Opens}
    (hU : IsCompact (U : Set X)) {s : Γ(X, U)} (hs : s ∈ X.nilpotentGermsVanishingAtIdeal x U) :
    IsNilpotent s := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU]
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyU : y ∈ U := X.basicOpen_le s hy
  exact ((mem_nilpotentGermsVanishingAtIdeal.mp hs).1 y hyU).not_isUnit
    ((X.mem_basicOpen s y hyU).mp hy)

end Scheme

/-! ### Affine opens are weak affine formal opens -/

/-- An affine open `U` of a scheme `X` is a weak affine formal open of its pseudo-discretisation:
the ring `Γ(X, U)` with the discrete topology is weakly admissible, and the open subspace `U`,
pseudo-discretised, is `Spec Γ(X, U)` pseudo-discretised, which is `Spfw Γ(X, U)`. -/
theorem IsAffineOpen.isWeakAffineFormalOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) : IsWeakAffineFormalOpen (schemeToLTRSObj X) U := by
  let _ : TopologicalSpace Γ(X, U) := ⊥
  have : DiscreteTopology Γ(X, U) := discreteTopology_bot _
  refine ⟨TopCommRingCat.of Γ(X, U), inferInstance, isWeaklyAdmissible_discrete _, ?_⟩
  refine ⟨?_ ≪≫ pseudoDiscreteSpaceIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso
      (Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec))
    ≪≫ discreteSpecSpfIsoOn Γ(X, U) (isWeakIdealOfDefinition_bot_discrete _)⟩
  exact PresheafedSpace.isoOfComponents (Iso.refl _)
    (pseudoDiscreteWhiskerIso U.inclusion' U.isOpenEmbedding' X.presheaf).symm

/-- The whole spectrum of a ring is a weak affine formal open of its pseudo-discretisation. -/
theorem isWeakAffineFormalOpen_top_Spec (R : CommRingCat.{u}) :
    IsWeakAffineFormalOpen (schemeToLTRSObj (Spec R)) ⊤ :=
  (isAffineOpen_top (Spec R)).isWeakAffineFormalOpen

namespace LocallyTopologicallyRingedSpace.IdealSheaf

/-! ### The ideal sheaf -/

variable (X : Scheme.{u}) (x : X)

/-- The ideal sheaf on the pseudo-discretisation of a scheme `X` of the sections all of whose
germs are nilpotent and whose germ at a given point `x` vanishes. -/
noncomputable def nilpotentGermsVanishingAt : IdealSheaf (schemeToLTRSObj X) where
  ideal U := X.nilpotentGermsVanishingAtIdeal x U
  map_mem h _ hs := Scheme.map_mem_nilpotentGermsVanishingAtIdeal h hs
  mem_of_locally_mem hlocal := Scheme.mem_nilpotentGermsVanishingAtIdeal_of_locally hlocal

variable {X x} in
/-- A section lies in `nilpotentGermsVanishingAt X x` exactly when all its germs are nilpotent
and its germ at `x` vanishes. -/
theorem mem_nilpotentGermsVanishingAt {U : X.Opens} {s : Γ(X, U)} :
    s ∈ (nilpotentGermsVanishingAt X x).ideal U ↔
      (∀ y (hy : y ∈ U), IsNilpotent (X.presheaf.germ U y hy s)) ∧
        ∀ hx : x ∈ U, X.presheaf.germ U x hx s = 0 :=
  Scheme.mem_nilpotentGermsVanishingAtIdeal

/-- The ideal sheaf of sections with nilpotent germs vanishing at a point is a weak ideal of
definition over the quasi-compact opens: the sections of the pseudo-discretised structure sheaf
over a quasi-compact open are discrete, and a section over a quasi-compact open all of whose germs
are nilpotent is nilpotent, its basic open being empty. -/
theorem isWeakIdealOfDefinitionOn_nilpotentGermsVanishingAt :
    (nilpotentGermsVanishingAt X x).IsWeakIdealOfDefinitionOn
      fun U => IsCompact (U : Set (schemeToLTRSObj X)) := by
  intro U hU
  have : DiscreteTopology ((schemeToLTRSObj X).presheaf.obj (op U)).α :=
    isPseudoDiscrete_pseudoDiscrete X.presheaf U hU
  refine ⟨isOpen_discrete _, fun s hs => ?_⟩
  have hnil : IsNilpotent s :=
    Scheme.isNilpotent_of_mem_nilpotentGermsVanishingAtIdeal (U := U) hU hs
  exact hnil.isTopologicallyNilpotent

/-- The ideal sheaf of sections with nilpotent germs vanishing at a point is a weak ideal of
definition over the weak affine formal opens of the pseudo-discretisation of `X`, these being
quasi-compact. -/
theorem isWeakIdealOfDefinitionOn_isWeakAffineFormalOpen_nilpotentGermsVanishingAt :
    (nilpotentGermsVanishingAt X x).IsWeakIdealOfDefinitionOn
      (IsWeakAffineFormalOpen (schemeToLTRSObj X)) :=
  fun U hU => isWeakIdealOfDefinitionOn_nilpotentGermsVanishingAt X x U hU.isCompact

/-! ### The spectrum of a local ring -/

variable (R : CommRingCat.{u}) [IsLocalRing R]

/-- On the spectrum of a local ring the ideal sheaf of sections with nilpotent germs vanishing at
the closed point has no non-zero global section: a global section with vanishing germ at the
closed point vanishes on an open neighbourhood of it, and every open neighbourhood of the closed
point of a local spectrum is everything. -/
theorem eq_zero_of_mem_nilpotentGermsVanishingAt_closedPoint {s : Γ(Spec R, ⊤)}
    (hs : s ∈ (nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R)).ideal ⊤) :
    s = 0 := by
  have h0 := (mem_nilpotentGermsVanishingAt (U := ⊤)).mp hs |>.2 trivial
  obtain ⟨W, hxW, iU, iV, h⟩ := (Spec R).presheaf.germ_eq (U := ⊤) (V := ⊤)
    (IsLocalRing.closedPoint R) trivial trivial s 0 (h0.trans (map_zero _).symm)
  obtain rfl : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hxW
  rwa [show iU = 𝟙 _ from Subsingleton.elim _ _, op_id, (Spec R).presheaf.map_id, map_zero] at h

/-- On the spectrum of a local ring the ideal sheaf of sections with nilpotent germs vanishing at
the closed point has zero ideal of global sections. -/
theorem nilpotentGermsVanishingAt_closedPoint_ideal_top :
    (nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R)).ideal ⊤ = ⊥ :=
  eq_bot_iff.mpr fun _ hs => eq_zero_of_mem_nilpotentGermsVanishingAt_closedPoint R hs

variable {R}

/-- On the spectrum of a local ring, the restriction of a nilpotent global section `ε` to the
basic open `D(t)` of an element `t` of the maximal ideal lies in the ideal sheaf of sections with
nilpotent germs vanishing at the closed point: its germs are nilpotent, and `D(t)` misses the
closed point. -/
theorem map_mem_nilpotentGermsVanishingAt_closedPoint_basicOpen {t ε : R}
    (ht : t ∈ IsLocalRing.maximalIdeal R) (hε : IsNilpotent ε) :
    (Spec R).presheaf.map (homOfLE ((Spec R).basicOpen_le ((Scheme.ΓSpecIso R).inv t))).op
        ((Scheme.ΓSpecIso R).inv ε) ∈
      (nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R)).ideal
        ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv t)) := by
  refine mem_nilpotentGermsVanishingAt.mpr ⟨fun y hy => ?_, fun hx => ?_⟩
  · exact ((hε.map (Scheme.ΓSpecIso R).inv.hom).map
      ((Spec R).presheaf.map (homOfLE ((Spec R).basicOpen_le _)).op).hom).map
        ((Spec R).presheaf.germ _ y hy).hom
  · rw [basicOpen_eq_of_affine] at hx
    exact absurd ht ((PrimeSpectrum.mem_basicOpen _ _).mp hx)

omit [IsLocalRing R] in
/-- If no power of `t` kills `ε`, the restriction of `ε` to the basic open `D(t)` of `Spec R` is
non-zero, the sections over `D(t)` being the localization `R_t`. -/
theorem map_basicOpen_ne_zero {t ε : R} (htε : ∀ n : ℕ, t ^ n * ε ≠ 0) :
    (Spec R).presheaf.map (homOfLE ((Spec R).basicOpen_le ((Scheme.ΓSpecIso R).inv t))).op
        ((Scheme.ΓSpecIso R).inv ε) ≠ 0 := fun hzero => by
  let := ((Spec R).presheaf.map
    (homOfLE ((Spec R).basicOpen_le ((Scheme.ΓSpecIso R).inv t))).op).hom.toAlgebra
  have := (isAffineOpen_top (Spec R)).isLocalization_basicOpen ((Scheme.ΓSpecIso R).inv t)
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers ((Scheme.ΓSpecIso R).inv t)) _ ((Scheme.ΓSpecIso R).inv ε)).mp hzero
  refine htε n ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1 ?_)
  simpa only [map_mul, map_pow, map_zero] using hn

/-- **The ideal sheaf of sections with nilpotent germs vanishing at the closed point of a local
spectrum is not cut out by its sections over the weak affine formal opens**, as soon as the
maximal ideal contains an element `t` no power of which kills some nilpotent `ε`.

Take `U` the whole spectrum, a weak affine formal open, and `V` the basic open `D(t)`, which misses
the closed point. The image of `ε` in `Γ(D(t), 𝒪) = R_t` lies in the ideal over `V`, its germs
being nilpotent, and is non-zero. The identity of the pseudo-discretised spectrum kills the ideal
over `U`, which is zero, but does not kill that section. -/
theorem not_isCutOutOn_nilpotentGermsVanishingAt_closedPoint {t ε : R}
    (ht : t ∈ IsLocalRing.maximalIdeal R) (hε : IsNilpotent ε) (htε : ∀ n : ℕ, t ^ n * ε ≠ 0) :
    ¬ (nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R)).IsCutOutOn
      (IsWeakAffineFormalOpen (schemeToLTRSObj (Spec R))) := fun hcut =>
  map_basicOpen_ne_zero htε <| (hcut ⊤ (isWeakAffineFormalOpen_top_Spec R) _ le_top _).mp
    (map_mem_nilpotentGermsVanishingAt_closedPoint_basicOpen ht hε) (Spec R) (𝟙 _)
    (fun _ _ => trivial) fun a ha => by
      rw [nilpotentGermsVanishingAt_closedPoint_ideal_top R, Ideal.mem_bot] at ha
      rw [ha, map_zero]

/-- **The ideal sheaf of sections with nilpotent germs vanishing at the closed point of a local
spectrum is not the kernel ideal sheaf of any quasi-compact morphism of schemes**, as soon as the
maximal ideal contains an element `t` no power of which kills some nilpotent `ε`.

The kernel of a quasi-compact morphism is quasi-coherent (`AlgebraicGeometry.Scheme.Hom.ker`), so
its ideal over the basic open `D(t)` is generated by its ideal of global sections, which here is
zero; but the image of `ε` in `Γ(D(t), 𝒪) = R_t` lies in the ideal sheaf and is non-zero. -/
theorem nilpotentGermsVanishingAt_closedPoint_ne_ker {t ε : R}
    (ht : t ∈ IsLocalRing.maximalIdeal R) (hε : IsNilpotent ε) (htε : ∀ n : ℕ, t ^ n * ε ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ Spec R) [QuasiCompact i] :
    nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R) ≠
      ker (schemeToLTRS.map i) := by
  intro hI
  set I := nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R)
  have hqc (U : (Spec R).affineOpens) : I.ideal U.1 = i.ker.ideal U := by
    rw [hI, Scheme.Hom.ker_apply]
    rfl
  let T : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hmap := i.ker.map_ideal_basicOpen T ((Scheme.ΓSpecIso R).inv t)
  rw [show i.ker.ideal T = ⊥ from (hqc T).symm.trans
    (nilpotentGermsVanishingAt_closedPoint_ideal_top R), Ideal.map_bot] at hmap
  exact map_basicOpen_ne_zero htε (Ideal.mem_bot.mp
    (((hqc _).trans hmap.symm).le (map_mem_nilpotentGermsVanishingAt_closedPoint_basicOpen ht hε)))

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

/-! ### The dual numbers over a local ring -/

/-- The dual numbers over a local commutative ring form a local ring: a dual number is a unit
exactly when its scalar part is. -/
theorem DualNumber.isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

/-- **Stacks 0AIV is false as printed for arbitrary ideal sheaves**: there is a scheme whose
pseudo-discretisation, a McQuillan formal scheme, carries a weak ideal of definition which is not
cut out by its sections over the weak affine formal opens and is the kernel ideal sheaf of no
thickening. The witness is the spectrum of the dual numbers `ℤ₂[ε]` over the `2`-adic integers,
with the ideal sheaf of sections with nilpotent germs vanishing at the closed point; here `t = 2`
lies in the maximal ideal and `2ⁿ ε ≠ 0` for every `n`. A thickening is a closed immersion, hence
quasi-compact. -/
theorem exists_isWeakIdealOfDefinitionOn_forall_isThickening_ne_ker :
    ∃ (X : Scheme.{0}) (I : IdealSheaf (schemeToLTRSObj X)),
      IsMcQuillanFormalScheme (schemeToLTRSObj X) ∧
        I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen (schemeToLTRSObj X)) ∧
        ¬ I.IsCutOutOn (IsWeakAffineFormalOpen (schemeToLTRSObj X)) ∧
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X), Stacks.Thickenings.IsThickening i →
          I ≠ ker (schemeToLTRS.map i) := by
  let R : CommRingCat.{0} := CommRingCat.of (DualNumber ℤ_[2])
  have : IsLocalRing R := DualNumber.isLocalRing ℤ_[2]
  let t : R := TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2])
  let ε : R := DualNumber.eps
  have ht : t ∈ IsLocalRing.maximalIdeal R := fun hu =>
    PadicInt.p_nonunit (p := 2) (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hu)
  have hε : IsNilpotent ε := ⟨2, (pow_two ε).trans DualNumber.eps_mul_eps⟩
  have htε (n : ℕ) : t ^ n * ε ≠ 0 := by
    intro h
    have h' := congrArg TrivSqZeroExt.snd h
    change ((TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2]) : DualNumber ℤ_[2]) ^ n *
      DualNumber.eps).snd = (0 : DualNumber ℤ_[2]).snd at h'
    rw [TrivSqZeroExt.inl_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, DualNumber.snd_eps,
      DualNumber.fst_eps, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, mul_one,
      TrivSqZeroExt.snd_zero] at h'
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr two_ne_zero) h'
  exact ⟨Spec R, nilpotentGermsVanishingAt (Spec R) (IsLocalRing.closedPoint R),
    isMcQuillanFormalScheme_schemeToLTRSObj _,
    isWeakIdealOfDefinitionOn_isWeakAffineFormalOpen_nilpotentGermsVanishingAt _ _,
    not_isCutOutOn_nilpotentGermsVanishingAt_closedPoint ht hε htε,
    fun _ i hi => have := hi.1; nilpotentGermsVanishingAt_closedPoint_ne_ker ht hε htε i⟩

/-- A McQuillan formal scheme with a weak ideal of definition which is not cut out by its
sections over the weak affine formal opens. -/
theorem exists_isWeakIdealOfDefinitionOn_not_isCutOutOn :
    ∃ (X : LTRS.{0}) (_ : IsMcQuillanFormalScheme X) (I : IdealSheaf X),
      I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X) ∧
        ¬ I.IsCutOutOn (IsWeakAffineFormalOpen X) :=
  let ⟨X, I, hX, hI, hcut, _⟩ := exists_isWeakIdealOfDefinitionOn_forall_isThickening_ne_ker
  ⟨schemeToLTRSObj X, hX, I, hI, hcut⟩

end AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

end
