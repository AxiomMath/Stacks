module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEssSurj

/-!
# Every affine object of the crystalline site maps to a thickening of the whole space

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] with `X` and `S`
affine.  Inside the small crystalline site `Cris(X/S)` sit the subsite `AffineCris(X/S)` of the
objects `(U, T, δ)` with `U` and `T` affine, and the chaotic subsite `𝒞` of the objects over the
whole of `X`; the inclusion of the latter in the former is
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeToAffineSubsite`.

This file proves that **every object of `AffineCris(X/S)` admits a morphism to an object of
`𝒞`** — the non-emptiness of the comma categories `I^u_{(U,T,δ)}` which is the step of the proof
of [Stacks, Tag 07JK] where the affineness of `X` and of `S` is used, and the only step of that
proof calling on [Stacks, Tag 07HP].

The argument is the one of the source.  Taking global sections of the ambient divided power
scheme turns an object `(U, T, δ)` of `AffineCris(X/S)` into an object of the *big* affine
crystalline category `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM]: the ring is `Γ(T, ⊤)`, the
divided power ideal is `I_T(⊤)`, and the structural map `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` is restriction
`Γ(X, ⊤) → Γ(U, ⊤)` followed by the inverse of the isomorphism
`Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)` of
`Crystalline.SchemeThickening.sectionsQuotientEquiv`.  That structural map is *not* bijective
unless `U` is the whole of `X`, which is exactly why the big category `CRIS` and not the little
one `Cris` is the right home for it.  [Stacks, Tag 07HP] — in the library
`Crystalline.exists_levelEnvelope_hom` — provides, for any object of `CRIS(C/A)`, a morphism to
it from a finite level `D_e` of the divided power envelope of a polynomial presentation of `C`,
and `D_e` *is* an object of the little category `Cris(C/A)`.  Taking `Spec` back, through
`Crystalline.GlobalCrystallineSituation.specWholeSpaceThickening`, turns `D_e` into an object of
`𝒞` and the morphism of rings into the required morphism of `Cris(X/S)`.

## Main results

`freePolynomialPresentation` and `exists_crystalline_hom` live in the namespace `Crystalline`;
everything else in `Crystalline.GlobalCrystallineSituation`.

* `homOfAffineHom` — **the morphism of `CRIS(X/S)` attached to a morphism of
  `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` out of a crystalline object**, the `Spec` of a morphism of divided
  power rings.
* `exists_crystalline_hom` — [Stacks, Tag 07HP] with no presentation chosen, for the free
  polynomial presentation `freePolynomialPresentation`.
* `exists_hom_to_specWholeSpaceThickening` — the two previous items combined with
  `wholeThickeningToAffine`.
* `SmallSite.exists_hom_to_wholeSpaceThickening` and
  `SmallSite.exists_hom_to_wholeToAffineSubsite` — **the non-emptiness of the comma categories
  `I^u_{(U,T,δ)}` of the proof of [Stacks, Tag 07JK]**, stated for the inclusion of `𝒞` in
  `Cris(X/S)` and for its inclusion in `AffineCris(X/S)`.

## What is and is not proved

No tag attribute is placed in this file.  [Stacks, Tag 07JK] is a statement about *cohomology*
and this is one of the inputs of its proof, not the tag; [Stacks, Tag 07HP] is the ring-theoretic
statement already carrying that tag in
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean`, and what is added here is
its translation across the affine-to-global bridge, not a second proof of it.

The connectedness of the comma categories `I^u_{(U,T,δ)}`, the other half of the step-3 input of
[Stacks, Tag 07JK], **is proved**, and not by the route the source takes: it is
`SmallSite.exists_refinement_wholeToAffineSubsite` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalConnected.lean`, which dominates
any two objects of `I^u_{(U,T,δ)}` by a third, so no preservation of the products of `𝒞` by the
inclusion is needed and `hasBinaryProducts_wholeSpaceThickening` is not used for it.  Together
with the non-emptiness below this gives the finality of the inclusion,
`SmallSite.final_wholeToAffineSubsite` of the same file.

The comparison of constant sheaves `g_! ℤ_𝒞 ≅ ℤ_{AffineCris(X/S)}`, the datum of
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`, **is proved**
as well, as `SmallSite.lowerShriekConstantSheafIntegerIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalConstantSheaf.lean`: the
terminal-object-free route
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal` asks exactly for that finality,
so the absence of a terminal object of `𝒞` does not close it.

What does still rest on the chaotic subsite `𝒞` having no terminal object — a terminal object of
`𝒞` being an initial object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, which the finite levels `D_e` of
`exists_crystalline_hom` do not provide (the `p`-adically completed envelope `D` would, and it is
not an object of the uncompleted category) — is the acyclicity of the restriction of an injective
abelian sheaf, [Stacks, Tag 0D6X],
whose main lemma `Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor` again asks
for a terminal object of the source site.  The vanishing of [Stacks, Tag 07JJ] over the objects of
`AffineCris(X/S)` is also still missing, the library having only the Zariski-side fragment
`SmallSite.isZero_cohomology_restriction_of_isAffine`.

The polynomial presentation of `Γ(X, ⊤)` over `Γ(S, ⊤)` used here is the free one, on the
underlying set of `Γ(X, ⊤)`; the source allows any polynomial presentation, and nothing below
depends on the choice.

## References

* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-! ### The fields of the global-sections object of an object with affine thickened scheme -/

section Object

variable (B : Thickening S) [IsAffine B.thickening.source]

/-- The divided power ring of `wholeThickeningToAffine hp B` is the ring of global sections of
the thickening of `B`. -/
@[simp]
theorem wholeThickeningToAffine_ring :
    (wholeThickeningToAffine hp B).ring = B.thickening.sectionsRing := rfl

/-- The structural map of `wholeThickeningToAffine hp B` is `wholeSectionsToQuotient B`. -/
@[simp]
theorem wholeThickeningToAffine_toQuotient :
    (wholeThickeningToAffine hp B).toQuotient = wholeSectionsToQuotient B := rfl

/-- The morphism from the base of `wholeThickeningToAffine hp B` is the morphism of divided
power rings that `B.toBase` induces on global sections. -/
@[simp]
theorem wholeThickeningToAffine_fromBase :
    (wholeThickeningToAffine hp B).fromBase = globalSectionsDPMorphism B.toBase := rfl

end Object

/-! ### `Spec` of a morphism of the affine crystalline category -/

section Morphism

variable (B : Thickening S) [IsAffine B.thickening.source]
  (T : DividedPowerThickening.{u, u, u} (affineSituation S hp))
  (φ : T ⟶ wholeThickeningToAffine hp B)

/-- The morphism of divided power schemes `T ⟶ Spec B` attached to a morphism of
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` out of `(B, J, δ)` into the global sections of an object of `CRIS(X/S)`
with affine thickened scheme.  It is the universal property of `Spec` of a divided power ring,
`Crystalline.DividedPowerScheme.toSpecDividedPowerScheme`. -/
def specTargetHom : B.thickening.target ⟶ DividedPowerScheme.specDividedPowerScheme T.ring :=
  DividedPowerScheme.toSpecDividedPowerScheme B.thickening.target T.ring φ.hom

/-- On global sections, `specTargetHom` is the morphism of divided power rings it was built
from. -/
theorem specTargetHom_appTop_apply (x : T.ring) :
    (specTargetHom hp B T φ).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom x) = φ.hom x :=
  RingHom.congr_fun
    (DividedPowerScheme.toSpecDividedPowerScheme_appTop B.thickening.target T.ring φ.hom) x

/-- **The thickened scheme of `Spec (B, J, δ)` is the whole of `X`**, as an isomorphism rather
than as the instance `isIso_specToX`: for an object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` whose structural
map `Γ(X, ⊤) → B/J` is bijective, `Spec (B/J) ≅ X`. -/
def specToXIso [IsAffine S.X] (hT : Function.Bijective T.toQuotient) :
    Spec (CommRingCat.of (↥T.ring ⧸ T.ring.ideal)) ≅ S.X :=
  haveI : IsIso (specToX hp T) := isIso_specToX hp T hT
  asIso (specToX hp T)

/-- The forward morphism of `specToXIso hp T hT` is `specToX hp T`. -/
@[simp]
theorem specToXIso_hom [IsAffine S.X] (hT : Function.Bijective T.toQuotient) :
    (specToXIso hp T hT).hom = specToX hp T := rfl

/-- **The morphism of `CRIS(X/S)` attached to a morphism of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` out of a
crystalline object.**  Let `(U, T, δ)` be an object of `CRIS(X/S)` with `U` affine, let
`(B, J, δ')` be an object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` whose structural map `Γ(X, ⊤) → B/J` is
bijective, and let `φ : (B, J, δ') → Γ(T, ⊤)` be a morphism of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`.  Then
`Spec φ` is a morphism `(U, T, δ) ⟶ Spec (B, J, δ')` of `CRIS(X/S)`, where the target is the
object of `Crystalline.GlobalCrystallineSituation.specThickeningOfAffine`.

The map on ambient schemes is `Spec φ` by the universal property of `Spec`; the map on thickened
schemes is forced, `U ⟶ X` followed by the inverse of the isomorphism `Spec (B/J) ≅ X` which the
bijectivity of the structural map provides.  The three compatibilities are the two of `φ` plus
that inverse: compatibility with the immersions is `toQuotient_comp` and compatibility over the
base is `fromBase_comp`, both read through `Spec`. -/
def homOfAffineHom [IsAffine S.X] [IsAffine S.S.scheme]
    (hT : Function.Bijective T.toQuotient) :
    B ⟶ specThickeningOfAffine hp T := by
  haveI : IsAffine (specThickeningOfAffine hp T).thickening.target.scheme :=
    (inferInstance : IsAffine (Spec (CommRingCat.of ↥T.ring)))
  refine
  { sourceHom := B.toX ≫ (specToXIso hp T hT).inv
    targetHom := specTargetHom hp B T φ
    immersion_naturality := ?_
    base_naturality := ?_
    toX_naturality := ?_ }
  · refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    obtain ⟨β, rfl⟩ : ∃ β, (Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β = x :=
      ⟨_, ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).hom_inv_id x⟩
    obtain ⟨y, hy⟩ := hT.2 (Ideal.Quotient.mk T.ring.ideal β)
    have hinv : ∀ z : Γ(S.X, ⊤),
        (specToXIso hp T hT).inv.appTop.hom ((specToX hp T).appTop.hom z) = z := by
      intro z
      rw [← specToXIso_hom hp T hT, Stacks.Thickenings.appTop_comp_apply,
        Iso.inv_hom_id]
      simp
    have hq : DividedPowerRing.quotientRingHom (A := T.ring)
        (B := (wholeThickeningToAffine hp B).ring) φ.hom (T.toQuotient y) =
          wholeSectionsToQuotient B y :=
      RingHom.congr_fun φ.toQuotient_comp y
    rw [hy, DividedPowerRing.quotientRingHom_mk] at hq
    have hL : B.thickening.immersion.appTop.hom
        ((specTargetHom hp B T φ).hom.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β)) = B.toX.appTop.hom y := by
      rw [specTargetHom_appTop_apply]
      calc B.thickening.immersion.appTop.hom (φ.hom β)
          = B.thickening.sectionsQuotientEquiv
              (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.thickening) (φ.hom β)) :=
            (SchemeThickening.sectionsQuotientEquiv_mk B.thickening _).symm
        _ = B.thickening.sectionsQuotientEquiv (wholeSectionsToQuotient B y) := congrArg _ hq
        _ = B.toX.appTop.hom y := sectionsQuotientEquiv_wholeSectionsToQuotient B y
    have hR : (specToXIso hp T hT).inv.appTop.hom
        ((DividedPowerScheme.specQuotientImmersion T.ring).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β)) = y := by
      rw [appTop_specQuotientImmersion_eq hp T hy.symm]
      exact hinv y
    exact hL.trans (congrArg B.toX.appTop.hom hR).symm
  · refine DividedPowerScheme.Hom.ext (ext_of_isAffine
      (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)))
    have hbase : (specThickeningToBase hp T).hom.appTop =
        CommRingCat.ofHom (specFromBase hp T).toRingHom :=
      DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _
    have hφ : φ.hom (T.fromBase a) = B.toBase.hom.appTop.hom a :=
      congrFun (congrArg (fun ψ : DividedPowers.DPMorphism (affineSituation S hp).A.dividedPowers
        (wholeThickeningToAffine hp B).ring.dividedPowers ↦
          (ψ : ↥(affineSituation S hp).A → ↥(wholeThickeningToAffine hp B).ring))
        φ.fromBase_comp) a
    change ((specTargetHom hp B T φ).hom ≫ (specThickeningToBase hp T).hom).appTop.hom a = _
    rw [← Stacks.Thickenings.appTop_comp_apply, hbase]
    change (specTargetHom hp B T φ).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom (T.fromBase a)) = _
    rw [specTargetHom_appTop_apply, hφ]
  · change (B.toX ≫ (specToXIso hp T hT).inv) ≫ specToX hp T = B.toX
    rw [← specToXIso_hom hp T hT, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Morphism

end Crystalline.GlobalCrystallineSituation

/-! ### The free polynomial presentation, and [Stacks, Tag 07HP] without a chosen presentation -/

namespace Crystalline

/-- The free polynomial presentation of `C` over `A`: the polynomial algebra on the underlying
set of `C`, evaluated by the identity.  Any polynomial presentation would do for
[Stacks, Tag 07HP]; this one exists for every affine crystalline situation. -/
def freePolynomialPresentation (s : AffineCrystallineSituation.{u, u}) :
    MvPolynomial s.C ↥s.A →ₐ[↥s.A] s.C :=
  MvPolynomial.aeval id

/-- The free polynomial presentation is surjective: the variable indexed by `c` is sent to `c`. -/
theorem surjective_freePolynomialPresentation (s : AffineCrystallineSituation.{u, u}) :
    Function.Surjective (freePolynomialPresentation s) :=
  fun c ↦ ⟨MvPolynomial.X c, by simp [freePolynomialPresentation]⟩

/-- **[Stacks, Tag 07HP], with no presentation chosen: every object of `CRIS(C/A)` receives a
morphism from an object of the little category `Cris(C/A)`.**  This is
`Crystalline.exists_levelEnvelope_hom` applied to the free polynomial presentation of `C` over
`A`, the crystallinity of the finite levels being part (3) of [Stacks, Tag 07KG].

The source object is a *finite level* `D_e` of the divided power envelope, in which `p` is
nilpotent, and not the `p`-adically completed envelope `D` of [Stacks, Tag 07KH]: `D` is an
object of `Cris^∧(C/A)` and not of `Cris(C/A)`.  There is in general no single object of
`Cris(C/A)` that works for every `B`, which is why the statement is an existence statement and
not the weak initiality of one object. -/
theorem exists_crystalline_hom (s : AffineCrystallineSituation.{u, u})
    (B : DividedPowerThickening.{u, u, u} s) :
    ∃ D : DividedPowerThickening.{u, u, u} s,
      DividedPowerThickening.IsCrystalline D ∧ Nonempty (D ⟶ B) := by
  obtain ⟨e, he, ⟨g⟩⟩ := exists_levelEnvelope_hom s (P := MvPolynomial s.C ↥s.A)
    ⟨s.C, ⟨AlgEquiv.refl⟩⟩ (freePolynomialPresentation s)
    (surjective_freePolynomialPresentation s) B
  exact ⟨_, (((levelCrystallineThickening s (freePolynomialPresentation s)
    (surjective_freePolynomialPresentation s)).2 e he).2).1, ⟨g⟩⟩

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **Every object of `CRIS(X/S)` with affine thickened scheme admits a morphism to a divided
power thickening of the whole of `X`**, for `X` and `S` affine.  The object of `CRIS(C/A)` of
global sections is `wholeThickeningToAffine`, the crystalline object mapping to it is
[Stacks, Tag 07HP] in the form `Crystalline.exists_crystalline_hom`, and the morphism is its
`Spec`, `homOfAffineHom`. -/
theorem exists_hom_to_specWholeSpaceThickening (B : Thickening S)
    [IsAffine B.thickening.source] :
    ∃ (T : DividedPowerThickening.{u, u, u} (affineSituation S hp))
      (_ : Function.Bijective T.toQuotient),
        Nonempty (B ⟶ specThickeningOfAffine hp T) := by
  obtain ⟨D, hD, ⟨φ⟩⟩ :=
    exists_crystalline_hom (affineSituation S hp) (wholeThickeningToAffine hp B)
  exact ⟨D, hD, ⟨homOfAffineHom hp B D φ hD⟩⟩

include hp in
/-- **The non-emptiness of the comma category `I^u_{(U,T,δ)}` of the proof of
[Stacks, Tag 07JK]**, for the inclusion `u = wholeι` of the chaotic subsite `𝒞` in the small
crystalline site: for `X` and `S` affine, every object of `Cris(X/S)` lying in
`AffineCris(X/S)` admits a morphism to an object of `𝒞`.

This is the step of the proof of [Stacks, Tag 07JK] where the affineness of `X` and `S` is used.
The *connectedness* of `I^u_{(U,T,δ)}`, the other half of that step, is
`SmallSite.exists_refinement_wholeToAffineSubsite`, and the two together are the finality
`SmallSite.final_wholeToAffineSubsite`. -/
theorem SmallSite.exists_hom_to_wholeSpaceThickening (A : CrystallineThickening S)
    (hA : SmallSite.IsAffineObject S A) :
    ∃ C : SmallSite.WholeSpaceThickening S, Nonempty (A ⟶ (SmallSite.wholeι S).obj C) := by
  have := hA.1
  obtain ⟨D, hD, ⟨f⟩⟩ := exists_hom_to_specWholeSpaceThickening hp A.obj
  exact ⟨specWholeSpaceThickening hp D hD, ⟨ObjectProperty.homMk f⟩⟩

include hp in
/-- **The non-emptiness of the comma category `I^u_{(U,T,δ)}` of the proof of
[Stacks, Tag 07JK]**, for the inclusion `u = wholeToAffineSubsite` of the chaotic subsite `𝒞` in
the affine subsite `AffineCris(X/S)`.  This is the form the proof of [Stacks, Tag 07JK] uses,
the comparison with `Cris(X/S)` having already been made by
`Crystalline.GlobalCrystallineSituation.SmallSite.affineCohomologyIso`. -/
theorem SmallSite.exists_hom_to_wholeToAffineSubsite
    (A : SmallSite.AffineCrystallineThickening S) :
    ∃ C : SmallSite.WholeSpaceThickening S,
      Nonempty (A ⟶ (SmallSite.wholeToAffineSubsite (S := S)).obj C) := by
  obtain ⟨C, ⟨f⟩⟩ := SmallSite.exists_hom_to_wholeSpaceThickening hp A.obj A.property
  exact ⟨C, ⟨ObjectProperty.homMk f⟩⟩

end GlobalCrystallineSituation

end Crystalline

end

end
