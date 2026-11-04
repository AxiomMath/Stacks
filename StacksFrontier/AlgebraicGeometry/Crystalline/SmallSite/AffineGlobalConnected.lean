module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalNonempty
public import StacksFrontier.CategoryTheory.Limits.FinalFromRefinement

/-!
# The comma categories of the chaotic subsite of an affine crystalline situation are connected

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] with `X` and `S`
affine, and let `u = wholeToAffineSubsite : 𝒞 ⥤ AffineCris(X/S)` be the inclusion of the chaotic
subsite of thickenings of the whole space into the subsite of affine objects.

`Crystalline.GlobalCrystallineSituation.SmallSite.exists_hom_to_wholeToAffineSubsite` proves that
the comma categories `I^u_{(U,T,δ)}` are nonempty.  This file proves that they are **connected**,
hence that `u` is final in the sense of `CategoryTheory.Functor.Final`.

## Main results

* `Crystalline.GlobalCrystallineSituation.wholeHomToAffine_comp` — the global-sections bridge on
  *morphisms* is contravariantly functorial.
* `Crystalline.GlobalCrystallineSituation.SmallSite.final_wholeToAffineSubsite` — **the inclusion
  `𝒞 ⥤ AffineCris(X/S)` is final**: the comma categories `I^u_{(U,T,δ)}` are nonempty and
  connected.

## What is and is not proved

No tag attribute is placed in this file.  [Stacks, Tag 07JK] is a statement about *cohomology*
and this is one of the inputs of its proof, not the tag.

## References

* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

section Morphisms

variable {B B' : Thickening S} [IsAffine B.thickening.source] [IsAffine B'.thickening.source]

/-- **The global-sections bridge on morphisms is contravariantly functorial.** -/
theorem wholeHomToAffine_comp {B'' : Thickening S} [IsAffine B''.thickening.source]
    (f : B ⟶ B') (g : B' ⟶ B'') :
    wholeHomToAffine hp (f ≫ g) = wholeHomToAffine hp g ≫ wholeHomToAffine hp f :=
  DividedPowerThickening.Hom.ext (globalSectionsDPMorphism_comp f.targetHom g.targetHom).symm

end Morphisms

section RoundTrip

variable [IsAffine S.X] [IsAffine S.S.scheme] (B : Thickening S) [IsAffine B.thickening.source]
  (T : DividedPowerThickening.{u, u, u} (affineSituation S hp))
  (φ : T ⟶ wholeThickeningToAffine hp B) (hT : Function.Bijective T.toQuotient)
  [IsIso (specThickeningOfAffine hp T).toX]

/-- **Taking global sections of `Spec` of a morphism gives the morphism back.**  For a morphism
`φ : (B, J, δ) ⟶ Γ(T, ⊤)` of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` out of an object with bijective structural
map, the morphism `Spec φ` of `CRIS(X/S)` provided by `homOfAffineHom` induces `φ` back on global
sections, up to the comparison isomorphism `wholeThickeningToAffineSpecIso` identifying the global
sections of `Spec (B, J, δ)` with `(B, J, δ)`.

This is the compatibility of the two directions of the affine-to-global dictionary that the
connectedness argument needs: it is what turns a factorisation obtained on the ring side into one
on the geometric side. -/
theorem wholeHomToAffine_homOfAffineHom :
    wholeHomToAffine hp (homOfAffineHom hp B T φ hT) =
      (wholeThickeningToAffineSpecIso hp T).hom ≫ φ := by
  apply DividedPowerThickening.Hom.ext
  apply DividedPowers.DPMorphism.ext
  funext z
  show (specTargetHom hp B T φ).hom.appTop.hom z =
    φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).hom.hom z)
  rw [← (Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).hom_inv_id_apply z, specTargetHom_appTop_apply,
    DividedPowerScheme.ΓSpecIso_hom_inv_apply]

end RoundTrip

section Refinement

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- **A morphism of divided power thickenings between the global sections of two objects of the
chaotic subsite `𝒞` comes from a morphism of `𝒞`.**  This is the fullness of the affine-to-global
bridge `wholeSiteToAffine`, read through `wholeHomToAffine`. -/
theorem exists_hom_of_affineHom (T₃ T' : SmallSite.WholeSpaceThickening S)
    [IsIso ((wholeToBig S).obj T₃).toX] [IsIso ((wholeToBig S).obj T').toX]
    (y : wholeThickeningToAffine hp ((wholeToBig S).obj T') ⟶
      wholeThickeningToAffine hp ((wholeToBig S).obj T₃)) :
    ∃ q : T₃ ⟶ T', wholeHomToAffine hp ((wholeToBig S).map q) = y :=
  ⟨((wholeSiteToAffine hp).preimage (X := op T') (Y := op T₃) y).unop,
    (wholeSiteToAffine hp).map_preimage y⟩

omit [IsAffine S.S.scheme] in
/-- **The factorisation of a morphism of `CRIS(X/S)` through an object of the chaotic subsite,
read off from a factorisation on the ring side.**

Let `B` be an object of `CRIS(X/S)` with affine thickened scheme, let `T₃` and `T'` be objects of
`𝒞`, let `D` be an object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` identified with the global sections of `T₃`
by `eP`, and let `ψ : D ⟶ Γ(B)`.  If `c : B ⟶ T₃` induces `eP.hom ≫ ψ` on global sections, if
`b' : B ⟶ T'` induces `x ≫ ψ` for some `x : Γ(T') ⟶ D`, and if `q : T₃ ⟶ T'` induces
`x ≫ eP.inv`, then `c ≫ q = b'`.

Both sides induce the same morphism on global sections, and a morphism of `CRIS(X/S)` between
objects with affine thickened schemes is determined by the one it induces
(`wholeHomToAffine_injective`). -/
theorem comp_eq_of_wholeHomToAffine (B : Thickening S) [IsAffine B.thickening.source]
    (T₃ T' : SmallSite.WholeSpaceThickening S)
    [IsIso ((wholeToBig S).obj T₃).toX] [IsIso ((wholeToBig S).obj T').toX]
    (D : DividedPowerThickening.{u, u, u} (affineSituation S hp))
    (eP : wholeThickeningToAffine hp ((wholeToBig S).obj T₃) ≅ D)
    (ψ : D ⟶ wholeThickeningToAffine hp B)
    (c : B ⟶ (wholeToBig S).obj T₃) (hc : wholeHomToAffine hp c = eP.hom ≫ ψ)
    (x : wholeThickeningToAffine hp ((wholeToBig S).obj T') ⟶ D)
    (b' : B ⟶ (wholeToBig S).obj T') (hx : x ≫ ψ = wholeHomToAffine hp b')
    (q : T₃ ⟶ T') (hq : wholeHomToAffine hp ((wholeToBig S).map q) = x ≫ eP.inv) :
    c ≫ (wholeToBig S).map q = b' := by
  refine wholeHomToAffine_injective hp ?_
  rw [wholeHomToAffine_comp, hq, hc, Category.assoc, Iso.inv_hom_id_assoc]
  exact hx

include hp in
/-- **Two morphisms from an affine object of `Cris(X/S)` to objects of the chaotic subsite `𝒞` are
dominated by a third.**  Given an object `(U, T, δ)` of `AffineCris(X/S)` and two morphisms
`b₁ : (U, T, δ) ⟶ T₁`, `b₂ : (U, T, δ) ⟶ T₂` into objects of `𝒞`, there is an object `T₃` of `𝒞`
with morphisms `q₁ : T₃ ⟶ T₁`, `q₂ : T₃ ⟶ T₂` and a morphism `c : (U, T, δ) ⟶ T₃` with
`c ≫ q₁ = b₁` and `c ≫ q₂ = b₂`.

This is the *connectedness* half of the step-3 input of [Stacks, Tag 07JK], and it is the source's
argument: on the ring side `𝒞` is the little affine crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`
read backwards, the product of `T₁` and `T₂` in `𝒞` is the coproduct of their rings of global
sections, that coproduct is computed in the *big* category `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` as well — by
[Stacks, Tag 07HN] in the form
`Crystalline.preservesColimitsOfShape_crystallineThickeningInclusion` — and the global sections of
`(U, T, δ)` are an object of that big category.  So the two induced ring morphisms factor through
the coproduct, and `Spec` of the factorisation is the required `c`. -/
theorem SmallSite.exists_refinement_wholeToAffineSubsite
    (A : SmallSite.AffineCrystallineThickening S)
    (T₁ T₂ : SmallSite.WholeSpaceThickening S)
    (b₁ : A.obj.obj ⟶ (wholeToBig S).obj T₁) (b₂ : A.obj.obj ⟶ (wholeToBig S).obj T₂) :
    ∃ (T₃ : SmallSite.WholeSpaceThickening S) (q₁ : T₃ ⟶ T₁) (q₂ : T₃ ⟶ T₂)
      (c : A.obj.obj ⟶ (wholeToBig S).obj T₃),
      c ≫ (wholeToBig S).map q₁ = b₁ ∧ c ≫ (wholeToBig S).map q₂ = b₂ := by
  have := A.property.1
  have _ : IsIso ((wholeToBig S).obj T₁).toX := T₁.property
  have _ : IsIso ((wholeToBig S).obj T₂).toX := T₂.property
  obtain ⟨D, hD, ψ, x₁, x₂, hx₁, hx₂⟩ :
      ∃ (D : DividedPowerThickening.{u, u, u} (affineSituation S hp))
        (_ : Function.Bijective D.toQuotient)
        (ψ : D ⟶ wholeThickeningToAffine hp A.obj.obj)
        (x₁ : wholeThickeningToAffine hp ((wholeToBig S).obj T₁) ⟶ D)
        (x₂ : wholeThickeningToAffine hp ((wholeToBig S).obj T₂) ⟶ D),
        x₁ ≫ ψ = wholeHomToAffine hp b₁ ∧ x₂ ≫ ψ = wholeHomToAffine hp b₂ := by
    have : HasBinaryCoproducts (affineIsCrystalline hp).FullSubcategory :=
      HasNonemptyFiniteColimits.out (Discrete WalkingPair)
    obtain ⟨ψ, hψ₁, hψ₂⟩ := BinaryCofan.IsColimit.desc'
      (isColimitOfHasBinaryCoproductOfPreservesColimit (affineIsCrystalline hp).ι
        ((wholeSiteToLittleAffine hp).obj (op T₁)) ((wholeSiteToLittleAffine hp).obj (op T₂)))
      (wholeHomToAffine hp b₁) (wholeHomToAffine hp b₂)
    exact ⟨_, ((wholeSiteToLittleAffine hp).obj (op T₁) ⨿
      (wholeSiteToLittleAffine hp).obj (op T₂)).property, ψ, _, _, hψ₁, hψ₂⟩
  have hiso : IsIso (specThickeningOfAffine hp D).toX := isIso_specToX hp D hD
  have h3 : IsIso ((wholeToBig S).obj (specWholeSpaceThickening hp D hD)).toX := hiso
  have key : ∀ (T : SmallSite.WholeSpaceThickening S) [IsIso ((wholeToBig S).obj T).toX]
      (x : wholeThickeningToAffine hp ((wholeToBig S).obj T) ⟶ D)
      (b : A.obj.obj ⟶ (wholeToBig S).obj T), x ≫ ψ = wholeHomToAffine hp b →
      ∃ q : specWholeSpaceThickening hp D hD ⟶ T,
        homOfAffineHom hp A.obj.obj D ψ hD ≫ (wholeToBig S).map q = b := by
    intro T _ x b hx
    obtain ⟨q, hq⟩ := exists_hom_of_affineHom hp (specWholeSpaceThickening hp D hD) T
      (x ≫ (wholeThickeningToAffineSpecIso hp D).inv)
    exact ⟨q, comp_eq_of_wholeHomToAffine hp _ _ T D _ ψ _
      (wholeHomToAffine_homOfAffineHom hp _ D ψ hD) x b hx q hq⟩
  obtain ⟨q₁, hq₁⟩ := key T₁ x₁ b₁ hx₁
  obtain ⟨q₂, hq₂⟩ := key T₂ x₂ b₂ hx₂
  exact ⟨specWholeSpaceThickening hp D hD, q₁, q₂, _, hq₁, hq₂⟩

include hp in
/-- **The inclusion `𝒞 ⥤ AffineCris(X/S)` of the chaotic subsite into the affine subsite is
final**: for every object `(U, T, δ)` of `AffineCris(X/S)` the comma category `I^u_{(U,T,δ)}` of
pairs `(T', (U, T, δ) ⟶ T')` with `T'` in `𝒞` is nonempty and connected.

This is the step-3 input of [Stacks, Tag 07JK].  Nonemptiness is
`SmallSite.exists_hom_to_wholeToAffineSubsite`, where the affineness of `X` and `S` and
[Stacks, Tag 07HP] are used; connectedness is
`SmallSite.exists_refinement_wholeToAffineSubsite`, which dominates any two objects of
`I^u_{(U,T,δ)}` by a third and so joins them by a zigzag of length two
(`CategoryTheory.Functor.final_of_exists_hom_of_exists_refinement`).

Finality is exactly the hypothesis of
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal`, so it delivers the comparison of
constant sheaves `g_! ℤ_𝒞 ≅ ℤ_{AffineCris(X/S)}` with no terminal object of either site — and `𝒞`
has none, as `AffineGlobalLimits` records. -/
theorem SmallSite.final_wholeToAffineSubsite :
    (SmallSite.wholeToAffineSubsite (S := S)).Final := by
  refine Functor.final_of_exists_hom_of_exists_refinement _ ?_ ?_
  · intro A
    obtain ⟨C, hC⟩ := SmallSite.exists_hom_to_wholeToAffineSubsite hp A
    exact ⟨C, hC⟩
  · intro A T₁ T₂ a₁ a₂
    obtain ⟨T₃, q₁, q₂, c, h₁, h₂⟩ :=
      SmallSite.exists_refinement_wholeToAffineSubsite hp A T₁ T₂ a₁.hom.hom a₂.hom.hom
    exact ⟨T₃, q₁, q₂, ObjectProperty.homMk (ObjectProperty.homMk c),
      ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₁),
      ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₂)⟩

end Refinement

end Crystalline.GlobalCrystallineSituation

end

end
