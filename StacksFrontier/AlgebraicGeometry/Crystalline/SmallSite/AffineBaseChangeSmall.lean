module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeAbstract
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus

/-!
# The affine base change of sections of a crystal on `Cris(X/S)` along an arbitrary morphism

`StacksFrontier/AlgebraicGeometry/Crystalline/AffineBaseChangeAbstract.lean` computes the base
change of ambient sections along an arbitrary morphism of `CRIS(X/S)` from three inputs: two modules
over the restrictions of `𝒪_{X/S}` to the two ambient schemes, an `f`-map between them, and the
invertibility of the comparison map of [Stacks, Tag 07IQ] that the `f`-map transposes to.  The
**small** crystalline site supplies all three, at the very same sheaf of rings:
`...SmallSite.CohomologyRestriction.moduleRestrictionSheaf`,
`...SmallSite.CohomologyRestriction.moduleFMapSheaf`, and the crystal condition
`...SmallSite.IsSheafCrystal`.

This module reads the computation there, and carries it from the ambient sections over the whole
of `T` to the sections of the coefficient sheaf over the object itself.  The outcome is the
kernel clause of [Stacks, Proposition 60.21.3, Tag 07LG] **for a crystal on `Cris(X/S)`**:

`ℱ(U, T, δ) ⟶ ℱ(U', T', δ')` kills `x` exactly when `x = p^N y` for some `y`,

whenever the restriction map `Γ(T, 𝒪_T) ⟶ Γ(T', 𝒪_{T'})` is surjective with kernel `(p^N)`.

## Why no semilinearity is needed

The passage from the ambient sections `Γ(T, ℱ_T)` to the sections `ℱ(U, T, δ)` is the restriction
along the structure morphism of the restriction of the object to the whole of its ambient scheme,
which is an isomorphism of `Cris(X/S)` by
`...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`; so it is an additive bijection.
It is *not* linear for a fixed ring, and the big-site development
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` therefore carries a
semilinearity lemma for it.  Here none is needed: the conclusion of the kernel clause is about
the **`ℕ`-action** `x = p^N • y`, and every additive map commutes with that.  The ring element
`p^N` of the ambient sections is the image of the natural number `p^N`, and
`Nat.cast_smul_eq_nsmul` turns its action into the `ℕ`-action before the transport.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isIso_comparisonAbstract_of_isSheafCrystal` — the crystal condition is the hypothesis the
  abstract chain asks for.
* `crysSectionTop` and `bijective_crysSectionTop` — the sections over an object and over the
  whole of its ambient scheme agree.
* `fmapTopSection_crysSectionTop` — the `f`-map on ambient sections is the restriction map of the
  site, read on both sides.
* `crysRestrict_eq_zero_iff_exists_nsmul` — **the kernel clause for a crystal on `Cris(X/S)` at
  an arbitrary morphism of the site.**

## What is and is not proved

**No `@[stacks]` attribute is placed and no tag is proved here.**  The kernel clause is one
hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG]; the surjectivity and principal-kernel
hypotheses on the restriction map of `𝒪_{X/S}` are properties of the morphism, discharged at the
level drops of the cosimplicial system of [Stacks, Proposition 60.20.1, Tag 07JN] in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceLevelDropRing.lean`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### Restriction of sections along a morphism of `Cris(X/S)` -/

/-- **The restriction map of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` along a morphism of the
site**, on sections over the objects: the map `ℱ(B) → ℱ(A)` of a morphism `A ⟶ B`, semilinear
over the map of the structure sheaf.  The small-site twin of
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict`. -/
abbrev crysRestrict {A B : CrystallineThickening S} (k : A ⟶ B) :=
  F.val.restrictₛₗ k.op

/-- Restricting along a composite of morphisms of the site is restricting along the two
factors. -/
theorem crysRestrict_comp {A B C : CrystallineThickening S} (j : A ⟶ B) (i : B ⟶ C)
    (x : F.val.obj (op C)) :
    crysRestrict F j (crysRestrict F i x) = crysRestrict F (j ≫ i) x := by
  have hx := F.val.map_comp_apply i.op j.op x
  rw [← op_comp] at hx
  exact hx.symm

/-- Restricting along an identity of the site does nothing. -/
theorem crysRestrict_id (B : CrystallineThickening S) (x : F.val.obj (op B)) :
    crysRestrict F (𝟙 B) x = x := by
  change F.val.map (𝟙 (op B)) x = x
  rw [← PresheafOfModules.presheaf_map_apply_coe, F.val.presheaf.map_id]
  rfl

/-- **Restriction along the structure morphism of the restriction of an object to the whole of
its ambient scheme is a bijection on sections.**  That morphism is an isomorphism of `Cris(X/S)`
by `...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`, so restriction along it is a
bijection with inverse the restriction along its inverse. -/
theorem bijective_crysRestrict_restrictOpenHom_top (B : CrystallineThickening S) :
    Function.Bijective
      (crysRestrict F (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens))) := by
  have := CrystallineThickening.isIso_restrictOpenHom_top B
  refine Function.bijective_iff_has_inverse.mpr
    ⟨crysRestrict F (inv (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens))),
      fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [crysRestrict_comp, IsIso.inv_hom_id, crysRestrict_id]
  · rw [crysRestrict_comp, IsIso.hom_inv_id, crysRestrict_id]

/-- **The restriction of a morphism of `Cris(X/S)` over the whole of the ambient schemes is the
morphism itself**, read on sections.  The small-site twin of
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_restrictOpenMap_top`. -/
theorem crysRestrict_restrictOpenMap_top {A B : CrystallineThickening S} (k : A ⟶ B)
    (x : F.val.obj (op B)) :
    crysRestrict F (CrystallineThickening.restrictOpenMap k
          (⊤ : B.obj.thickening.target.scheme.Opens))
        (crysRestrict F (B.restrictOpenHom ⊤) x) =
      crysRestrict F (A.restrictOpenHom (k.hom.targetHom.hom ⁻¹ᵁ ⊤)) (crysRestrict F k x) := by
  rw [crysRestrict_comp, crysRestrict_comp,
    CrystallineThickening.restrictOpenMap_restrictOpenHom]

/-! ### The three inputs of the abstract chain, on the small site -/

variable {A A' : CrystallineThickening S} (k : A' ⟶ A)

/-- **The comparison map the abstract chain is built from, at the restrictions of a sheaf of
modules on `Cris(X/S)`, is the small-site comparison map of [Stacks, Tag 07IQ].**  True by
definition: both are the adjoint transpose of the same `f`-map through the same adjunction. -/
theorem comparisonAbstract_moduleFMapSheaf :
    comparisonAbstract k.hom (moduleRestrictionSheaf F A) (moduleRestrictionSheaf F A')
        (moduleFMapSheaf F k) =
      moduleComparisonSheaf F k := rfl

/-- **The crystal condition on `Cris(X/S)` is the hypothesis the abstract chain asks for.** -/
theorem isIso_comparisonAbstract_of_isSheafCrystal (hF : IsSheafCrystal F) :
    IsIso (comparisonAbstract k.hom (moduleRestrictionSheaf F A) (moduleRestrictionSheaf F A')
      (moduleFMapSheaf F k)) := by
  rw [comparisonAbstract_moduleFMapSheaf]
  exact hF A' A k

/-- **The restriction `ℱ_T` of a locally quasi-coherent sheaf of modules on `Cris(X/S)`, read
over the structure sheaf of the ambient scheme, is quasi-coherent in the sense of Mathlib.**  This
is `...SmallSite.isQuasicoherent_ambientModuleRestriction` at the spelling the abstract chain is
stated with. -/
theorem isQuasicoherent_ambientSchemeOf (hF : IsLocallyQuasiCoherent F)
    (B : CrystallineThickening S) :
    (ambientSchemeOf B.obj (moduleRestrictionSheaf F B)).IsQuasicoherent :=
  isQuasicoherent_ambientModuleRestriction hF B

/-! ### The sections over an object and over the whole of its ambient scheme -/

/-- **The restriction of a section of `ℱ` over an object of `Cris(X/S)` to the whole of its
ambient scheme**, with its target named at the sections of `ℱ_T` over the whole of `T`, which is
the spelling the abstract chain is written in. -/
def crysSectionTop (B : CrystallineThickening S) (x : F.val.obj (op B)) :
    Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤) :=
  crysRestrict F (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)) x

/-- **The sections over an object and over the whole of its ambient scheme agree.** -/
theorem bijective_crysSectionTop (B : CrystallineThickening S) :
    Function.Bijective (crysSectionTop F B) :=
  bijective_crysRestrict_restrictOpenHom_top F B

/-- `Crystalline.GlobalCrystallineSituation.SmallSite.crysSectionTop`, as an additive map. -/
def crysSectionTopHom (B : CrystallineThickening S) :
    F.val.obj (op B) →+ Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤) :=
  AddMonoidHom.mk' (crysSectionTop F B) (fun x y ↦ map_add _ x y)

/-- The additive map `crysSectionTopHom F B` sends a section `x` to `crysSectionTop F B x`. -/
@[simp]
theorem crysSectionTopHom_apply (B : CrystallineThickening S) (x : F.val.obj (op B)) :
    crysSectionTopHom F B x = crysSectionTop F B x := rfl

/-- The restriction of sections to the whole of the ambient scheme, as an additive
equivalence. -/
def crysSectionTopEquiv (B : CrystallineThickening S) :
    F.val.obj (op B) ≃+ Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤) :=
  AddEquiv.ofBijective (crysSectionTopHom F B) (bijective_crysSectionTop F B)

/-- The additive equivalence `crysSectionTopEquiv F B` sends a section `x` to
`crysSectionTop F B x`. -/
@[simp]
theorem crysSectionTopEquiv_apply (B : CrystallineThickening S) (x : F.val.obj (op B)) :
    crysSectionTopEquiv F B x = crysSectionTop F B x := rfl

/-- **The `f`-map of [Stacks, Tag 07IQ] on global sections is the restriction map of the site**,
read on both sides through
`Crystalline.GlobalCrystallineSituation.SmallSite.crysSectionTop`. -/
theorem fmapTopSection_crysSectionTop (x : F.val.obj (op A)) :
    fmapTopSection k.hom (moduleRestrictionSheaf F A) (moduleRestrictionSheaf F A')
        (moduleFMapSheaf F k) (crysSectionTop F A x) =
      crysSectionTop F A' (crysRestrict F k x) :=
  crysRestrict_restrictOpenMap_top F k x

/-- **A section over an object vanishes exactly when its restriction to the whole of the ambient
scheme does.** -/
theorem crysSectionTop_eq_zero_iff (B : CrystallineThickening S) (z : F.val.obj (op B)) :
    crysSectionTop F B z = 0 ↔ z = 0 := by
  exact map_eq_zero_iff (crysSectionTopHom F B) (bijective_crysSectionTop F B).1

/-- **A section over an object is `m` times a section exactly when its restriction to the whole
of the ambient scheme is.**  The restriction is an additive bijection and the `ℕ`-action is
carried by every additive map. -/
theorem exists_nsmul_crysSectionTop_iff (B : CrystallineThickening S) (m : ℕ)
    (z : F.val.obj (op B)) :
    (∃ b, crysSectionTop F B z = m • b) ↔ ∃ y, z = m • y := by
  rw [(bijective_crysSectionTop F B).2.exists]
  exact exists_congr fun y ↦ by
    rw [← crysSectionTopHom_apply, ← crysSectionTopHom_apply, ← map_nsmul]
    exact (bijective_crysSectionTop F B).1.eq_iff

/-- **The base change of the ambient sections of a crystal on `Cris(X/S)` along an arbitrary
morphism of the site is bijective**, on a pair of objects with affine ambient schemes and with a
locally quasi-coherent coefficient sheaf:

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T) ≅ Γ(T', ℱ_{T'})`.

This is `Crystalline.GlobalCrystallineSituation.bijective_ambientBaseChangeTensorFun` at the
small-site data, and it is the small-site counterpart of
`Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMapAlong`.  The
quasi-coherence instance is carried rather than derived because it appears in the *statement*; it
is supplied from local quasi-coherence by
`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherent_ambientSchemeOf`. -/
theorem bijective_crysAmbientBaseChange
    [IsAffine A.obj.thickening.target.scheme] [IsAffine A'.obj.thickening.target.scheme]
    [(ambientSchemeOf A.obj (moduleRestrictionSheaf F A)).IsQuasicoherent]
    (hcrys : IsSheafCrystal F) :
    Function.Bijective (ambientBaseChangeTensorFun k.hom (moduleRestrictionSheaf F A)
      (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)) :=
  bijective_ambientBaseChangeTensorFun k.hom (moduleRestrictionSheaf F A)
    (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
    (isIso_comparisonAbstract_of_isSheafCrystal F k hcrys)

/-! ### The kernel clause for a crystal on `Cris(X/S)` -/

/-- **The kernel clause of the crystal property of [Stacks, Proposition 60.21.3, Tag 07LG], for a
crystal on `Cris(X/S)` and at an arbitrary morphism of the site.**

Let `k : (U', T', δ') ⟶ (U, T, δ)` be a morphism whose restriction map on the sections of
`𝒪_{X/S}` is surjective with kernel the principal ideal `(p^m)`, let the two ambient schemes be
affine and let `ℱ` be a locally quasi-coherent crystal.  Then a section of `ℱ` over `(U, T, δ)`
restricts to zero over `(U', T', δ')` exactly when it is `p^m` times a section over `(U, T, δ)`.

The sections over `(U', T', δ')` are the base change of the sections over `(U, T, δ)` — this is
`Crystalline.GlobalCrystallineSituation.bijective_ambientBaseChangeTensorFun` at the small-site
data — and the kernel of `x ↦ 1 ⊗ x` into a base change along a surjection with principal kernel
is the multiples of the generator, by `TensorProduct.one_tmul_eq_zero_iff_exists_smul`.

This is what the source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF] says needs the crystal
property: "we don't know that `M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a crystal then
this does hold." -/
theorem crysRestrict_eq_zero_iff_exists_nsmul
    [IsAffine A.obj.thickening.target.scheme] [IsAffine A'.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)
    (hsurj : Function.Surjective (crysSheafRingMap k.hom)) (m : ℕ)
    (hker : ∀ b : crysSheafRing S A.obj,
      crysSheafRingMap k.hom b = 0 ↔ ((S.p : crysSheafRing S A.obj) ^ m) ∣ b)
    (x : F.val.obj (op A)) :
    crysRestrict F k x = 0 ↔ ∃ y, x = (S.p ^ m : ℕ) • y := by
  have := isQuasicoherent_ambientSchemeOf F hF A
  have happ : ∀ b : crysSheafRing S A.obj,
      (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom b =
        crysSheafRingMap k.hom b :=
    fun b ↦ appLE_top_eq_crysSheafRingMap k.hom (top_le_preimage_ambient k.hom) b
  have hsurj' : Function.Surjective
      (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom := fun t ↦ by
    obtain ⟨b, hb⟩ := hsurj t
    exact ⟨b, (happ b).trans hb⟩
  have hker' : ∀ b : Γ(A.obj.thickening.target.scheme, ⊤),
      (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom b = 0 ↔
        ((S.p : Γ(A.obj.thickening.target.scheme, ⊤)) ^ m) ∣ b := fun b ↦ by
    rw [happ b]
    exact hker b
  have hsm : ∀ b : Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤),
      ((S.p : Γ(A.obj.thickening.target.scheme, ⊤)) ^ m) • b = (S.p ^ m : ℕ) • b := fun b ↦ by
    rw [← Nat.cast_pow]
    exact Nat.cast_smul_eq_nsmul _ _ _
  rw [← crysSectionTop_eq_zero_iff F A' (crysRestrict F k x),
    ← fmapTopSection_crysSectionTop F k x,
    fmapTopSection_eq_zero_iff_exists_smul k.hom (moduleRestrictionSheaf F A)
      (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
      (isIso_comparisonAbstract_of_isSheafCrystal F k hcrys) hsurj'
      ((S.p : Γ(A.obj.thickening.target.scheme, ⊤)) ^ m) hker' (crysSectionTop F A x)]
  refine Iff.trans ?_ (exists_nsmul_crysSectionTop_iff F A (S.p ^ m) x)
  exact exists_congr fun b ↦ by rw [hsm b]

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
