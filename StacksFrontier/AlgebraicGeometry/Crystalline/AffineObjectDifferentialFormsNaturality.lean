module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentialForms

/-!
# Naturality of the affine identification of the crystalline differential forms

Fix a global crystalline situation `(p, (S, I, γ), X)` and a morphism `k : (U, T, δ) ⟶
(U', T', δ')` of the big crystalline category `CRIS(X/S)` between two objects whose ambient
schemes are affine and whose structure morphisms both factor through *one and the same* affine
open `V ⊆ S`.  `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` of
`AffineObjectDifferentialForms.lean` identifies the sections of `Ω^i_{X/S}` at either object with
the divided power differential forms of its ring of global sections relative to `Γ(V, 𝒪_S)`.
This file proves that those two identifications commute with the transition maps.

The two factorizations are related by one equality of maps on sections,
`Crystalline.GlobalCrystallineSituation.affineBaseAppLE_fac`: the `V`-level analogue of
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE_fac`, saying that `Γ(V, 𝒪_S) ⟶ Γ(T, 𝒪_T)`
is `Γ(V, 𝒪_S) ⟶ Γ(T', 𝒪_{T'}) ⟶ Γ(T, 𝒪_T)`.  Everything else follows from it: the right-hand
vertical of the square is the map on divided power differentials it makes available, and the
degree-`i` statement is the degree-one statement carried up the exterior powers.

## Main definitions

* `Crystalline.dpCompDerivation` and `Crystalline.dpMap` — the map `Ω¹_{B/A,δ} ⟶ Ω¹_{B'/A',δ'}`
  on divided power differentials induced by a square of commutative rings whose vertical on the
  divided power side is a homomorphism of divided power rings.  This is the analogue for
  `Crystalline.dpDifferentials` of `Crystalline.dpConstMap`, which is the same construction for
  the differentials that also kill a set of constants.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsMap` — the right-hand vertical
  of the square in degree one: the map `Ω¹_{Γ(T',𝒪_{T'})/Γ(V,𝒪_S),δ'} ⟶
  Ω¹_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` of divided power differentials relative to the common open `V`.
* `Crystalline.GlobalCrystallineSituation.crysDifferentialsMapₛₗ` and
  `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsMapₛₗ` — the two degree-one
  verticals as semilinear maps over the map on sections, which is the form the exterior powers
  are functorial in.

## Main results

* `Crystalline.GlobalCrystallineSituation.affineBaseAppLE_fac` — the maps `Γ(V, 𝒪_S) ⟶ Γ(T, 𝒪_T)`
  given by two factorizations through one open `V` are compatible with a morphism of
  `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso_naturality` and
  `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso_inv_naturality` — **the
  degree-one identification is natural**, in the two directions: as an equality of maps out of
  the sections of `Ω_{X/S}` and as an equality of maps out of the divided power differentials.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso_naturality` — **the
  degree-`i` identification is natural**, as an equality of maps, for every `i`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso_naturality_ιMulti_d` —
  the degree-`i` square read on the standard wedges `d b₁ ∧ ⋯ ∧ d bᵢ`, which span.

## Implementation notes

The left-hand vertical `Crystalline.GlobalCrystallineSituation.crysDifferentialsMap` is a map of
`ModuleCat`s into a restriction of scalars, while the exterior powers are functorial in a
*semilinear* map; `crysDifferentialsMapₛₗ` and `affineCrysDifferentialsMapₛₗ` are the same two
maps in the semilinear spelling, which is a retyping and no mathematics.  With them the
degree-`i` square is an equality of two semilinear maps out of `⋀^i` of the sections of
`Ω_{X/S}`, and `ExteriorAlgebra.powMapₛₗ_ext` reduces it to the wedges, where the degree-one
square is the whole content.

The mismatch the proof has to bridge is that
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` carries the exterior
powers up with the *linear* same-ring `exteriorPowerCongr`, the two exterior powers at one object
being taken over one ring, while the verticals of the square are semilinear over the map on
sections.  `Stacks.exteriorPowerCongr_ιMulti` and `ExteriorAlgebra.powMapₛₗ_ιMulti` evaluate both
on a wedge, so the two kinds of functoriality meet there.

`affineBaseAppLE_fac` is stated with the identity of `Γ(V, 𝒪_S)` on the left, as
`crysBaseAppLE_fac` is, because that is the shape `Crystalline.dpMap` consumes: the square it
needs has a map of base rings on one side, and here that map is the identity of the common open.

## What is and is not proved

No tag attribute is placed by this file.  [Stacks, Tag 07LF] is **not** proved here: the
cosimplicial comparison it states needs, besides this naturality, the divided power envelopes of
the Čech nerve and the vanishing of the higher cohomology of the resulting complex, none of which
is touched.  What is proved is exactly that the affine identification of [Stacks, Tag 07J0], in
every degree, commutes with the transition maps of `Ω^i_{X/S}` — for one common open `V` of the
divided power base, which is the situation the cosimplicial argument supplies, and with no
hypothesis on the morphism `k` beyond the two factorizations.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline

/-! ### Functoriality of the divided power differentials of a morphism of commutative rings -/

section Functoriality

variable {A B A' B' : CommRingCat.{u}} {J : Ideal B} {J' : Ideal B'}
  {f : A ⟶ B} {f' : A' ⟶ B'} {g : A ⟶ A'} {g' : B ⟶ B'}

/-- Composing a homomorphism `g'` of divided power rings over `g` with the universal divided
power differential of `f'` gives a derivation of `B` into the divided power differentials of
`f'`, the latter viewed as a `B`-module along `g'`.  This is `Crystalline.dpConstCompDerivation`
without the constants. -/
noncomputable def dpCompDerivation (fac : g ≫ f' = f ≫ g') (hJ' : DividedPowers J') :
    ((ModuleCat.restrictScalars g'.hom).obj (dpDifferentials f' hJ')).Derivation f :=
  ModuleCat.Derivation.mk (fun b ↦ (dpD f' hJ').d (g' b))
    (fun b b' ↦ by
      rw [map_add]
      exact ModuleCat.Derivation.d_add (dpD f' hJ') (g' b) (g' b'))
    (fun b b' ↦ by
      rw [map_mul]
      exact ModuleCat.Derivation.d_mul (dpD f' hJ') (g' b) (g' b'))
    (fun a ↦ by
      have h : g' (f a) = f' (g a) := by
        rw [← CommRingCat.comp_apply, ← fac, CommRingCat.comp_apply]
      rw [h]
      exact ModuleCat.Derivation.d_map (dpD f' hJ') (g a))

/-- **The map on divided power differentials induced by a homomorphism of divided power rings**
over a map of base rings.  This is `Crystalline.dpConstMap` for the differentials that do not
divide out any constants. -/
noncomputable def dpMap (fac : g ≫ f' = f ≫ g') (hJ : DividedPowers J) (hJ' : DividedPowers J')
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) :
    dpDifferentials f hJ ⟶ (ModuleCat.restrictScalars g'.hom).obj (dpDifferentials f' hJ') :=
  dpDesc (dpCompDerivation fac hJ')
    (fun n x hx ↦ by
      have hgx : g' x ∈ J' := mem_ideal_of_isDPMorphism hg hx
      have h1 : (dpD f' hJ').d (g' (hJ.dpow (n + 1) x))
          = hJ'.dpow n (g' x) • (dpD f' hJ').d (g' x) := by
        rw [← dpow_of_isDPMorphism hg hx]
        exact dpd_dpow f' hJ' n (g' x) hgx
      have h2 : hJ'.dpow n (g' x) • (dpD f' hJ').d (g' x)
          = g' (hJ.dpow n x) • (dpD f' hJ').d (g' x) := by
        rw [dpow_of_isDPMorphism hg hx]
      exact h1.trans h2)

/-- The map `Crystalline.dpMap` carries the universal divided power differential `d b` of `b` to
the universal divided power differential `d (g' b)` of its image. -/
@[simp]
theorem dpMap_d (fac : g ≫ f' = f ≫ g') (hJ : DividedPowers J) (hJ' : DividedPowers J')
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) (b : B) :
    dpMap fac hJ hJ' hg (dpd hJ b) = dpd hJ' (g' b) :=
  dpDesc_d _ _ b

end Functoriality

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) {A B : Thickening S} (k : A ⟶ B)
  {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V)
  (hVB : (⊤ : B.thickening.target.scheme.Opens) ≤ B.toBase.hom ⁻¹ᵁ V)

/-! ### The base maps of a common open are compatible with the transition maps -/

/-- **The two factorizations through one open `V` of the divided power base are compatible with a
morphism of `CRIS(X/S)`.**  This is the `V`-level analogue of
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE_fac`, and the identity of `Γ(V, 𝒪_S)` on
the left is there because `Crystalline.dpMap` consumes a square of rings. -/
theorem affineBaseAppLE_fac :
    (𝟙 Γ(S.S.scheme, V)) ≫ affineBaseAppLE S A hVA =
      affineBaseAppLE S B hVB ≫ k.targetHom.hom.appTop := by
  have hb : A.toBase.hom = k.targetHom.hom ≫ B.toBase.hom := by
    rw [← DividedPowerScheme.Hom.comp_hom, k.base_naturality]
  have e1 := Scheme.Hom.appLE_comp_appLE k.targetHom.hom B.toBase.hom V ⊤ ⊤ hVB
    (le_preimage_top k.targetHom.hom (⊤ : A.thickening.target.scheme.Opens))
  rw [appLE_top_top] at e1
  rw [Category.id_comp, affineBaseAppLE, affineBaseAppLE]
  revert hVA
  rw [hb]
  exact fun _ ↦ e1.symm

/-! ### The degree-one square -/

/-- **The right-hand vertical of the square in degree one**: the map on divided power
differentials relative to the common open `V` of the divided power base induced by a morphism of
`CRIS(X/S)`.  The map on sections is a homomorphism of divided power rings, and
`affineBaseAppLE_fac` is the compatibility with the two base maps. -/
noncomputable def affineCrysDifferentialsMap :
    affineCrysDifferentialsObj S B hVB ⟶
      (ModuleCat.restrictScalars k.targetHom.hom.appTop.hom).obj
        (affineCrysDifferentialsObj S A hVA) :=
  dpMap (affineBaseAppLE_fac S k hVA hVB) (crysDividedPowers S B) (crysDividedPowers S A)
    (k.targetHom.compatible ⊤)

/-- The map `affineCrysDifferentialsMap` carries the universal divided power differential of a
section `b` of `𝒪_{T'}` to the universal divided power differential of its image in `Γ(T, 𝒪_T)`. -/
@[simp]
theorem affineCrysDifferentialsMap_dpd (b : Γ(B.thickening.target.scheme, ⊤)) :
    affineCrysDifferentialsMap S k hVA hVB
        (dpd (f := affineBaseAppLE S B hVB) (crysDividedPowers S B) b) =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A)
        (k.targetHom.hom.appTop b) :=
  dpMap_d _ _ _ _ b

/-- **The degree-one identification is natural**, as an equality of maps out of the sections of
`Ω_{X/S}`: identifying over `(U', T', δ')` and then restricting is restricting and then
identifying over `(U, T, δ)`.  Both composites carry `d b` to the universal divided power
differential of the image of `b`, and those span. -/
theorem affineCrysDifferentialsIso_naturality [IsAffine A.thickening.target.scheme]
    [IsAffine B.thickening.target.scheme] (hV : IsAffineOpen V) :
    (affineCrysDifferentialsIso S B hVB hV).hom ≫ affineCrysDifferentialsMap S k hVA hVB =
      crysDifferentialsMap S k ≫
        (ModuleCat.restrictScalars k.targetHom.hom.appTop.hom).map
          (affineCrysDifferentialsIso S A hVA hV).hom := by
  refine dpConstDifferentials_ext fun b ↦ ?_
  have hleft : affineCrysDifferentialsMap S k hVA hVB
      ((affineCrysDifferentialsIso S B hVB hV).hom ((crysDifferentialsD S B).d b)) =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A)
        (k.targetHom.hom.appTop b) :=
    (congrArg (fun x ↦ affineCrysDifferentialsMap S k hVA hVB x)
      (affineCrysDifferentialsHom_d S B hVB hV b)).trans
      (affineCrysDifferentialsMap_dpd S k hVA hVB b)
  have hright : (affineCrysDifferentialsIso S A hVA hV).hom
      (crysDifferentialsMap S k ((crysDifferentialsD S B).d b)) =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A)
        (k.targetHom.hom.appTop b) :=
    (congrArg (fun x ↦ (affineCrysDifferentialsIso S A hVA hV).hom x)
      (crysDifferentialsMap_d S k b)).trans
      (affineCrysDifferentialsHom_d S A hVA hV (k.targetHom.hom.appTop b))
  exact hleft.trans hright.symm

/-- The degree-one square, read on a section of `Ω_{X/S}` over `(U', T', δ')`. -/
theorem affineCrysDifferentialsIso_naturality_apply [IsAffine A.thickening.target.scheme]
    [IsAffine B.thickening.target.scheme] (hV : IsAffineOpen V)
    (x : ↥(crysDifferentialsObj S B)) :
    affineCrysDifferentialsMap S k hVA hVB ((affineCrysDifferentialsIso S B hVB hV).hom x) =
      (affineCrysDifferentialsIso S A hVA hV).hom (crysDifferentialsMap S k x) :=
  (ModuleCat.comp_apply _ _ x).symm.trans
    ((congrArg (fun φ ↦ ModuleCat.Hom.hom φ x)
      (affineCrysDifferentialsIso_naturality S k hVA hVB hV)).trans
        (ModuleCat.comp_apply _ _ x))

/-- **The degree-one identification is natural, in the inverse direction**: an equality of maps
out of the divided power differentials relative to `V`.  Both composites carry the universal
divided power differential of `b` to the universal `S`-derivation of the image of `b`. -/
theorem affineCrysDifferentialsIso_inv_naturality [IsAffine A.thickening.target.scheme]
    [IsAffine B.thickening.target.scheme] (hV : IsAffineOpen V) :
    affineCrysDifferentialsMap S k hVA hVB ≫
        (ModuleCat.restrictScalars k.targetHom.hom.appTop.hom).map
          (affineCrysDifferentialsIso S A hVA hV).inv =
      (affineCrysDifferentialsIso S B hVB hV).inv ≫ crysDifferentialsMap S k := by
  refine dpDifferentials_ext fun b ↦ ?_
  have hleft : (affineCrysDifferentialsIso S A hVA hV).inv
      (affineCrysDifferentialsMap S k hVA hVB
        (dpd (f := affineBaseAppLE S B hVB) (crysDividedPowers S B) b)) =
      (crysDifferentialsD S A).d (k.targetHom.hom.appTop b) :=
    (congrArg (fun x ↦ (affineCrysDifferentialsIso S A hVA hV).inv x)
      (affineCrysDifferentialsMap_dpd S k hVA hVB b)).trans
      (affineCrysDifferentialsInv_dpd S A hVA (k.targetHom.hom.appTop b))
  have hright : crysDifferentialsMap S k ((affineCrysDifferentialsIso S B hVB hV).inv
      (dpd (f := affineBaseAppLE S B hVB) (crysDividedPowers S B) b)) =
      (crysDifferentialsD S A).d (k.targetHom.hom.appTop b) :=
    (congrArg (fun x ↦ crysDifferentialsMap S k x)
      (affineCrysDifferentialsInv_dpd S B hVB b)).trans
      (crysDifferentialsMap_d S k b)
  exact hleft.trans hright.symm

/-! ### The degree-`i` square -/

/-- **The transition map of `Ω_{X/S}` as a semilinear map** over the map on sections.  The
exterior powers are functorial in this form; see the implementation notes. -/
noncomputable def crysDifferentialsMapₛₗ :
    ↥(crysDifferentialsObj S B) →ₛₗ[k.targetHom.hom.appTop.hom] ↥(crysDifferentialsObj S A) where
  toFun x := crysDifferentialsMap S k x
  map_add' x y := map_add (crysDifferentialsMap S k).hom x y
  map_smul' c x := (crysDifferentialsMap S k).hom.map_smul c x

/-- **The degree-one right-hand vertical as a semilinear map** over the map on sections. -/
noncomputable def affineCrysDifferentialsMapₛₗ :
    ↥(affineCrysDifferentialsObj S B hVB) →ₛₗ[k.targetHom.hom.appTop.hom]
      ↥(affineCrysDifferentialsObj S A hVA) where
  toFun x := affineCrysDifferentialsMap S k hVA hVB x
  map_add' x y := map_add (affineCrysDifferentialsMap S k hVA hVB).hom x y
  map_smul' c x := (affineCrysDifferentialsMap S k hVA hVB).hom.map_smul c x

/-- **The transition maps of `Ω^i_{X/S}` are the exterior powers of those of `Ω_{X/S}`**, read
through the retyping of the sections of `Crystalline.GlobalCrystallineSituation.
crysFormSectionsTop`.  This is `PresheafOfModules.extPowSections_map` at the presheaf of
crystalline differentials, and it holds by `rfl`. -/
theorem crysFormSectionsTop_map (i : ℕ) (z : ((crysDifferentialForms S i).obj (op B) : Type u)) :
    crysFormSectionsTop S A i ((crysDifferentialForms S i).map k.op z) =
      ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom (crysDifferentialsMapₛₗ S k)
        (crysFormSectionsTop S B i z) := rfl

/-- **The degree-`i` square at the level of exterior powers.**  Carrying the degree-one
identification up the exterior powers with the linear `exteriorPowerCongr` commutes with the
semilinear exterior powers of the two transition maps.  The wedges span, and on a wedge this is
the degree-one square `affineCrysDifferentialsIso_naturality`. -/
theorem exteriorPowerCongr_affineCrysDifferentialsIso_naturality
    [IsAffine A.thickening.target.scheme] [IsAffine B.thickening.target.scheme]
    (hV : IsAffineOpen V) (i : ℕ)
    (w : ⋀[Γ(B.thickening.target.scheme, ⊤)]^i ↥(crysDifferentialsObj S B)) :
    exteriorPowerCongr i (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv
        (ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom (crysDifferentialsMapₛₗ S k) w) =
      ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
        (affineCrysDifferentialsMapₛₗ S k hVA hVB)
        (exteriorPowerCongr i (affineCrysDifferentialsIso S B hVB hV).toLinearEquiv w) := by
  have hmaps :
      (exteriorPowerCongr i
            (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv).toLinearMap.comp
          (ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom (crysDifferentialsMapₛₗ S k)) =
        (ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
            (affineCrysDifferentialsMapₛₗ S k hVA hVB)).comp
          (exteriorPowerCongr i
            (affineCrysDifferentialsIso S B hVB hV).toLinearEquiv).toLinearMap := by
    refine ExteriorAlgebra.powMapₛₗ_ext fun v ↦ ?_
    have hl : exteriorPowerCongr i (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv
        (ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom (crysDifferentialsMapₛₗ S k)
          (exteriorPower.ιMulti Γ(B.thickening.target.scheme, ⊤) i v)) =
        exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
          (affineCrysDifferentialsIso S A hVA hV).hom (crysDifferentialsMap S k (v j)) :=
      (congrArg (fun x ↦ exteriorPowerCongr i
            (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv x)
          (ExteriorAlgebra.powMapₛₗ_ιMulti i _ (crysDifferentialsMapₛₗ S k) v)).trans
        (Stacks.exteriorPowerCongr_ιMulti i _ _)
    have hr : ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
        (affineCrysDifferentialsMapₛₗ S k hVA hVB)
        (exteriorPowerCongr i (affineCrysDifferentialsIso S B hVB hV).toLinearEquiv
          (exteriorPower.ιMulti Γ(B.thickening.target.scheme, ⊤) i v)) =
        exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
          affineCrysDifferentialsMap S k hVA hVB
            ((affineCrysDifferentialsIso S B hVB hV).hom (v j)) :=
      (congrArg (fun x ↦ ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
            (affineCrysDifferentialsMapₛₗ S k hVA hVB) x)
          (Stacks.exteriorPowerCongr_ιMulti i _ v)).trans
        (ExteriorAlgebra.powMapₛₗ_ιMulti i _ _ _)
    refine hl.trans (Eq.trans ?_ hr.symm)
    exact congrArg _ (funext fun j ↦
      (affineCrysDifferentialsIso_naturality_apply S k hVA hVB hV (v j)).symm)
  exact DFunLike.congr_fun hmaps w

/-- **[Stacks, Tag 07J0] in every degree is natural in the object.**  For a morphism of
`CRIS(X/S)` between two affine objects whose structure morphisms factor through one affine open
`V` of the divided power base, the identification of the sections of `Ω^i_{X/S}` with the divided
power differential forms relative to `Γ(V, 𝒪_S)` commutes with the transition maps: restricting
and then identifying is identifying and then applying the `i`-th exterior power of the degree-one
map on divided power differentials. -/
theorem affineCrysDifferentialFormsIso_naturality [IsAffine A.thickening.target.scheme]
    [IsAffine B.thickening.target.scheme] (hV : IsAffineOpen V) (i : ℕ)
    (z : ((crysDifferentialForms S i).obj (op B) : Type u)) :
    affineCrysDifferentialFormsIso S A hVA hV i ((crysDifferentialForms S i).map k.op z) =
      ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
        (affineCrysDifferentialsMapₛₗ S k hVA hVB)
        (affineCrysDifferentialFormsIso S B hVB hV i z) :=
  (congrArg
    (fun x ↦ exteriorPowerCongr i (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv x)
      (crysFormSectionsTop_map S k i z)).trans
    (exteriorPowerCongr_affineCrysDifferentialsIso_naturality S k hVA hVB hV i
      (crysFormSectionsTop S B i z))

/-- **The degree-`i` square on the standard wedges.**  A wedge `d b₁ ∧ ⋯ ∧ d bᵢ` of universal
`S`-derivations over `(U', T', δ')` is carried, round the square, to the wedge of the universal
divided power differentials of the images of the `bⱼ`.  Those wedges span the sections of
`Ω^i_{X/S}`, so this is the square read on generators; it needs no factorization of the structure
morphism of `(U', T', δ')` through `V`, the transition map of `Ω^i_{X/S}` already carrying the
wedge to the wedge of the images. -/
theorem affineCrysDifferentialFormsIso_naturality_ιMulti_d
    [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (i : ℕ) (b : Fin i → Γ(B.thickening.target.scheme, ⊤)) :
    affineCrysDifferentialFormsIso S A hVA hV i
        ((crysDifferentialForms S i).map k.op
          ((crysFormSectionsTop S B i).symm
            (exteriorPower.ιMulti Γ(B.thickening.target.scheme, ⊤) i fun j ↦
              (crysDifferentialsD S B).d (b j)))) =
      exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
        dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A)
          (k.targetHom.hom.appTop (b j)) := by
  have h1 : crysFormSectionsTop S A i
      ((crysDifferentialForms S i).map k.op
        ((crysFormSectionsTop S B i).symm
          (exteriorPower.ιMulti Γ(B.thickening.target.scheme, ⊤) i fun j ↦
            (crysDifferentialsD S B).d (b j)))) =
      exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
        (crysDifferentialsD S A).d (k.targetHom.hom.appTop (b j)) := by
    refine (crysFormSectionsTop_map S k i _).trans ?_
    refine (congrArg (fun x ↦ ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom
        (crysDifferentialsMapₛₗ S k) x)
      (LinearEquiv.apply_symm_apply (crysFormSectionsTop S B i) _)).trans ?_
    refine (ExteriorAlgebra.powMapₛₗ_ιMulti i k.targetHom.hom.appTop.hom
      (crysDifferentialsMapₛₗ S k) _).trans (congrArg _ (funext fun j ↦ ?_))
    exact crysDifferentialsMap_d S k (b j)
  have h2 : (crysDifferentialForms S i).map k.op
      ((crysFormSectionsTop S B i).symm
        (exteriorPower.ιMulti Γ(B.thickening.target.scheme, ⊤) i fun j ↦
          (crysDifferentialsD S B).d (b j))) =
      (crysFormSectionsTop S A i).symm
        (exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
          (crysDifferentialsD S A).d (k.targetHom.hom.appTop (b j))) :=
    (LinearEquiv.symm_apply_apply (crysFormSectionsTop S A i) _).symm.trans
      (congrArg (fun x ↦ (crysFormSectionsTop S A i).symm x) h1)
  exact (congrArg (fun x ↦ affineCrysDifferentialFormsIso S A hVA hV i x) h2).trans
    (affineCrysDifferentialFormsIso_ιMulti_d S A hVA hV i fun j ↦
      k.targetHom.hom.appTop (b j))

end GlobalCrystallineSituation

end Crystalline

end
