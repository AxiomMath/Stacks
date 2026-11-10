module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIso

/-!
# `H × W` is the fibre product `W ×_{𝓜₁,₁} W`

Let `W` be the Weierstrass scheme with its universal plane cubic `E_W`, and let `H` be the group
scheme of coordinate changes of a Weierstrass equation, acting on `W`. This file proves the
torsor property used in the proof of Tag 072T: over `H × W` the coordinate change gives an
isomorphism between the pullbacks of `E_W` along the action `H × W ⟶ W` and along the projection
`H × W ⟶ W`, and this triple makes `H × W` the fibre product `W ×_{𝓜₁,₁} W`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.familyOfEq`: the identification of the
  plane cubics of two equal Weierstrass equations.
* `AlgebraicGeometry.ModuliEllipticCurves.Comparison.ofFamilyIsoPullback`: the triple
  `(a, b, ρ ×_S T)` obtained by pulling back an isomorphism `ρ` of restricted families along a
  morphism `T ⟶ S`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.ringIso`: for ring maps
  `φa, φb : ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ] → R` and a coordinate change `γ` over `R` with
  `curve.map φa = γ • curve.map φb`, the isomorphism of the pullbacks of `E_W` to `Spec R`
  induced by `γ`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.universalComparison`: the universal triple
  `(actionMap, productToBase, α)` over `H × W`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.representsComparisons_coordinateChange`:
  `H × W` is the fibre product `W ×_{𝓜₁,₁} W`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.mapMap_comp` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.familyOfMapIso_comp`: changing
  coefficients in two steps is changing coefficients along the composite.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.ringIso_pullback`: the isomorphism
  `ringIso` is compatible with base change along a ring map.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.baseChange_universalComparison`: the base
  change of the universal triple to an affine scheme `Spec A` is `ringIso` over `A`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.bijective_baseChange_universalComparison`:
  on `Spec A`-points, base change of the universal triple is a bijection onto the triples.

## Implementation notes

A triple over a general scheme `T` is never built by hand: the triple classified by
`g : T ⟶ H × W` is the base change along `g` of the universal one, so naturality is
`Comparison.baseChange_comp`. The universal triple is the pullback along
`H × W ⟶ Spec Γ(H × W, ⊤)` of the ring-level isomorphism `ringIso`, which is assembled from
`changeIso` and `familyOfMapIso`. Bijectivity is tested on affine schemes by
`representsComparisons_of_bijective_affine`: over `Spec A` both morphisms to `W` come from ring
maps, the isomorphism of the triple read through `familyOfMapIso` is an isomorphism of plane
cubics over `A`, and `exists_unique_variableChange` identifies it with `changeIso` of a unique
coordinate change.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

/-! ### Triples obtained by pulling back an isomorphism of restricted families -/

namespace Comparison

variable {W W' S S' T U : Scheme.{u}} {F : PointedFamily W} {F' : PointedFamily W'}

/-- The triple `(a, b, ρ ×_S T)` for an isomorphism `ρ : F ×_{W,c} S ≅ F' ×_{W',c'} S` of
restricted families and a morphism `t : T ⟶ S` with `a = t ≫ c` and `b = t ≫ c'`. -/
def ofFamilyIsoPullback {c : S ⟶ W} {c' : S ⟶ W'} (ρ : FamilyIso (F.pullback c) (F'.pullback c'))
    (t : T ⟶ S) {a : T ⟶ W} {b : T ⟶ W'} (ha : a = t ≫ c) (hb : b = t ≫ c') :
    Comparison F F' T :=
  ofFamilyIso a b (((F.pullbackPullbackIso c t ha).symm.trans (ρ.pullback t)).trans
    (F'.pullbackPullbackIso c' t hb))

variable {c : S ⟶ W} {c' : S ⟶ W'}

/-- The triple `(a, b, ρ ×_S T)` depends on `ρ` only through its isomorphism of total spaces,
and on `t` only up to equality. -/
theorem ofFamilyIsoPullback_congr {ρ σ : FamilyIso (F.pullback c) (F'.pullback c')}
    (hρ : ρ.iso.hom = σ.iso.hom) {t t' : T ⟶ S} (ht : t = t') {a : T ⟶ W} {b : T ⟶ W'}
    (ha : a = t ≫ c) (hb : b = t ≫ c') (ha' : a = t' ≫ c) (hb' : b = t' ≫ c') :
    ofFamilyIsoPullback ρ t ha hb = ofFamilyIsoPullback σ t' ha' hb' := by
  subst ht
  obtain rfl : ρ = σ := by
    obtain ⟨ρ, _, _⟩ := ρ
    obtain ⟨σ, _, _⟩ := σ
    obtain rfl : ρ = σ := Iso.ext hρ
    rfl
  rfl

/-- The base change of `(a, b, ρ ×_S T)` along `f : U ⟶ T` is `(f ≫ a, f ≫ b, ρ ×_S U)`. -/
theorem baseChange_ofFamilyIsoPullback (ρ : FamilyIso (F.pullback c) (F'.pullback c'))
    (t : T ⟶ S) {a : T ⟶ W} {b : T ⟶ W'} (ha : a = t ≫ c) (hb : b = t ≫ c') (f : U ⟶ T) :
    (ofFamilyIsoPullback ρ t ha hb).baseChange f =
      ofFamilyIsoPullback ρ (f ≫ t) (a := f ≫ a) (b := f ≫ b) (by rw [ha, Category.assoc])
        (by rw [hb, Category.assoc]) := by
  have key : (((F.pullbackPullbackIso c (f ≫ t)
        (by rw [ha, Category.assoc] : f ≫ a = (f ≫ t) ≫ c)).iso.inv ≫
        (ρ.pullback (f ≫ t)).iso.hom) ≫ (F'.pullbackPullbackIso c' (f ≫ t)
          (by rw [hb, Category.assoc] : f ≫ b = (f ≫ t) ≫ c')).iso.hom) ≫
          F'.pullbackMap f (rfl : f ≫ b = f ≫ b) =
      F.pullbackMap f (rfl : f ≫ a = f ≫ a) ≫ (((F.pullbackPullbackIso c t ha).iso.inv ≫
        (ρ.pullback t).iso.hom) ≫ (F'.pullbackPullbackIso c' t hb).iso.hom) := by
    simp only [Category.assoc]
    rw [← F'.pullbackMap_pullbackPullbackIso_hom c' f rfl hb (by rw [hb, Category.assoc]) rfl,
      ← FamilyIso.pullbackMap_pullback_hom_assoc ρ f rfl,
      ← F.pullbackMap_pullbackPullbackIso_inv_assoc c f rfl ha (by rw [ha, Category.assoc]) rfl]
  refine Eq.symm (IsBaseChange.eq_baseChange ⟨rfl, rfl, ?_⟩)
  exact key

/-- Replacing `t` by an equal morphism does not change `(a, b, ρ ×_S T)`. -/
theorem ofFamilyIsoPullback_congr_t (ρ : FamilyIso (F.pullback c) (F'.pullback c'))
    {t t' : T ⟶ S} (ht : t = t') {a : T ⟶ W} {b : T ⟶ W'} (ha : a = t ≫ c) (hb : b = t ≫ c') :
    ofFamilyIsoPullback ρ t ha hb = ofFamilyIsoPullback ρ t' (ht ▸ ha) (ht ▸ hb) := by
  subst ht
  rfl

end Comparison

/-- The base change of a composite of isomorphisms of pointed families is the composite of their
base changes. -/
@[simp]
theorem FamilyIso.trans_pullback_iso_hom {S T : Scheme.{u}} {E F G : PointedFamily S}
    (e : FamilyIso E F) (f : FamilyIso F G) (a : T ⟶ S) :
    ((e.trans f).pullback a).iso.hom = (e.pullback a).iso.hom ≫ (f.pullback a).iso.hom := by
  ext <;> simp

namespace Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Plane cubics of equal Weierstrass equations -/

section Eq

variable {R : Type u} [CommRing R]

/-- The identification `E_D = E_{D'}` of the plane cubics of two equal Weierstrass equations, as
an isomorphism of pointed families over `Spec R`. -/
def familyOfEq {D D' : WeierstrassCurve R} (h : D = D') : FamilyIso (familyOf D) (familyOf D') where
  iso := eqToIso (congrArg projOf h)
  iso_map := by subst h; exact Category.id_comp _
  zero_iso := by subst h; exact Category.comp_id _

/-- The identification of plane cubics is `eqToHom` on total spaces. -/
@[simp]
theorem familyOfEq_iso_hom {D D' : WeierstrassCurve R} (h : D = D') :
    (familyOfEq h).iso.hom = eqToHom (congrArg projOf h) :=
  rfl

/-- The inverse identification of plane cubics is `eqToHom` on total spaces. -/
@[simp]
theorem familyOfEq_iso_inv {D D' : WeierstrassCurve R} (h : D = D') :
    (familyOfEq h).iso.inv = eqToHom (congrArg projOf h.symm) :=
  rfl

/-- The coordinate-change isomorphism commutes with the identification of the plane cubics of
equal Weierstrass equations. -/
@[reassoc]
theorem familyOfEq_changeIso (γ : WeierstrassCurve.VariableChange R) {D D' : WeierstrassCurve R}
    (h : D = D') :
    (familyOfEq (congrArg (γ • ·) h)).iso.hom ≫ (changeIso γ D').iso.hom =
      (changeIso γ D).iso.hom ≫ (familyOfEq h).iso.hom := by
  subst h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The base change isomorphism commutes with the identification of the plane cubics of equal
Weierstrass equations. -/
@[reassoc]
theorem familyOfMapIso_familyOfEq {S : Type u} [CommRing S] (φ : R →+* S)
    {D D' : WeierstrassCurve R} (h : D = D') :
    (familyOfMapIso D φ).iso.inv ≫
        ((familyOfEq h).pullback (Spec.map (CommRingCat.ofHom φ))).iso.hom =
      (familyOfEq (congrArg (fun E : WeierstrassCurve R => E.map φ) h)).iso.hom ≫
        (familyOfMapIso D' φ).iso.inv := by
  subst h
  have e : ((familyOfEq (rfl : D = D)).pullback (Spec.map (CommRingCat.ofHom φ))).iso.hom =
      𝟙 _ := by
    refine Limits.pullback.hom_ext ?_ ?_
    · exact (FamilyIso.pullback_hom_fst _ _).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)
    · exact (FamilyIso.pullback_hom_snd _ _).trans (Category.id_comp _).symm
  rw [e]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Two identifications of plane cubics compose to the identification along the composite
equality. -/
@[reassoc (attr := simp)]
theorem familyOfEq_trans {D D' D'' : WeierstrassCurve R} (h : D = D') (h' : D' = D'') :
    (familyOfEq h).iso.hom ≫ (familyOfEq h').iso.hom = (familyOfEq (h.trans h')).iso.hom := by
  subst h h'
  exact Category.id_comp _

/-- The identification of a plane cubic with itself is the identity. -/
@[simp]
theorem familyOfEq_refl_hom {D : WeierstrassCurve R} (h : D = D) :
    (familyOfEq h).iso.hom = 𝟙 _ :=
  rfl

/-- The identification of plane cubics lies over `Spec R`. -/
@[reassoc]
theorem familyOfEq_hom_projectionOf {D D' : WeierstrassCurve R} (h : D = D') :
    (familyOfEq h).iso.hom ≫ projectionOf D' = projectionOf D :=
  (familyOfEq h).iso_map

/-- `familyOfMapIso_changeIso`, with the identification of plane cubics written as
`familyOfEq`. -/
@[reassoc]
theorem familyOfMapIso_changeIso_familyOfEq {S : Type u} [CommRing S]
    (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) (ψ : R →+* S) :
    (familyOfMapIso (γ • C) ψ).iso.inv ≫
        ((changeIso γ C).pullback (Spec.map (CommRingCat.ofHom ψ))).iso.hom ≫
          (familyOfMapIso C ψ).iso.hom =
      (familyOfEq (WeierstrassCurve.map_variableChange C γ ψ).symm).iso.hom ≫
        (changeIso (γ.map ψ) (C.map ψ)).iso.hom :=
  familyOfMapIso_changeIso γ C ψ

end Eq

/-! ### Changing coefficients in two steps -/

section MapComp

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']

/-- `MvPolynomial.map` of a composite, as graded ring homomorphisms. -/
theorem polyGradedMap_comp (φ : R →+* S) (ψ : S →+* S') :
    (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ) =
      Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) (ψ.comp φ) :=
  GradedRingHom.ext fun p => MvPolynomial.map_map φ ψ p

/-- Changing coefficients along `φ` and then along `ψ` is changing coefficients along `ψ.comp φ`,
once the plane cubics of `(C.map φ).map ψ` and `C.map (ψ.comp φ)` are identified. -/
theorem mapMap_comp (C : WeierstrassCurve R) (φ : R →+* S) (ψ : S →+* S') :
    mapMap C (ψ.comp φ) =
      eqToHom (congrArg projOf (C.map_map φ ψ).symm) ≫ mapMap (C.map φ) ψ ≫ mapMap C φ := by
  have h₂ : Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) (ψ.comp φ) (cubicOf C) ∈
      (cubicIdealOf ((C.map φ).map ψ)).toIdeal := by
    rw [C.map_map φ ψ]
    exact map_cubicOf_mem C (ψ.comp φ)
  have e : mapMap (C.map φ) ψ ≫ mapMap C φ =
      Proj.map ((mapHom (C.map φ) ψ).comp (mapHom C φ))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_mapHom C φ)
          (irrelevant_le_map_mapHom (C.map φ) ψ)) :=
    (Proj.map_comp _ _ _ _).symm
  rw [e]
  refine map_eq_eqToHom_comp_map (C.map_map φ ψ) _ (map_cubicOf_mem C (ψ.comp φ)) h₂ _ _ rfl ?_
    _ _
  refine GradedRingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GradedRingHom.comp_apply, mapHom, mapHom, coordHom_mk, coordHom_mk, coordHom_mk,
    ← polyGradedMap_comp, GradedRingHom.comp_apply]

/-- `mapMap_comp`, with the identification of plane cubics written as `familyOfEq`. -/
@[reassoc]
theorem familyOfEq_mapMap_comp (C : WeierstrassCurve R) (φ : R →+* S) (ψ : S →+* S') :
    (familyOfEq (C.map_map φ ψ)).iso.hom ≫ mapMap C (ψ.comp φ) =
      mapMap (C.map φ) ψ ≫ mapMap C φ := by
  rw [mapMap_comp]
  change eqToHom (congrArg projOf (C.map_map φ ψ)) ≫
    eqToHom (congrArg projOf (C.map_map φ ψ).symm) ≫ _ = _
  rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- `familyOfEq_mapMap_comp`, with each change of coefficients written as the inverse of
`familyOfMapIso` followed by the first projection of the pullback. -/
theorem familyOfEq_familyOfMapIso_inv_fst (C : WeierstrassCurve R) (φ : R →+* S)
    (ψ : S →+* S') :
    (familyOfEq (C.map_map φ ψ)).iso.hom ≫ (familyOfMapIso C (ψ.comp φ)).iso.inv ≫
        Limits.pullback.fst (familyOf C).map (Spec.map (CommRingCat.ofHom (ψ.comp φ))) =
      (familyOfMapIso (C.map φ) ψ).iso.inv ≫
        Limits.pullback.fst (familyOf (C.map φ)).map (Spec.map (CommRingCat.ofHom ψ)) ≫
          (familyOfMapIso C φ).iso.inv ≫
            Limits.pullback.fst (familyOf C).map (Spec.map (CommRingCat.ofHom φ)) := by
  rw [familyOfMapIso_inv_fst, familyOfMapIso_inv_fst]
  exact (familyOfEq_mapMap_comp C φ ψ).trans (familyOfMapIso_inv_fst_assoc _ _ _).symm

/-- **Base change in two steps.** The pullback of `familyOfMapIso C φ` along
`Spec S' ⟶ Spec S`, followed by `familyOfMapIso (C.map φ) ψ`, is the restriction of a
restriction followed by `familyOfMapIso C (ψ.comp φ)`, up to the identification of the plane
cubics of `(C.map φ).map ψ` and `C.map (ψ.comp φ)`. -/
theorem familyOfMapIso_comp (C : WeierstrassCurve R) (φ : R →+* S) (ψ : S →+* S')
    (hb : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)) :
    ((familyOfMapIso C φ).pullback (Spec.map (CommRingCat.ofHom ψ))).iso.hom ≫
        (familyOfMapIso (C.map φ) ψ).iso.hom ≫ (familyOfEq (C.map_map φ ψ)).iso.hom =
      ((familyOf C).pullbackPullbackIso _ _ hb).iso.hom ≫
        (familyOfMapIso C (ψ.comp φ)).iso.hom := by
  rw [← Iso.comp_inv_eq]
  refine Limits.pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [familyOfEq_familyOfMapIso_inv_fst, Iso.hom_inv_id_assoc,
      FamilyIso.pullback_hom_fst_assoc, Iso.hom_inv_id_assoc,
      PointedFamily.pullbackPullbackIso_hom_fst]
  · simp only [Category.assoc]
    rw [familyOfMapIso_inv_snd, familyOfEq_hom_projectionOf, familyOfMapIso_hom_projectionOf,
      FamilyIso.pullback_hom_snd, PointedFamily.pullbackPullbackIso_hom_snd]

end MapComp

/-! ### The isomorphism of restricted universal cubics induced by a coordinate change -/

section RingIso

variable {R : Type u} [CommRing R]

/-- For ring maps `φa, φb : ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ] → R` and a coordinate change `γ` over
`R` with `curve.map φa = γ • curve.map φb`, the isomorphism `E_W ×_{W,φa} Spec R ≅
E_W ×_{W,φb} Spec R` of pointed families over `Spec R` given by `familyOfMapIso`, the
identification `E_{curve.map φa} = E_{γ • curve.map φb}`, `changeIso γ (curve.map φb)` and the
inverse of `familyOfMapIso`. -/
def ringIso (φa φb : baseRing.{u} →+* R) (γ : WeierstrassCurve.VariableChange R)
    (h : curve.{u}.map φa = γ • curve.{u}.map φb) :
    FamilyIso (family.{u}.pullback (Spec.map (CommRingCat.ofHom φa)))
      (family.{u}.pullback (Spec.map (CommRingCat.ofHom φb))) :=
  ((familyOfMapIso curve.{u} φa).trans (familyOfEq h)).trans
    ((changeIso γ (curve.{u}.map φb)).trans (familyOfMapIso curve.{u} φb).symm)

/-- The relation `curve.map φa = γ • curve.map φb` persists after changing coefficients along
`ψ`. -/
theorem map_comp_eq_smul_map_comp {R' : Type u} [CommRing R'] {φa φb : baseRing.{u} →+* R}
    {γ : WeierstrassCurve.VariableChange R} (h : curve.{u}.map φa = γ • curve.{u}.map φb)
    (ψ : R →+* R') : curve.{u}.map (ψ.comp φa) = γ.map ψ • curve.{u}.map (ψ.comp φb) := by
  rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map, h,
    WeierstrassCurve.map_variableChange]

/-- **Base change of `ringIso` along a ring map.** Pulling back `ringIso φa φb γ h` along
`Spec R' ⟶ Spec R` for `ψ : R →+* R'`, read through the identifications of restrictions of
restrictions, is `ringIso (ψ.comp φa) (ψ.comp φb) (γ.map ψ)`. -/
theorem ringIso_pullback {R' : Type u} [CommRing R'] (φa φb : baseRing.{u} →+* R)
    (γ : WeierstrassCurve.VariableChange R) (h : curve.{u}.map φa = γ • curve.{u}.map φb)
    (ψ : R →+* R')
    (ha : Spec.map (CommRingCat.ofHom (ψ.comp φa)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φa))
    (hb : Spec.map (CommRingCat.ofHom (ψ.comp φb)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φb)) :
    (((family.{u}.pullbackPullbackIso _ _ ha).symm.trans
        ((ringIso φa φb γ h).pullback (Spec.map (CommRingCat.ofHom ψ)))).trans
          (family.{u}.pullbackPullbackIso _ _ hb)).iso.hom =
      (ringIso (ψ.comp φa) (ψ.comp φb) (γ.map ψ) (map_comp_eq_smul_map_comp h ψ)).iso.hom := by
  have k₁ : (family.{u}.pullbackPullbackIso _ _ ha).iso.inv ≫
      ((familyOfMapIso curve.{u} φa).pullback (Spec.map (CommRingCat.ofHom ψ))).iso.hom =
        (familyOfMapIso curve.{u} (ψ.comp φa)).iso.hom ≫
          (familyOfEq (curve.{u}.map_map φa ψ).symm).iso.hom ≫
            (familyOfMapIso (curve.{u}.map φa) ψ).iso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← familyOfMapIso_comp curve.{u} φa ψ ha]
    simp only [Category.assoc, familyOfEq_trans_assoc, familyOfEq_refl_hom, Category.id_comp,
      Iso.hom_inv_id, Category.comp_id]
  have k₂ : ((familyOfMapIso curve.{u} φb).pullback (Spec.map (CommRingCat.ofHom ψ))).iso.inv ≫
      (family.{u}.pullbackPullbackIso _ _ hb).iso.hom =
        (familyOfMapIso (curve.{u}.map φb) ψ).iso.hom ≫
          (familyOfEq (curve.{u}.map_map φb ψ)).iso.hom ≫
            (familyOfMapIso curve.{u} (ψ.comp φb)).iso.inv := by
    rw [Iso.inv_comp_eq]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv]
    simpa only [Category.assoc] using (familyOfMapIso_comp curve.{u} φb ψ hb).symm
  dsimp only [ringIso]
  simp only [FamilyIso.trans_pullback_iso_hom, FamilyIso.trans_iso, FamilyIso.symm_iso,
    FamilyIso.symm_pullback, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [k₂, reassoc_of% k₁, familyOfMapIso_familyOfEq_assoc,
    familyOfMapIso_changeIso_familyOfEq_assoc,
    ← familyOfEq_changeIso_assoc, familyOfEq_trans_assoc, familyOfEq_trans_assoc,
    familyOfEq_trans_assoc]

end RingIso

/-! ### The universal triple over `H × W` -/

section Universal

/-- The universal coordinate change over `H × W` carries the Weierstrass equation of the
projection `H × W ⟶ W` to that of the action `H × W ⟶ W`. -/
theorem curveAt_actionMap :
    curve.{u}.map (ringOf actionMap.{u}).hom =
      changeAt productToGroup.{u} • curve.{u}.map (ringOf productToBase.{u}).hom :=
  curveAt_act productToGroup productToBase

/-- **The universal triple over `H × W`.** The triple `(actionMap, productToBase, α)`, where `α`
is the pullback along `H × W ⟶ Spec Γ(H × W, ⊤)` of `ringIso` for the universal coordinate
change `changeAt productToGroup`. -/
def universalComparison : Comparison family.{u} family.{u} coordinateChangeProduct.{u} :=
  Comparison.ofFamilyIsoPullback
    (ringIso (ringOf actionMap.{u}).hom (ringOf productToBase.{u}).hom
      (changeAt productToGroup.{u}) curveAt_actionMap)
    coordinateChangeProduct.{u}.toSpecΓ (homOfRing_ringOf actionMap.{u}).symm
    (homOfRing_ringOf productToBase.{u}).symm

/-- The first morphism of the universal triple is the action `H × W ⟶ W`. -/
@[simp]
theorem universalComparison_fst : universalComparison.{u}.fst = actionMap.{u} :=
  rfl

/-- The second morphism of the universal triple is the projection `H × W ⟶ W`. -/
@[simp]
theorem universalComparison_snd : universalComparison.{u}.snd = productToBase.{u} :=
  rfl

/-- Pulling back `ringIso` along `Spec R' ⟶ Spec R` gives `ringIso` of the composite ring
maps. -/
theorem ofFamilyIsoPullback_ringIso {R R' : Type u} [CommRing R] [CommRing R']
    (φa φb : baseRing.{u} →+* R) (γ : WeierstrassCurve.VariableChange R)
    (h : curve.{u}.map φa = γ • curve.{u}.map φb) (ψ : R →+* R')
    {a b : Spec (CommRingCat.of R') ⟶ base.{u}}
    (ha : a = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φa))
    (hb : b = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φb)) :
    Comparison.ofFamilyIsoPullback (ringIso φa φb γ h) (Spec.map (CommRingCat.ofHom ψ)) ha hb =
      Comparison.ofFamilyIso _ _
        (ringIso (ψ.comp φa) (ψ.comp φb) (γ.map ψ) (map_comp_eq_smul_map_comp h ψ)) := by
  have hc (φ : baseRing.{u} →+* R) : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain rfl : a = _ := ha.trans (hc φa).symm
  obtain rfl : b = _ := hb.trans (hc φb).symm
  exact Comparison.ofFamilyIso_ext (ringIso_pullback φa φb γ h ψ ha hb)

/-- **The base change of the universal triple to an affine scheme.** For `g : Spec A ⟶ H × W`
with `ψ : Γ(H × W, ⊤) → A` the ring map of `g ≫ (H × W ⟶ Spec Γ(H × W, ⊤))`, the base change
of the universal triple along `g` is `ringIso` of the composites of `ψ` with the ring maps of
the two projections to `W`, for the coordinate change `(changeAt productToGroup).map ψ`. -/
theorem baseChange_universalComparison {A : CommRingCat.{u}}
    (g : Spec A ⟶ coordinateChangeProduct.{u}) :
    universalComparison.{u}.baseChange g =
      Comparison.ofFamilyIso _ _ (ringIso
        ((Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
          (ringOf actionMap.{u}).hom)
        ((Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
          (ringOf productToBase.{u}).hom)
        ((changeAt productToGroup.{u}).map
          (Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom)
        (map_comp_eq_smul_map_comp curveAt_actionMap _)) := by
  refine (Comparison.baseChange_ofFamilyIsoPullback _ _ _ _ g).trans ?_
  refine (Comparison.ofFamilyIsoPullback_congr_t _
    (Spec.map_preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).symm _ _).trans ?_
  exact ofFamilyIsoPullback_ringIso _ _ _ _ _ _ _

end Universal

/-! ### Triples over affine schemes -/

section Affine

/-- Ring maps with equal spectra are equal. -/
theorem ringHom_eq_of_SpecMap_eq {R S : Type u} [CommRing R] [CommRing S] {f f' : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom f')) : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The ring map of `Spec A ⟶ T ⟶ Spec Γ(T, ⊤)`, composed with the ring map of `q : T ⟶ Spec R`,
is the ring map of `g ≫ q`. -/
theorem SpecMap_preimage_comp_ringOf {A R : CommRingCat.{u}} {T : Scheme.{u}} (g : Spec A ⟶ T)
    (q : T ⟶ Spec R) :
    Spec.map (CommRingCat.ofHom ((Spec.preimage (g ≫ T.toSpecΓ)).hom.comp (ringOf q).hom)) =
      g ≫ q := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
    Spec.map_preimage, Category.assoc]
  exact congrArg (g ≫ ·) (homOfRing_ringOf q)

/-- The ring map of `Spec A ⟶ T ⟶ Spec Γ(T, ⊤)`, composed with the ring map of `q : T ⟶ Spec R`,
is `φ` as soon as `g ≫ q` is `Spec.map φ`. -/
private theorem preimage_comp_ringOf_eq {A R : CommRingCat.{u}} {T : Scheme.{u}} (g : Spec A ⟶ T)
    (q : T ⟶ Spec R) {φ : R →+* A} (h : g ≫ q = Spec.map (CommRingCat.ofHom φ)) :
    (Spec.preimage (g ≫ T.toSpecΓ)).hom.comp (ringOf q).hom = φ :=
  ringHom_eq_of_SpecMap_eq ((SpecMap_preimage_comp_ringOf g q).trans h)

/-- The triple `ofFamilyIso _ _ (ringIso φa φb γ h)` depends only on `φa`, `φb` and `γ`. -/
theorem ofFamilyIso_ringIso_congr {R : Type u} [CommRing R] {φa φa' φb φb' : baseRing.{u} →+* R}
    {γ γ' : WeierstrassCurve.VariableChange R} (h : curve.{u}.map φa = γ • curve.{u}.map φb)
    (h' : curve.{u}.map φa' = γ' • curve.{u}.map φb') (ea : φa = φa') (eb : φb = φb')
    (eγ : γ = γ') :
    Comparison.ofFamilyIso _ _ (ringIso φa φb γ h) =
      Comparison.ofFamilyIso _ _ (ringIso φa' φb' γ' h') := by
  subst ea eb eγ
  rfl

/-- Two triples `(a, b, α)` and `(a, b, β)` with the same morphisms to the bases are equal only if
`α = β`. -/
theorem iso_hom_eq_of_ofFamilyIso_eq {S S' T : Scheme.{u}} {E : PointedFamily S}
    {E' : PointedFamily S'} {a : T ⟶ S} {b : T ⟶ S'}
    {ρ σ : FamilyIso (E.pullback a) (E'.pullback b)}
    (h : Comparison.ofFamilyIso a b ρ = Comparison.ofFamilyIso a b σ) : ρ.iso.hom = σ.iso.hom :=
  (Category.comp_id _).symm.trans ((Comparison.iso_congr h).trans (Category.id_comp _))

variable {R : Type u} [CommRing R]

/-- The isomorphism of total spaces of `ringIso φa φb γ h`, as a composite. -/
theorem ringIso_iso_hom (φa φb : baseRing.{u} →+* R) (γ : WeierstrassCurve.VariableChange R)
    (h : curve.{u}.map φa = γ • curve.{u}.map φb) :
    (ringIso φa φb γ h).iso.hom = (familyOfMapIso curve.{u} φa).iso.hom ≫
      (familyOfEq h).iso.hom ≫ (changeIso γ (curve.{u}.map φb)).iso.hom ≫
        (familyOfMapIso curve.{u} φb).iso.inv := by
  simp only [ringIso, FamilyIso.trans_iso, FamilyIso.symm_iso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]

/-- An isomorphism `E_W ×_{W,φa} Spec R ≅ E_W ×_{W,φb} Spec R` is `ringIso φa φb γ h` as soon as
it is `changeIso γ` once both sides are identified with plane cubics by `familyOfMapIso`. -/
theorem iso_hom_eq_ringIso {φa φb : baseRing.{u} →+* R}
    (σ : FamilyIso (family.{u}.pullback (Spec.map (CommRingCat.ofHom φa)))
      (family.{u}.pullback (Spec.map (CommRingCat.ofHom φb))))
    (γ : WeierstrassCurve.VariableChange R) (h : curve.{u}.map φa = γ • curve.{u}.map φb)
    (hσ : (familyOfMapIso curve.{u} φa).iso.inv ≫ σ.iso.hom ≫
        (familyOfMapIso curve.{u} φb).iso.hom =
      (familyOfEq h).iso.hom ≫ (changeIso γ (curve.{u}.map φb)).iso.hom) :
    σ.iso.hom = (ringIso φa φb γ h).iso.hom := by
  rw [ringIso_iso_hom, ← reassoc_of% hσ]
  simp

end Affine

section Bijective

/-- Two ring maps out of the ring of `H` are equal when they carry the universal coordinate change
to the same coordinate change. -/
theorem ringHom_eq_of_universalChange_map_eq {R : Type u} [CommRing R]
    (φ φ' : coordinateChangeRing.{u} →+* R)
    (h : universalChange.{u}.map φ = universalChange.{u}.map φ') : φ = φ' :=
  (changeRingHom_eq_of_map φ _ h).trans (changeRingHom_eq_of_map φ' _ rfl).symm

/-- Every triple over an affine scheme `Spec A` is the base change of the universal triple. -/
theorem surjective_baseChange_universalComparison (A : CommRingCat.{u}) :
    Function.Surjective fun g : Spec A ⟶ coordinateChangeProduct.{u} =>
      universalComparison.{u}.baseChange g := by
  intro x
  obtain ⟨a, b, i, hi₁, hi₂⟩ := x
  obtain ⟨φa, rfl⟩ : ∃ φ : baseRing.{u} →+* A, Spec.map (CommRingCat.ofHom φ) = a :=
    ⟨(Spec.preimage a).hom, Spec.map_preimage a⟩
  obtain ⟨φb, rfl⟩ : ∃ φ : baseRing.{u} →+* A, Spec.map (CommRingCat.ofHom φ) = b :=
    ⟨(Spec.preimage b).hom, Spec.map_preimage b⟩
  let σ : FamilyIso (family.{u}.pullback (Spec.map (CommRingCat.ofHom φa)))
      (family.{u}.pullback (Spec.map (CommRingCat.ofHom φb))) := ⟨i, hi₁, hi₂⟩
  obtain ⟨γ, ⟨h₀, hγ⟩, -⟩ := exists_unique_variableChange (curve.{u}.map φb) (curve.{u}.map φa)
    (((familyOfMapIso curve.{u} φa).symm.trans σ).trans (familyOfMapIso curve.{u} φb))
  have h : curve.{u}.map φa = γ • curve.{u}.map φb := h₀.symm
  have hσ : (familyOfMapIso curve.{u} φa).iso.inv ≫ σ.iso.hom ≫
      (familyOfMapIso curve.{u} φb).iso.hom =
        (familyOfEq h).iso.hom ≫ (changeIso γ (curve.{u}.map φb)).iso.hom := by
    simp only [FamilyIso.trans_iso, FamilyIso.symm_iso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc] at hγ
    exact hγ
  let g : Spec A ⟶ coordinateChangeProduct.{u} :=
    productLift (Spec.map (CommRingCat.ofHom (changeRingHom γ))) (Spec.map (CommRingCat.ofHom φb))
  refine ⟨g, ?_⟩
  have eb : (Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf productToBase.{u}).hom = φb :=
    preimage_comp_ringOf_eq g productToBase (productLift_snd _ _)
  have eg : (Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf productToGroup.{u}).hom = changeRingHom γ :=
    preimage_comp_ringOf_eq g productToGroup (productLift_fst _ _)
  have eγ : (changeAt productToGroup.{u}).map
      (Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom = γ := by
    rw [changeAt, WeierstrassCurve.VariableChange.map_map, eg, universalChange_map_changeRingHom]
  have ea : (Spec.preimage (g ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf actionMap.{u}).hom = φa := by
    refine (baseRingHom_eq_of_curve_map _ (curve.{u}.map φa) ?_).trans
      (baseRingHom_eq_of_curve_map φa _ rfl).symm
    rw [map_comp_eq_smul_map_comp curveAt_actionMap, eγ, eb, h]
  refine (baseChange_universalComparison g).trans
    ((ofFamilyIso_ringIso_congr _ h ea eb eγ).trans ?_)
  exact Comparison.ofFamilyIso_ext (iso_hom_eq_ringIso σ γ h hσ).symm

/-- Distinct morphisms `Spec A ⟶ H × W` give distinct base changes of the universal triple. -/
theorem injective_baseChange_universalComparison (A : CommRingCat.{u}) :
    Function.Injective fun g : Spec A ⟶ coordinateChangeProduct.{u} =>
      universalComparison.{u}.baseChange g := by
  intro g₁ g₂ hg
  have hb : g₁ ≫ productToBase.{u} = g₂ ≫ productToBase.{u} := congrArg Comparison.snd hg
  have ha : g₁ ≫ actionMap.{u} = g₂ ≫ actionMap.{u} := congrArg Comparison.fst hg
  have hg' := (baseChange_universalComparison g₁).symm.trans
    (hg.trans (baseChange_universalComparison g₂))
  have eb : (Spec.preimage (g₁ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf productToBase.{u}).hom =
        (Spec.preimage (g₂ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
          (ringOf productToBase.{u}).hom :=
    preimage_comp_ringOf_eq _ _ (hb.trans (SpecMap_preimage_comp_ringOf _ _).symm)
  have ea : (Spec.preimage (g₁ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf actionMap.{u}).hom =
        (Spec.preimage (g₂ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
          (ringOf actionMap.{u}).hom :=
    preimage_comp_ringOf_eq _ _ (ha.trans (SpecMap_preimage_comp_ringOf _ _).symm)
  have h' := map_comp_eq_smul_map_comp curveAt_actionMap
    (Spec.preimage (g₂ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom
  rw [← ea, ← eb] at h'
  have key := iso_hom_eq_of_ofFamilyIso_eq
    (hg'.trans (ofFamilyIso_ringIso_congr _ h' ea.symm eb.symm rfl))
  rw [ringIso_iso_hom, ringIso_iso_hom, Iso.cancel_iso_hom_left,
    Iso.cancel_iso_inv_right_assoc] at key
  have eγ : (changeAt productToGroup.{u}).map
      (Spec.preimage (g₁ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom =
        (changeAt productToGroup.{u}).map
          (Spec.preimage (g₂ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom := by
    obtain ⟨γ, -, hγ⟩ := exists_unique_variableChange _ _
      ((familyOfEq (map_comp_eq_smul_map_comp curveAt_actionMap
        (Spec.preimage (g₁ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom)).trans
          (changeIso _ _))
    exact (hγ _ ⟨(map_comp_eq_smul_map_comp curveAt_actionMap _).symm, rfl⟩).trans
      (hγ _ ⟨h'.symm, key⟩).symm
  have eg : (Spec.preimage (g₁ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
      (ringOf productToGroup.{u}).hom =
        (Spec.preimage (g₂ ≫ coordinateChangeProduct.{u}.toSpecΓ)).hom.comp
          (ringOf productToGroup.{u}).hom := by
    refine (ringHom_eq_of_universalChange_map_eq _ _ ?_)
    exact eγ
  refine Limits.pullback.hom_ext ?_ hb
  rw [← SpecMap_preimage_comp_ringOf g₁ productToGroup,
    ← SpecMap_preimage_comp_ringOf g₂ productToGroup, eg]

/-- The base change of the universal triple to `Spec A` is a bijection from the `Spec A`-points of
`H × W` to the triples over `Spec A`. -/
theorem bijective_baseChange_universalComparison (A : CommRingCat.{u}) :
    Function.Bijective fun g : Spec A ⟶ coordinateChangeProduct.{u} =>
      universalComparison.{u}.baseChange g :=
  ⟨injective_baseChange_universalComparison A, surjective_baseChange_universalComparison A⟩

/-- **`H × W` is the fibre product `W ×_{𝓜₁,₁} W`**, the torsor property used in the proof of
Tag 072T. A `T`-point `g` of `H × W` classifies the base change along `g` of the universal triple
`(actionMap, productToBase, α)`, whose isomorphism `α` is induced by the universal coordinate
change. -/
def representsComparisons_coordinateChange :
    RepresentsComparisons family.{u} family.{u} coordinateChangeProduct.{u} :=
  representsComparisons_of_bijective_affine (fun _ g => universalComparison.{u}.baseChange g)
    (fun h g => by
      rw [Comparison.baseChange_comp]
      exact Comparison.isBaseChange_baseChange _ h)
    bijective_baseChange_universalComparison

/-- The triple classified by a `T`-point `g` of `H × W` is the base change of the universal
triple along `g`. -/
theorem representsComparisons_coordinateChange_homEquiv {T : Scheme.{u}}
    (g : T ⟶ coordinateChangeProduct.{u}) :
    representsComparisons_coordinateChange.{u}.homEquiv T g =
      universalComparison.{u}.baseChange g :=
  rfl

/-- The first projection of the universal triple of `W ×_{𝓜₁,₁} W = H × W` is the action. -/
@[simp]
theorem representsComparisons_coordinateChange_homEquiv_id_fst :
    (representsComparisons_coordinateChange.{u}.homEquiv _ (𝟙 _)).fst = actionMap.{u} :=
  Category.id_comp _

/-- The second projection of the universal triple of `W ×_{𝓜₁,₁} W = H × W` is the projection
to `W`. -/
@[simp]
theorem representsComparisons_coordinateChange_homEquiv_id_snd :
    (representsComparisons_coordinateChange.{u}.homEquiv _ (𝟙 _)).snd = productToBase.{u} :=
  Category.id_comp _

end Bijective

end Weierstrass

end AlgebraicGeometry.ModuliEllipticCurves

end
