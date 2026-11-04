module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesAlgebraic

/-!
# Transporting a fibre product over the moduli stack of elliptic curves

Let `F` be a pointed family over `W` and `F'` one over `W'`, and let `P` be a fibre product
`W ×_{𝓜₁,₁} W'` of the two morphisms they classify. This file transports `P` in two ways.

* Along isomorphisms of pointed families: a fibre product for `(F, F')` is one for any `(E, E')`
  with `E ≅ F` and `E' ≅ F'`.
* Along base change: for `c : S ⟶ W` and `c' : S' ⟶ W'`, the fibre product of the restricted
  families `F ×_{W,c} S` and `F' ×_{W',c'} S'` is the scheme `P ×_{W × W'} (S × S')`, because
  composing `S ⟶ W ⟶ 𝓜₁,₁` is restriction of the family along `c`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.FamilyIso.pullback` is the base change of an
  isomorphism of pointed families, and
  `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.pullbackPullbackIso` identifies a
  restriction of a restriction with a single restriction.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.pullbackScheme` is the scheme
  `P ×_{W × W'} (S × S')`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.ofFamilyIso`: a fibre product is
  invariant under isomorphisms of the two families.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.pullback`: the scheme
  `P ×_{W × W'} (S × S')` is a fibre product of the restricted families.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.ofComparisons`: the two combined,
  for families which are presented as restrictions of `F` and `F'` by triples.

## References

* [Stacks Project, Tag 072L](https://stacks.math.columbia.edu/tag/072L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

variable {S S' W W' P T U : Scheme.{u}}

attribute [local simp] Limits.pullback.lift_fst Limits.pullback.lift_snd
  Limits.pullback.lift_fst_assoc Limits.pullback.lift_snd_assoc

/-! ### Isomorphisms of pointed families -/

/-- The restriction of a pointed family along the identity of its base is the family itself. -/
def PointedFamily.pullbackIdIso (E : PointedFamily T) : FamilyIso (E.pullback (𝟙 T)) E where
  iso := asIso (Limits.pullback.fst E.map (𝟙 T))
  iso_map := by
    rw [asIso_hom, Limits.pullback.condition, Category.comp_id]
  zero_iso := by
    rw [asIso_hom, Limits.pullback.lift_fst, Category.id_comp]

namespace FamilyIso

/-- The identity isomorphism of a pointed family. -/
@[simps]
def refl (E : PointedFamily T) : FamilyIso E E where
  iso := Iso.refl _
  iso_map := Category.id_comp _
  zero_iso := Category.comp_id _

/-- The inverse of an isomorphism of pointed families. -/
@[simps]
def symm {E F : PointedFamily T} (e : FamilyIso E F) : FamilyIso F E where
  iso := e.iso.symm
  iso_map := by rw [Iso.symm_hom, Iso.inv_comp_eq, e.iso_map]
  zero_iso := by rw [Iso.symm_hom, Iso.comp_inv_eq, e.zero_iso]

/-- The composite of two isomorphisms of pointed families. -/
@[simps]
def trans {E F G : PointedFamily T} (e : FamilyIso E F) (f : FamilyIso F G) :
    FamilyIso E G where
  iso := e.iso ≪≫ f.iso
  iso_map := by rw [Iso.trans_hom, Category.assoc, f.iso_map, e.iso_map]
  zero_iso := by rw [Iso.trans_hom, ← Category.assoc, e.zero_iso, f.zero_iso]

/-- The inverse of the inverse of an isomorphism of pointed families is the isomorphism. -/
@[simp]
theorem symm_symm {E F : PointedFamily T} (e : FamilyIso E F) : e.symm.symm = e := rfl

/-- The base change `E ×_{T,a} U ≅ F ×_{T,a} U` of an isomorphism `E ≅ F` of pointed families
along `a : U ⟶ T`. -/
def pullback {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    FamilyIso (E.pullback a) (F.pullback a) where
  iso :=
    { hom := Limits.pullback.lift (Limits.pullback.fst E.map a ≫ e.iso.hom)
        (Limits.pullback.snd E.map a)
        (by rw [Category.assoc, e.iso_map, Limits.pullback.condition])
      inv := Limits.pullback.lift (Limits.pullback.fst F.map a ≫ e.iso.inv)
        (Limits.pullback.snd F.map a)
        (by rw [Category.assoc, ← e.iso_map, e.iso.inv_hom_id_assoc, Limits.pullback.condition])
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  iso_map := by simp
  zero_iso := by ext <;> simp [e.zero_iso]

/-- The base change of `e` along `a`, followed by the first projection, is the first projection
followed by `e`. -/
@[reassoc (attr := simp)]
theorem pullback_hom_fst {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    (e.pullback a).iso.hom ≫ Limits.pullback.fst F.map a =
      Limits.pullback.fst E.map a ≫ e.iso.hom := by
  simp [pullback]

/-- The base change of `e` along `a` commutes with the second projections to `U`. -/
@[reassoc (attr := simp)]
theorem pullback_hom_snd {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    (e.pullback a).iso.hom ≫ Limits.pullback.snd F.map a = Limits.pullback.snd E.map a := by
  simp [pullback]

/-- The inverse of the base change of `e` along `a`, followed by the first projection, is the first
projection followed by the inverse of `e`. -/
@[reassoc (attr := simp)]
theorem pullback_inv_fst {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    (e.pullback a).iso.inv ≫ Limits.pullback.fst E.map a =
      Limits.pullback.fst F.map a ≫ e.iso.inv := by
  simp [pullback]

/-- The inverse of the base change of `e` along `a` commutes with the second projections to `U`.
-/
@[reassoc (attr := simp)]
theorem pullback_inv_snd {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    (e.pullback a).iso.inv ≫ Limits.pullback.snd E.map a = Limits.pullback.snd F.map a := by
  simp [pullback]

/-- The base change of an isomorphism of pointed families commutes with the canonical morphisms
of the restricted families. -/
@[reassoc]
theorem pullbackMap_pullback_hom {E F : PointedFamily S} (e : FamilyIso E F) {a : T ⟶ S}
    {b : U ⟶ S} (h : U ⟶ T) (hb : b = h ≫ a) :
    E.pullbackMap h hb ≫ (e.pullback a).iso.hom = (e.pullback b).iso.hom ≫ F.pullbackMap h hb := by
  ext <;> simp [PointedFamily.pullbackMap]

/-- The inverse of the base change of an isomorphism commutes with the canonical morphisms of the
restricted families. -/
@[reassoc]
theorem pullbackMap_pullback_inv {E F : PointedFamily S} (e : FamilyIso E F) {a : T ⟶ S}
    {b : U ⟶ S} (h : U ⟶ T) (hb : b = h ≫ a) :
    F.pullbackMap h hb ≫ (e.pullback a).iso.inv = (e.pullback b).iso.inv ≫ E.pullbackMap h hb := by
  exact (CommSq.mk (pullbackMap_pullback_hom e h hb)).vert_inv.w

/-- Base change of an isomorphism and of its inverse are mutually inverse. -/
theorem symm_pullback {E F : PointedFamily T} (e : FamilyIso E F) (a : U ⟶ T) :
    (e.symm.pullback a).iso = (e.pullback a).iso.symm := by
  ext1
  rw [Iso.symm_hom]
  ext <;> simp [pullback, symm]

end FamilyIso

/-! ### Triples as isomorphisms of pointed families -/

namespace Comparison

variable {E : PointedFamily S} {E' : PointedFamily S'}

/-- The isomorphism `α` of a triple `(a, a', α)`, as an isomorphism of pointed families over the
test scheme. -/
@[simps]
def familyIso (x : Comparison E E' T) : FamilyIso (E.pullback x.fst) (E'.pullback x.snd) :=
  ⟨x.iso, x.iso_map, x.zero_iso⟩

/-- The triple `(a, a', α)` with `α` an isomorphism of pointed families. -/
@[simps]
def ofFamilyIso (a : T ⟶ S) (a' : T ⟶ S') (φ : FamilyIso (E.pullback a) (E'.pullback a')) :
    Comparison E E' T :=
  ⟨a, a', φ.iso, φ.iso_map, φ.zero_iso⟩

/-- Two triples with the same morphisms to the bases are equal when their isomorphisms are. -/
theorem ofFamilyIso_ext {a : T ⟶ S} {a' : T ⟶ S'} {φ ψ : FamilyIso (E.pullback a) (E'.pullback a')}
    (h : φ.iso.hom = ψ.iso.hom) : ofFamilyIso a a' φ = ofFamilyIso a a' ψ := by
  obtain ⟨φ, _, _⟩ := φ
  obtain ⟨ψ, _, _⟩ := ψ
  obtain rfl : φ = ψ := Iso.ext h
  rfl

end Comparison

/-! ### Invariance under isomorphisms of the families -/

section FamilyIso

variable {E₁ E₂ : PointedFamily S} {E₁' E₂' : PointedFamily S'}

/-- A triple for `(E₁, E₁')` gives one for `(E₂, E₂')`, along isomorphisms `E₁ ≅ E₂` and
`E₁' ≅ E₂'`. -/
@[simps!]
def Comparison.mapFamilyIso (e : FamilyIso E₁ E₂) (e' : FamilyIso E₁' E₂')
    (x : Comparison E₁ E₁' T) : Comparison E₂ E₂' T :=
  Comparison.ofFamilyIso x.fst x.snd
    (((e.pullback x.fst).symm.trans x.familyIso).trans (e'.pullback x.snd))

/-- Transporting a triple along `e` and `e'` and then along their inverses recovers the triple. -/
theorem Comparison.mapFamilyIso_symm_mapFamilyIso (e : FamilyIso E₁ E₂)
    (e' : FamilyIso E₁' E₂') (x : Comparison E₁ E₁' T) :
    (x.mapFamilyIso e e').mapFamilyIso e.symm e'.symm = x := by
  obtain ⟨a, a', i, h₁, h₂⟩ := x
  dsimp only [Comparison.mapFamilyIso, Comparison.ofFamilyIso, Comparison.familyIso,
    FamilyIso.trans_iso, FamilyIso.symm_iso]
  congr 1
  ext1
  simp [FamilyIso.symm_pullback]

/-- The triples for `(E₁, E₁')` and for `(E₂, E₂')` correspond, along isomorphisms `E₁ ≅ E₂` and
`E₁' ≅ E₂'`. -/
def Comparison.familyIsoEquiv (e : FamilyIso E₁ E₂) (e' : FamilyIso E₁' E₂') (T : Scheme.{u}) :
    Comparison E₁ E₁' T ≃ Comparison E₂ E₂' T where
  toFun := Comparison.mapFamilyIso e e'
  invFun := Comparison.mapFamilyIso e.symm e'.symm
  left_inv := Comparison.mapFamilyIso_symm_mapFamilyIso e e'
  right_inv x := by
    have h := Comparison.mapFamilyIso_symm_mapFamilyIso e.symm e'.symm x
    rwa [FamilyIso.symm_symm, FamilyIso.symm_symm] at h

/-- Transport along isomorphisms of the families preserves the base-change relation. -/
theorem Comparison.IsBaseChange.mapFamilyIso (e : FamilyIso E₁ E₂) (e' : FamilyIso E₁' E₂')
    {x : Comparison E₁ E₁' T} {h : U ⟶ T} {y : Comparison E₁ E₁' U} (hxy : x.IsBaseChange h y) :
    (x.mapFamilyIso e e').IsBaseChange h (y.mapFamilyIso e e') := by
  obtain ⟨hf, hs, hiso⟩ := hxy
  refine ⟨hf, hs, ?_⟩
  dsimp only [Comparison.mapFamilyIso, Comparison.ofFamilyIso, Comparison.familyIso,
    FamilyIso.trans, FamilyIso.symm, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← FamilyIso.pullbackMap_pullback_hom e' h hs, reassoc_of% hiso,
    ← FamilyIso.pullbackMap_pullback_inv_assoc e h hf]

/-- **A fibre product over `𝓜₁,₁` is invariant under isomorphisms of the families.** If `P`
is a fibre product for `(E₁, E₁')`, it is one for `(E₂, E₂')` whenever `E₁ ≅ E₂` and
`E₁' ≅ E₂'`. -/
def RepresentsComparisons.ofFamilyIso (r : RepresentsComparisons E₁ E₁' P)
    (e : FamilyIso E₁ E₂) (e' : FamilyIso E₁' E₂') : RepresentsComparisons E₂ E₂' P where
  homEquiv T := (r.homEquiv T).trans (Comparison.familyIsoEquiv e e' T)
  naturality h g := (r.naturality h g).mapFamilyIso e e'

end FamilyIso

/-! ### Restriction of a restriction -/

namespace PointedFamily

/-- The restriction `(F ×_{W,c} S) ×_{S,a} T` of a restriction is the restriction `F ×_{W,b} T`
along the composite `b = a ≫ c`. -/
def pullbackPullbackIso (F : PointedFamily W) (c : S ⟶ W) (a : T ⟶ S) {b : T ⟶ W}
    (hb : b = a ≫ c) : FamilyIso ((F.pullback c).pullback a) (F.pullback b) where
  iso :=
    { hom := Limits.pullback.lift
        (Limits.pullback.fst _ _ ≫ Limits.pullback.fst F.map c) (Limits.pullback.snd _ _)
        (by
          rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
            Limits.pullback.condition, Category.assoc, hb])
      inv := Limits.pullback.lift
        (Limits.pullback.lift (Limits.pullback.fst F.map b)
          (Limits.pullback.snd F.map b ≫ a)
          (by rw [Limits.pullback.condition, hb, Category.assoc]))
        (Limits.pullback.snd _ _) (by simp)
      hom_inv_id := by
        ext
        · simp
        · simp [Limits.pullback.condition]
        · simp
      inv_hom_id := by ext <;> simp }
  iso_map := by simp
  zero_iso := by ext <;> simp [hb]

/-- Followed by the first projection of `F ×_{W,b} T`, the isomorphism `pullbackPullbackIso` is the
composite of the first projections of `(F ×_{W,c} S) ×_{S,a} T` and of `F ×_{W,c} S`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIso_hom_fst (F : PointedFamily W) (c : S ⟶ W) (a : T ⟶ S) {b : T ⟶ W}
    (hb : b = a ≫ c) :
    (F.pullbackPullbackIso c a hb).iso.hom ≫ Limits.pullback.fst F.map b =
      Limits.pullback.fst _ _ ≫ Limits.pullback.fst F.map c := by
  simp [pullbackPullbackIso]

/-- The isomorphism `pullbackPullbackIso` commutes with the second projections to `T`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIso_hom_snd (F : PointedFamily W) (c : S ⟶ W) (a : T ⟶ S) {b : T ⟶ W}
    (hb : b = a ≫ c) :
    (F.pullbackPullbackIso c a hb).iso.hom ≫ Limits.pullback.snd F.map b =
      Limits.pullback.snd _ _ := by
  simp [pullbackPullbackIso]

/-- The identification of a restriction of a restriction with a single restriction commutes
with the canonical morphisms of the restricted families. -/
@[reassoc]
theorem pullbackMap_pullbackPullbackIso_hom (F : PointedFamily W) (c : S ⟶ W) {a : T ⟶ S}
    {a' : U ⟶ S} {b : T ⟶ W} {b' : U ⟶ W} (h : U ⟶ T) (ha : a' = h ≫ a) (hb : b = a ≫ c)
    (hb' : b' = a' ≫ c) (hbb : b' = h ≫ b) :
    (F.pullback c).pullbackMap h ha ≫ (F.pullbackPullbackIso c a hb).iso.hom =
      (F.pullbackPullbackIso c a' hb').iso.hom ≫ F.pullbackMap h hbb := by
  ext <;> simp [pullbackMap]

/-- The inverse form of `pullbackMap_pullbackPullbackIso_hom`. -/
@[reassoc]
theorem pullbackMap_pullbackPullbackIso_inv (F : PointedFamily W) (c : S ⟶ W) {a : T ⟶ S}
    {a' : U ⟶ S} {b : T ⟶ W} {b' : U ⟶ W} (h : U ⟶ T) (ha : a' = h ≫ a) (hb : b = a ≫ c)
    (hb' : b' = a' ≫ c) (hbb : b' = h ≫ b) :
    F.pullbackMap h hbb ≫ (F.pullbackPullbackIso c a hb).iso.inv =
      (F.pullbackPullbackIso c a' hb').iso.inv ≫ (F.pullback c).pullbackMap h ha := by
  exact (CommSq.mk (pullbackMap_pullbackPullbackIso_hom F c h ha hb hb' hbb)).vert_inv.w

end PointedFamily

/-! ### Base change of a fibre product -/

section BaseChange

variable {F : PointedFamily W} {F' : PointedFamily W'}

namespace Comparison

/-- A triple for the restricted families `(F ×_{W,c} S, F' ×_{W',c'} S')` from morphisms
`a : T ⟶ S`, `a' : T ⟶ S'` and a triple `y` for `(F, F')` lying over `(a ≫ c, a' ≫ c')`. -/
def ofRestrict (c : S ⟶ W) (c' : S' ⟶ W') (a : T ⟶ S) (a' : T ⟶ S') (y : Comparison F F' T)
    (h₁ : y.fst = a ≫ c) (h₂ : y.snd = a' ≫ c') :
    Comparison (F.pullback c) (F'.pullback c') T :=
  Comparison.ofFamilyIso a a'
    (((F.pullbackPullbackIso c a h₁).trans y.familyIso).trans
      (F'.pullbackPullbackIso c' a' h₂).symm)

/-- The triple for `(F, F')` underlying a triple for the restricted families. -/
def toRestrict (c : S ⟶ W) (c' : S' ⟶ W') (x : Comparison (F.pullback c) (F'.pullback c') T) :
    Comparison F F' T :=
  Comparison.ofFamilyIso (x.fst ≫ c) (x.snd ≫ c')
    (((F.pullbackPullbackIso c x.fst rfl).symm.trans x.familyIso).trans
      (F'.pullbackPullbackIso c' x.snd rfl))

/-- The triple `ofRestrict` depends only on the morphisms `a`, `a'` and the triple `y`, not on the
proofs that `y` lies over `(a ≫ c, a' ≫ c')`. -/
theorem ofRestrict_congr (c : S ⟶ W) (c' : S' ⟶ W') {a₁ a₂ : T ⟶ S} {a₁' a₂' : T ⟶ S'}
    {y₁ y₂ : Comparison F F' T} (h₁ : y₁.fst = a₁ ≫ c) (h₂ : y₁.snd = a₁' ≫ c')
    (k₁ : y₂.fst = a₂ ≫ c) (k₂ : y₂.snd = a₂' ≫ c') (ha : a₁ = a₂) (ha' : a₁' = a₂')
    (hy : y₁ = y₂) : ofRestrict c c' a₁ a₁' y₁ h₁ h₂ = ofRestrict c c' a₂ a₂' y₂ k₁ k₂ := by
  subst ha ha' hy
  rfl

/-- Restricting the underlying triple of a triple `x` for the restricted families recovers `x`. -/
theorem ofRestrict_toRestrict (c : S ⟶ W) (c' : S' ⟶ W')
    (x : Comparison (F.pullback c) (F'.pullback c') T) :
    ofRestrict c c' x.fst x.snd (toRestrict c c' x) rfl rfl = x := by
  change Comparison.ofFamilyIso x.fst x.snd _ = Comparison.ofFamilyIso x.fst x.snd x.familyIso
  refine Comparison.ofFamilyIso_ext ?_
  dsimp only [toRestrict, Comparison.ofFamilyIso, FamilyIso.trans_iso, FamilyIso.symm_iso,
    Comparison.familyIso_iso, Iso.trans_hom, Iso.symm_hom]
  simp

/-- The triple for `(F, F')` underlying the restriction of a triple `y` is `y`. -/
theorem toRestrict_ofRestrict (c : S ⟶ W) (c' : S' ⟶ W') (a : T ⟶ S) (a' : T ⟶ S')
    (y : Comparison F F' T) (h₁ : y.fst = a ≫ c) (h₂ : y.snd = a' ≫ c') :
    toRestrict c c' (ofRestrict c c' a a' y h₁ h₂) = y := by
  obtain ⟨b, b', i, hi₁, hi₂⟩ := y
  dsimp only at h₁ h₂
  subst h₁ h₂
  change Comparison.ofFamilyIso (a ≫ c) (a' ≫ c') _ =
      Comparison.ofFamilyIso (a ≫ c) (a' ≫ c') ⟨i, hi₁, hi₂⟩
  refine Comparison.ofFamilyIso_ext ?_
  dsimp only [ofRestrict, Comparison.ofFamilyIso, FamilyIso.trans_iso, FamilyIso.symm_iso,
    Comparison.familyIso_iso, Iso.trans_hom, Iso.symm_hom]
  simp

/-- Restricting triples preserves the base-change relation. -/
theorem IsBaseChange.ofRestrict (c : S ⟶ W) (c' : S' ⟶ W') {a : T ⟶ S} {a' : T ⟶ S'}
    {y : Comparison F F' T} (h₁ : y.fst = a ≫ c) (h₂ : y.snd = a' ≫ c') {h : U ⟶ T}
    {z : Comparison F F' U} (k₁ : z.fst = (h ≫ a) ≫ c) (k₂ : z.snd = (h ≫ a') ≫ c')
    (hyz : y.IsBaseChange h z) :
    (Comparison.ofRestrict c c' a a' y h₁ h₂).IsBaseChange h
      (Comparison.ofRestrict c c' (h ≫ a) (h ≫ a') z k₁ k₂) := by
  obtain ⟨hf, hs, hiso⟩ := hyz
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [Comparison.ofRestrict, Comparison.toRestrict, Comparison.ofFamilyIso,
    Comparison.familyIso, FamilyIso.trans, FamilyIso.symm, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← PointedFamily.pullbackMap_pullbackPullbackIso_inv F' c' h rfl h₂ k₂ hs, reassoc_of% hiso,
    PointedFamily.pullbackMap_pullbackPullbackIso_hom_assoc F c h rfl h₁ k₁ hf]

end Comparison

namespace RepresentsComparisons

variable (r : RepresentsComparisons F F' P) (c : S ⟶ W) (c' : S' ⟶ W')

/-- The scheme `P ×_{W × W'} (S × S')`, for a fibre product `P` of `(F, F')` and morphisms
`c : S ⟶ W`, `c' : S' ⟶ W'`. -/
abbrev pullbackScheme : Scheme.{u} :=
  Limits.pullback (prod.lift (r.homEquiv P (𝟙 P)).fst (r.homEquiv P (𝟙 P)).snd)
    (prod.map c c')

variable {r c c'}

/-- For a `T`-point `q` of `P ×_{W × W'} (S × S')`, the first morphism of the triple classified by
its image in `P` is the composite of its image in `S` with `c`. -/
theorem fst_homEquiv_pullbackFst (q : T ⟶ r.pullbackScheme c c') :
    (r.homEquiv T (q ≫ Limits.pullback.fst _ _)).fst =
      (q ≫ Limits.pullback.snd _ _ ≫ prod.fst) ≫ c := by
  have h := (Limits.pullback.condition (f := prod.lift (r.homEquiv P (𝟙 P)).fst
    (r.homEquiv P (𝟙 P)).snd) (g := prod.map c c')) =≫ prod.fst
  simp only [Category.assoc, prod.lift_fst, prod.map_fst] at h
  rw [r.fst_homEquiv, Category.assoc, h, Category.assoc, Category.assoc]

/-- For a `T`-point `q` of `P ×_{W × W'} (S × S')`, the second morphism of the triple classified by
its image in `P` is the composite of its image in `S'` with `c'`. -/
theorem snd_homEquiv_pullbackFst (q : T ⟶ r.pullbackScheme c c') :
    (r.homEquiv T (q ≫ Limits.pullback.fst _ _)).snd =
      (q ≫ Limits.pullback.snd _ _ ≫ prod.snd) ≫ c' := by
  have h := (Limits.pullback.condition (f := prod.lift (r.homEquiv P (𝟙 P)).fst
    (r.homEquiv P (𝟙 P)).snd) (g := prod.map c c')) =≫ prod.snd
  simp only [Category.assoc, prod.lift_snd, prod.map_snd] at h
  rw [r.snd_homEquiv, Category.assoc, h, Category.assoc, Category.assoc]

variable (r c c')

/-- The triple for the restricted families classified by a `T`-point of
`P ×_{W × W'} (S × S')`. -/
def toComparison (q : T ⟶ r.pullbackScheme c c') :
    Comparison (F.pullback c) (F'.pullback c') T :=
  Comparison.ofRestrict c c' (q ≫ Limits.pullback.snd _ _ ≫ prod.fst)
    (q ≫ Limits.pullback.snd _ _ ≫ prod.snd) (r.homEquiv T (q ≫ Limits.pullback.fst _ _))
    (fst_homEquiv_pullbackFst q) (snd_homEquiv_pullbackFst q)

/-- The `T`-point of `P ×_{W × W'} (S × S')` classifying a triple for the restricted families. -/
def ofComparison (x : Comparison (F.pullback c) (F'.pullback c') T) :
    T ⟶ r.pullbackScheme c c' :=
  Limits.pullback.lift ((r.homEquiv T).symm (Comparison.toRestrict c c' x))
    (prod.lift x.fst x.snd) (by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, prod.lift_fst, ← r.fst_homEquiv, Equiv.apply_symm_apply,
          Category.assoc, prod.map_fst, prod.lift_fst_assoc]
        rfl
      · rw [Category.assoc, prod.lift_snd, ← r.snd_homEquiv, Equiv.apply_symm_apply,
          Category.assoc, prod.map_snd, prod.lift_snd_assoc]
        rfl)

/-- The `T`-point classifying the triple of a `T`-point `q` of `P ×_{W × W'} (S × S')` is `q`. -/
theorem ofComparison_toComparison (q : T ⟶ r.pullbackScheme c c') :
    r.ofComparison c c' (r.toComparison c c' q) = q := by
  refine Limits.pullback.hom_ext ?_ (prod.hom_ext ?_ ?_)
  · rw [ofComparison, Limits.pullback.lift_fst, Equiv.symm_apply_eq, toComparison,
      Comparison.toRestrict_ofRestrict]
  · simp [ofComparison, toComparison, Comparison.ofRestrict]
  · simp [ofComparison, toComparison, Comparison.ofRestrict]

/-- The triple classified by the `T`-point of `P ×_{W × W'} (S × S')` of a triple `x` for the
restricted families is `x`. -/
theorem toComparison_ofComparison (x : Comparison (F.pullback c) (F'.pullback c') T) :
    r.toComparison c c' (r.ofComparison c c' x) = x := by
  conv_rhs => rw [← Comparison.ofRestrict_toRestrict c c' x]
  refine Comparison.ofRestrict_congr c c' _ _ _ _ ?_ ?_ ?_
  · simp [ofComparison]
  · simp [ofComparison]
  · rw [ofComparison, Limits.pullback.lift_fst, Equiv.apply_symm_apply]

/-- **Base change of a fibre product over `𝓜₁,₁`.** If `P` is a fibre product `W ×_{𝓜₁,₁} W'`
for the families `F` and `F'`, then for morphisms `c : S ⟶ W` and `c' : S' ⟶ W'` the scheme
`P ×_{W × W'} (S × S')` is a fibre product for the restricted families `F ×_{W,c} S` and
`F' ×_{W',c'} S'`. -/
def pullback : RepresentsComparisons (F.pullback c) (F'.pullback c') (r.pullbackScheme c c') where
  homEquiv T :=
    { toFun := r.toComparison c c'
      invFun := r.ofComparison c c'
      left_inv := r.ofComparison_toComparison c c'
      right_inv := r.toComparison_ofComparison c c' }
  naturality {T U} h q := by
    change (r.toComparison c c' q).IsBaseChange h (r.toComparison c c' (h ≫ q))
    have k₁ : (r.homEquiv U ((h ≫ q) ≫ Limits.pullback.fst _ _)).fst =
        (h ≫ q ≫ Limits.pullback.snd _ _ ≫ prod.fst) ≫ c := by
      rw [fst_homEquiv_pullbackFst]; simp only [Category.assoc]
    have k₂ : (r.homEquiv U ((h ≫ q) ≫ Limits.pullback.fst _ _)).snd =
        (h ≫ q ≫ Limits.pullback.snd _ _ ≫ prod.snd) ≫ c' := by
      rw [snd_homEquiv_pullbackFst]; simp only [Category.assoc]
    have hnat := r.naturality h (q ≫ Limits.pullback.fst _ _)
    rw [← Category.assoc h q] at hnat
    have key := Comparison.IsBaseChange.ofRestrict c c' (fst_homEquiv_pullbackFst q)
      (snd_homEquiv_pullbackFst q) (h := h) k₁ k₂ hnat
    have e : r.toComparison c c' (h ≫ q) = Comparison.ofRestrict c c'
        (h ≫ q ≫ Limits.pullback.snd _ _ ≫ prod.fst) (h ≫ q ≫ Limits.pullback.snd _ _ ≫ prod.snd)
        (r.homEquiv U ((h ≫ q) ≫ Limits.pullback.fst _ _)) k₁ k₂ :=
      Comparison.ofRestrict_congr c c' _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _) rfl
    exact (congrArg (fun z => (r.toComparison c c' q).IsBaseChange h z) e).mpr key

end RepresentsComparisons

/-- The isomorphism of pointed families carried by a triple `(a, a', α)` for `(F, E)` whose second
morphism is `b`: the family `F ×_{W,a} T` is isomorphic to `E ×_{S,b} T`. -/
def Comparison.familyIsoOfSnd {E : PointedFamily S} (x : Comparison F E T) {b : T ⟶ S}
    (hx : x.snd = b) : FamilyIso (F.pullback x.fst) (E.pullback b) where
  iso := x.iso ≪≫ E.pullbackIsoOfEq hx
  iso_map := by
    rw [Iso.trans_hom, Category.assoc, PointedFamily.pullbackIsoOfEq_hom_map, x.iso_map]
  zero_iso := by
    rw [Iso.trans_hom, ← Category.assoc, x.zero_iso, PointedFamily.zero_pullbackIsoOfEq_hom]

/-- **A fibre product over `𝓜₁,₁` of two families presented by restrictions.** If `P` is a fibre
product for `(F, F')` and the families `E ×_{S,b} T` and `E' ×_{S',b'} T'` are restrictions of `F`
and `F'`, as witnessed by triples `x` and `x'` whose second morphisms are `b` and `b'`, then the
scheme `P ×_{W × W'} (T × T')` is a fibre product for `(E ×_{S,b} T, E' ×_{S',b'} T')`. -/
def RepresentsComparisons.ofComparisons {E : PointedFamily S} {E' : PointedFamily S'}
    (r : RepresentsComparisons F F' P) {T' : Scheme.{u}} (x : Comparison F E T)
    (x' : Comparison F' E' T') {b : T ⟶ S} {b' : T' ⟶ S'} (hx : x.snd = b) (hx' : x'.snd = b') :
    RepresentsComparisons (E.pullback b) (E'.pullback b') (r.pullbackScheme x.fst x'.fst) :=
  (r.pullback x.fst x'.fst).ofFamilyIso (x.familyIsoOfSnd hx) (x'.familyIsoOfSnd hx')

end BaseChange

end AlgebraicGeometry.ModuliEllipticCurves

end
