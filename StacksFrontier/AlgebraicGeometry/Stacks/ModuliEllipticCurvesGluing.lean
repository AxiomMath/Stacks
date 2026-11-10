module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesBaseChange

/-!
# The fibre product over `𝓜₁,₁` is Zariski local on the two bases

Let `E` be a pointed family over `S` and `E'` one over `S'`. The triples `(a, a', α)` of Tag 072L
form a functor `Sch^{opp} → Sets`, whose action on a morphism `h : U ⟶ T` of test schemes is
base change of the triple along `h`. This file proves that this functor is a sheaf for the
Zariski topology, and that it is representable as soon as it is representable after restricting
`E` and `E'` to the members of open covers of `S` and of `S'`: a fibre product
`S ×_{𝓜₁,₁} S'` is glued from the fibre products `Uᵢ ×_{𝓜₁,₁} U'ⱼ` of the restrictions.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.baseChangeHom` is the base change along
  a morphism of test schemes of a morphism of pulled-back families.
* `AlgebraicGeometry.ModuliEllipticCurves.Comparison.baseChange` is the base change of a triple.
* `AlgebraicGeometry.ModuliEllipticCurves.comparisonFunctor` is the functor of triples.
* `AlgebraicGeometry.ModuliEllipticCurves.restrictChart` is the morphism from the functor of
  points of a fibre product of the restricted families `(E|_U, E'|_{U'})` to the functor of
  triples of `(E, E')`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Comparison.IsBaseChange.eq_baseChange`: a triple which
  is a base change of `x` along `h` in the sense of `Comparison.IsBaseChange` is
  `x.baseChange h`.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.representableBy` and
  `AlgebraicGeometry.ModuliEllipticCurves.representsComparisonsOfRepresentableBy`: a fibre
  product `S ×_{𝓜₁,₁} S'` is the same thing as a representing object of the functor of triples.
* `AlgebraicGeometry.ModuliEllipticCurves.comparisonFunctor_isSheaf`: the functor of triples is
  a Zariski sheaf.
* `AlgebraicGeometry.ModuliEllipticCurves.representsComparisons_of_bijective_affine`: a natural
  family of maps from points of `P` to triples which is bijective on affine schemes makes `P` a
  fibre product.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.uniqueIso`: fibre products are
  unique up to an isomorphism compatible with the two projections.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.restrictSnd`: restricting the
  second family to an open `U` of its base restricts the fibre product to the preimage of `U`.
* `AlgebraicGeometry.ModuliEllipticCurves.isOpenImmersion_restrictChart`: the triples of
  restricted families form an open subfunctor of the triples.
* `AlgebraicGeometry.ModuliEllipticCurves.exists_representsComparisons_of_openCover`: the fibre
  product exists as soon as it exists over the members of open covers of the two bases.

## Implementation notes

The sheaf property is proved on the open covers of a test scheme `T`. A compatible family of
triples over the members `Uᵢ ⟶ T` of a cover glues to morphisms `a : T ⟶ S` and `a' : T ⟶ S'`,
and the isomorphisms of pulled-back families glue along the open cover of `E ×_{S,a} T` by the
pulled-back families `E ×_{S,aᵢ} Uᵢ`, which is
`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.pullbackCover`; its members are the
canonical morphisms `PointedFamily.pullbackMap`, so the compatibility of the local morphisms on
the overlaps is read off from `Comparison.IsBaseChange` directly.

Representability is then Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
(Stacks 01JJ) applied to the charts `restrictChart`, one for each pair of members of the two
covers. A chart is an open immersion of presheaves because its pullback along a triple `x` over
`T` is represented by the open of `T` over which both morphisms of `x` land in the given opens of
the bases; the passage between triples of the restricted families and triples of `(E, E')` is
`Comparison.toRestrict` and `Comparison.ofRestrict`.

## References

* [Stacks Project, Tag 072L](https://stacks.math.columbia.edu/tag/072L)
* [Stacks Project, Tag 072M](https://stacks.math.columbia.edu/tag/072M)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

attribute [reassoc (attr := simp)] PointedFamily.pullbackMap_fst PointedFamily.pullbackMap_snd

attribute [local simp] Limits.pullback.lift_fst Limits.pullback.lift_snd
  Limits.pullback.lift_fst_assoc Limits.pullback.lift_snd_assoc

namespace PointedFamily

variable {S S' S'' T U V : Scheme.{u}}

/-- The canonical morphisms of pulled-back families compose. -/
@[reassoc]
theorem pullbackMap_comp (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S} {c : V ⟶ S}
    (h : U ⟶ T) (k : V ⟶ U) (hb : b = h ≫ a) (hc : c = k ≫ b) :
    E.pullbackMap k hc ≫ E.pullbackMap h hb =
      E.pullbackMap (k ≫ h) (by rw [hc, hb, Category.assoc]) := by
  refine Limits.pullback.hom_ext ?_ ?_ <;> simp

/-- The canonical morphism of pulled-back families depends only on the morphism of test schemes,
not on the way it is written. -/
theorem pullbackMap_congr (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S} {h h' : U ⟶ T}
    (hh : h = h') (hb : b = h ≫ a) (hb' : b = h' ≫ a) :
    E.pullbackMap h hb = E.pullbackMap h' hb' := by
  subst hh; rfl

/-- The canonical morphism of pulled-back families carries the section to the section. -/
@[reassoc]
theorem zero_pullbackMap (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S} (h : U ⟶ T)
    (hb : b = h ≫ a) : (E.pullback b).zero ≫ E.pullbackMap h hb = h ≫ (E.pullback a).zero := by
  subst hb
  refine Limits.pullback.hom_ext ?_ ?_ <;> simp

/-- The square formed by the canonical morphism of pulled-back families over `h : U ⟶ T` is
cartesian. -/
theorem isPullback_pullbackMap (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S} (h : U ⟶ T)
    (hb : b = h ≫ a) :
    IsPullback (E.pullbackMap h hb) (E.pullback b).map (E.pullback a).map h := by
  subst hb
  refine IsPullback.of_right ?_ (E.pullbackMap_snd h rfl) (IsPullback.of_hasPullback E.map a)
  rw [pullbackMap_fst]
  exact IsPullback.of_hasPullback E.map (h ≫ a)

/-- Base change along an open immersion of test schemes is an open immersion of pulled-back
families. -/
instance isOpenImmersion_pullbackMap (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S}
    (h : U ⟶ T) [IsOpenImmersion h] (hb : b = h ≫ a) : IsOpenImmersion (E.pullbackMap h hb) :=
  MorphismProperty.of_isPullback (E.isPullback_pullbackMap h hb).flip ‹_›

/-! ### Base change of a morphism of pulled-back families -/

/-- The base change along `h : U ⟶ T` of a morphism `φ : E ×_{S,a} T ⟶ E' ×_{S',a'} T` of
pulled-back families over `T`. -/
def baseChangeHom (E : PointedFamily S) (E' : PointedFamily S') {a : T ⟶ S} {a' : T ⟶ S'}
    (φ : (E.pullback a).total ⟶ (E'.pullback a').total)
    (hφ : φ ≫ (E'.pullback a').map = (E.pullback a).map) (h : U ⟶ T) {b : U ⟶ S}
    {b' : U ⟶ S'} (hb : b = h ≫ a) (hb' : b' = h ≫ a') :
    (E.pullback b).total ⟶ (E'.pullback b').total :=
  Limits.pullback.lift (E.pullbackMap h hb ≫ φ ≫ Limits.pullback.fst E'.map a')
    (Limits.pullback.snd E.map b) (by
      have hφ' : φ ≫ Limits.pullback.snd E'.map a' = Limits.pullback.snd E.map a := hφ
      rw [Category.assoc, Category.assoc, Limits.pullback.condition, reassoc_of% hφ',
        pullbackMap_snd_assoc, hb'])

variable (E : PointedFamily S) (E' : PointedFamily S') (E'' : PointedFamily S'')
  {a : T ⟶ S} {a' : T ⟶ S'} {a'' : T ⟶ S''}
  (φ : (E.pullback a).total ⟶ (E'.pullback a').total)
  (hφ : φ ≫ (E'.pullback a').map = (E.pullback a).map) (h : U ⟶ T) {b : U ⟶ S}
  {b' : U ⟶ S'} {b'' : U ⟶ S''} (hb : b = h ≫ a) (hb' : b' = h ≫ a') (hb'' : b'' = h ≫ a'')

/-- The base change of a morphism of pulled-back families commutes with the second projections
to `U`. -/
@[reassoc (attr := simp)]
theorem baseChangeHom_snd :
    baseChangeHom E E' φ hφ h hb hb' ≫ Limits.pullback.snd E'.map b' =
      Limits.pullback.snd E.map b :=
  Limits.pullback.lift_snd _ _ _

/-- The base change of a morphism of pulled-back families is a morphism over `U`. -/
theorem baseChangeHom_map :
    baseChangeHom E E' φ hφ h hb hb' ≫ (E'.pullback b').map = (E.pullback b).map :=
  baseChangeHom_snd E E' φ hφ h hb hb'

/-- The base change of `φ` along `h` lies over `φ`: the square formed with the canonical
morphisms of pulled-back families commutes. -/
@[reassoc (attr := simp)]
theorem baseChangeHom_pullbackMap :
    baseChangeHom E E' φ hφ h hb hb' ≫ E'.pullbackMap h hb' = E.pullbackMap h hb ≫ φ := by
  have hφ' : φ ≫ Limits.pullback.snd E'.map a' = Limits.pullback.snd E.map a := hφ
  refine Limits.pullback.hom_ext ?_ ?_
  · simp [baseChangeHom]
  · simp only [Category.assoc, pullbackMap_snd, hφ']
    rw [← Category.assoc]
    exact congrArg (· ≫ h) (Limits.pullback.lift_snd _ _ _)

/-- A morphism over `U` lying over `φ` is the base change of `φ`. -/
theorem eq_baseChangeHom (ψ : (E.pullback b).total ⟶ (E'.pullback b').total)
    (hψ : ψ ≫ (E'.pullback b').map = (E.pullback b).map)
    (hψ' : ψ ≫ E'.pullbackMap h hb' = E.pullbackMap h hb ≫ φ) :
    ψ = baseChangeHom E E' φ hφ h hb hb' := by
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [← E'.pullbackMap_fst h hb', reassoc_of% hψ']
    simp [baseChangeHom]
  · exact hψ.trans (baseChangeHom_map E E' φ hφ h hb hb').symm

/-- The base change of a morphism carrying the section to the section carries the section to the
section. -/
theorem zero_baseChangeHom (hz : (E.pullback a).zero ≫ φ = (E'.pullback a').zero) :
    (E.pullback b).zero ≫ baseChangeHom E E' φ hφ h hb hb' = (E'.pullback b').zero := by
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ← E'.pullbackMap_fst h hb', baseChangeHom_pullbackMap_assoc,
      zero_pullbackMap_assoc, reassoc_of% hz, ← zero_pullbackMap_assoc E' h hb', pullbackMap_fst]
  · simp

/-- Base change of morphisms of pulled-back families is compatible with composition. -/
theorem baseChangeHom_comp (ψ : (E'.pullback a').total ⟶ (E''.pullback a'').total)
    (hψ : ψ ≫ (E''.pullback a'').map = (E'.pullback a').map) :
    baseChangeHom E E'' (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) h hb hb'' =
      baseChangeHom E E' φ hφ h hb hb' ≫ baseChangeHom E' E'' ψ hψ h hb' hb'' :=
  (eq_baseChangeHom _ _ _ _ _ _ _ _ (by simp) (by simp)).symm

/-- Base change of the identity is the identity. -/
theorem baseChangeHom_id :
    baseChangeHom E E (𝟙 _) (Category.id_comp _) h hb hb = 𝟙 (E.pullback b).total :=
  (eq_baseChangeHom _ _ _ _ _ _ _ _ (Category.id_comp _) (by simp)).symm

/-- Base change of a morphism equal to the identity is the identity. -/
theorem baseChangeHom_of_eq_id {ψ : (E.pullback a).total ⟶ (E.pullback a).total}
    (hψ : ψ ≫ (E.pullback a).map = (E.pullback a).map) (h1 : ψ = 𝟙 _) :
    baseChangeHom E E ψ hψ h hb hb = 𝟙 (E.pullback b).total := by
  subst h1
  exact baseChangeHom_id E h hb

end PointedFamily

/-! ### Base change of a triple -/

namespace Comparison

variable {S S' T U V : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- The inverse isomorphism of a triple is a morphism over the test scheme. -/
theorem iso_inv_map (x : Comparison E E' T) :
    x.iso.inv ≫ (E.pullback x.fst).map = (E'.pullback x.snd).map := by
  rw [← x.iso_map, Iso.inv_hom_id_assoc]

/-- The base change of a triple `(a, a', α)` over `T` along `h : U ⟶ T`: the triple
`(h ≫ a, h ≫ a', α ×_T U)`. It is reducible so that its two morphisms to the bases are
syntactically the composites wherever the pulled-back families are compared. -/
@[reducible] def baseChange (x : Comparison E E' T) (h : U ⟶ T) : Comparison E E' U where
  fst := h ≫ x.fst
  snd := h ≫ x.snd
  iso :=
    { hom := PointedFamily.baseChangeHom E E' x.iso.hom x.iso_map h rfl rfl
      inv := PointedFamily.baseChangeHom E' E x.iso.inv x.iso_inv_map h rfl rfl
      hom_inv_id := by
        rw [← PointedFamily.baseChangeHom_comp E E' E x.iso.hom x.iso_map h rfl rfl rfl
          x.iso.inv x.iso_inv_map]
        exact PointedFamily.baseChangeHom_of_eq_id E h rfl _ x.iso.hom_inv_id
      inv_hom_id := by
        rw [← PointedFamily.baseChangeHom_comp E' E E' x.iso.inv x.iso_inv_map h rfl rfl rfl
          x.iso.hom x.iso_map]
        exact PointedFamily.baseChangeHom_of_eq_id E' h rfl _ x.iso.inv_hom_id }
  iso_map := PointedFamily.baseChangeHom_map E E' x.iso.hom x.iso_map h rfl rfl
  zero_iso := PointedFamily.zero_baseChangeHom E E' x.iso.hom x.iso_map h rfl rfl x.zero_iso

/-- The first morphism of the base change of a triple along `h` is `h ≫ x.fst`. -/
@[simp]
theorem baseChange_fst (x : Comparison E E' T) (h : U ⟶ T) : (x.baseChange h).fst = h ≫ x.fst :=
  rfl

/-- The second morphism of the base change of a triple along `h` is `h ≫ x.snd`. -/
@[simp]
theorem baseChange_snd (x : Comparison E E' T) (h : U ⟶ T) : (x.baseChange h).snd = h ≫ x.snd :=
  rfl

/-- The base change of a triple is a base change in the sense of `Comparison.IsBaseChange`. -/
theorem isBaseChange_baseChange (x : Comparison E E' T) (h : U ⟶ T) :
    x.IsBaseChange h (x.baseChange h) :=
  ⟨rfl, rfl, PointedFamily.baseChangeHom_pullbackMap E E' x.iso.hom x.iso_map h rfl rfl⟩

/-- A triple which is a base change of `x` along `h` is `x.baseChange h`. -/
theorem IsBaseChange.eq_baseChange {x : Comparison E E' T} {h : U ⟶ T}
    {y : Comparison E E' U} (hy : x.IsBaseChange h y) : y = x.baseChange h := by
  obtain ⟨b, b', i, hi₁, hi₂⟩ := y
  obtain ⟨hfst, hsnd, hiso⟩ := hy
  dsimp only at hfst hsnd hiso
  subst hfst hsnd
  obtain rfl : i = (x.baseChange h).iso :=
    Iso.ext (PointedFamily.eq_baseChangeHom E E' x.iso.hom x.iso_map h rfl rfl i.hom hi₁ hiso)
  rfl

/-- Base change of triples is unique. -/
theorem IsBaseChange.unique {x : Comparison E E' T} {h : U ⟶ T} {y z : Comparison E E' U}
    (hy : x.IsBaseChange h y) (hz : x.IsBaseChange h z) : y = z :=
  hy.eq_baseChange.trans hz.eq_baseChange.symm

/-- Base changes of triples compose. -/
theorem IsBaseChange.trans {x : Comparison E E' T} {h : U ⟶ T} {y : Comparison E E' U}
    {k : V ⟶ U} {z : Comparison E E' V} (hy : x.IsBaseChange h y) (hz : y.IsBaseChange k z) :
    x.IsBaseChange (k ≫ h) z := by
  obtain ⟨hfst, hsnd, hiso⟩ := hy
  obtain ⟨hfst', hsnd', hiso'⟩ := hz
  refine ⟨by rw [hfst', hfst, Category.assoc], by rw [hsnd', hsnd, Category.assoc], ?_⟩
  rw [← PointedFamily.pullbackMap_comp E' h k hsnd hsnd', reassoc_of% hiso', hiso,
    PointedFamily.pullbackMap_comp_assoc]

/-- The base change of a triple along the identity is the triple itself. -/
@[simp]
theorem baseChange_id (x : Comparison E E' T) : x.baseChange (𝟙 T) = x :=
  (isBaseChange_id x).eq_baseChange.symm

/-- Base change of triples along a composite is the iterated base change. -/
theorem baseChange_comp (x : Comparison E E' T) (h : U ⟶ T) (k : V ⟶ U) :
    x.baseChange (k ≫ h) = (x.baseChange h).baseChange k :=
  (((isBaseChange_baseChange x h).trans
    (isBaseChange_baseChange _ k))).eq_baseChange.symm

end Comparison

/-! ### Morphisms out of a pulled-back family glue along an open cover of the test scheme -/

namespace PointedFamily

variable {S T Z : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S} (𝒰 : T.OpenCover)
  {b : ∀ i, 𝒰.X i ⟶ S} (hb : ∀ i, b i = 𝒰.f i ≫ a)

/-- The open cover of `E ×_{S,a} T` by the pulled-back families `E ×_{S,bᵢ} Uᵢ` over the members
`Uᵢ ⟶ T` of an open cover of `T`. -/
def pullbackCover : (E.pullback a).total.OpenCover :=
  Scheme.Cover.mkOfCovers 𝒰.I₀ (fun i => (E.pullback (b i)).total)
    (fun i => E.pullbackMap (𝒰.f i) (hb i)) (fun z => by
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (Limits.pullback.snd E.map a z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := Limits.pullback.snd E.map a) (g := 𝒰.f i) z y hy.symm
      refine ⟨i, (E.isPullback_pullbackMap (𝒰.f i) (hb i)).isoPullback.inv w, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw])

/-- The `i`-th member of `PointedFamily.pullbackCover` is `E ×_{S,bᵢ} Uᵢ`. -/
@[simp]
theorem pullbackCover_X (i : 𝒰.I₀) : (E.pullbackCover 𝒰 hb).X i = (E.pullback (b i)).total :=
  rfl

/-- The `i`-th morphism of `PointedFamily.pullbackCover` is the canonical morphism of pulled-back
families over `Uᵢ ⟶ T`. -/
@[simp]
theorem pullbackCover_f (i : 𝒰.I₀) :
    (E.pullbackCover 𝒰 hb).f i = E.pullbackMap (𝒰.f i) (hb i) :=
  rfl

/-- Two morphisms out of `E ×_{S,a} T` agree as soon as they agree on the pulled-back families
over the members of an open cover of `T`. -/
theorem hom_ext_of_cover {g₁ g₂ : (E.pullback a).total ⟶ Z}
    (h : ∀ i, E.pullbackMap (𝒰.f i) (hb i) ≫ g₁ = E.pullbackMap (𝒰.f i) (hb i) ≫ g₂) :
    g₁ = g₂ :=
  Scheme.Cover.hom_ext (E.pullbackCover 𝒰 hb) _ _ h

/-- The compatibility condition for glueing morphisms out of pulled-back families: on every test
scheme mapping to two members of the cover compatibly, the two restrictions agree. -/
def CoverCompatible (g : ∀ i, (E.pullback (b i)).total ⟶ Z) : Prop :=
  ∀ (i j : 𝒰.I₀) (Y : Scheme.{u}) (p : Y ⟶ 𝒰.X i) (q : Y ⟶ 𝒰.X j) (c : Y ⟶ S)
    (hp : c = p ≫ b i) (hq : c = q ≫ b j), p ≫ 𝒰.f i = q ≫ 𝒰.f j →
      E.pullbackMap p hp ≫ g i = E.pullbackMap q hq ≫ g j

include hb in
/-- The fibre product of two members of `PointedFamily.pullbackCover` maps to the family pulled
back to the fibre product of the corresponding two members of the cover of `T`. -/
private def coverPairMap (i j : 𝒰.I₀) :
    Limits.pullback (E.pullbackMap (𝒰.f i) (hb i)) (E.pullbackMap (𝒰.f j) (hb j)) ⟶
      (E.pullback (Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ b i)).total :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst E.map (b i))
    (Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.snd E.map (b i))
      (Limits.pullback.snd _ _ ≫ Limits.pullback.snd E.map (b j)) (by
        simp only [Category.assoc]
        rw [← E.pullbackMap_snd (𝒰.f i) (hb i), ← E.pullbackMap_snd (𝒰.f j) (hb j),
          Limits.pullback.condition_assoc]))
    (by
      simp only [Category.assoc, Limits.pullback.lift_fst_assoc]
      rw [Limits.pullback.condition])

include hb in
/-- Glue morphisms out of the pulled-back families over the members of an open cover of `T`
into a morphism out of `E ×_{S,a} T`. -/
def glueHom (g : ∀ i, (E.pullback (b i)).total ⟶ Z) (hg : E.CoverCompatible 𝒰 g) :
    (E.pullback a).total ⟶ Z :=
  Scheme.Cover.glueMorphisms (E.pullbackCover 𝒰 hb) g (fun (i j : 𝒰.I₀) => by
    have hq : Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ b i =
        Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ b j := by
      rw [hb, hb, Limits.pullback.condition_assoc]
    have h₁ : coverPairMap E 𝒰 hb i j ≫
        E.pullbackMap (Limits.pullback.fst (𝒰.f i) (𝒰.f j)) rfl =
        Limits.pullback.fst (E.pullbackMap (𝒰.f i) (hb i)) (E.pullbackMap (𝒰.f j) (hb j)) := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp [coverPairMap]
      · simp [coverPairMap]
    have h₂ : coverPairMap E 𝒰 hb i j ≫
        E.pullbackMap (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) hq =
        Limits.pullback.snd (E.pullbackMap (𝒰.f i) (hb i)) (E.pullbackMap (𝒰.f j) (hb j)) := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [coverPairMap, Category.assoc, pullbackMap_fst, Limits.pullback.lift_fst]
        rw [← E.pullbackMap_fst (𝒰.f i) (hb i), ← E.pullbackMap_fst (𝒰.f j) (hb j),
          Limits.pullback.condition_assoc]
      · simp [coverPairMap]
    change Limits.pullback.fst (E.pullbackMap (𝒰.f i) (hb i)) (E.pullbackMap (𝒰.f j) (hb j)) ≫
        g i = Limits.pullback.snd _ _ ≫ g j
    rw [← h₁, ← h₂, Category.assoc, Category.assoc,
      hg i j _ _ _ _ rfl hq Limits.pullback.condition])

/-- The glued morphism restricts to the given morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackMap_glueHom (g : ∀ i, (E.pullback (b i)).total ⟶ Z)
    (hg : E.CoverCompatible 𝒰 g) (i : 𝒰.I₀) :
    E.pullbackMap (𝒰.f i) (hb i) ≫ E.glueHom 𝒰 hb g hg = g i :=
  Scheme.Cover.ι_glueMorphisms (E.pullbackCover 𝒰 hb) g _ i

end PointedFamily

/-! ### The functor of triples -/

variable {S S' : Scheme.{u}}

/-- The functor `Sch^{opp} → Sets` sending a scheme `T` to the triples `(a, a', α)` of Tag 072L,
with base change of triples as its action on morphisms. -/
@[simps obj]
def comparisonFunctor (E : PointedFamily S) (E' : PointedFamily S') :
    Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Comparison E E' T.unop
  map h := ↾fun x => x.baseChange h.unop
  map_id T := by
    ext x
    exact x.baseChange_id
  map_comp h k := by
    ext x
    exact x.baseChange_comp h.unop k.unop

/-- The functor of triples sends `h : U ⟶ T` to base change of triples along `h`. -/
@[simp]
theorem comparisonFunctor_map_apply (E : PointedFamily S) (E' : PointedFamily S')
    {T U : Scheme.{u}} (h : U ⟶ T) (x : Comparison E E' T) :
    (comparisonFunctor E E').map h.op x = x.baseChange h :=
  rfl

/-- A scheme represents the triples in the sense of `RepresentsComparisons` exactly when it
represents the functor of triples. -/
def RepresentsComparisons.representableBy {E : PointedFamily S} {E' : PointedFamily S'}
    {P : Scheme.{u}} (r : RepresentsComparisons E E' P) :
    (comparisonFunctor E E').RepresentableBy P where
  homEquiv {T} := r.homEquiv T
  homEquiv_comp f g := (r.naturality f g).eq_baseChange

/-- A representing object of the functor of triples is a fibre product `S ×_{𝓜₁,₁} S'`. -/
def representsComparisonsOfRepresentableBy {E : PointedFamily S} {E' : PointedFamily S'}
    {P : Scheme.{u}} (r : (comparisonFunctor E E').RepresentableBy P) :
    RepresentsComparisons E E' P where
  homEquiv T := r.homEquiv
  naturality h g := by
    have e : r.homEquiv (h ≫ g) = (r.homEquiv g).baseChange h := r.homEquiv_comp h g
    exact (congrArg ((r.homEquiv g).IsBaseChange h) e).mpr
      (Comparison.isBaseChange_baseChange (r.homEquiv g) h)

/-! ### The functor of triples is a Zariski sheaf -/

namespace Comparison

variable {T U : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- The isomorphism of a triple lies over the test scheme, in the form of the second projections
of the two pulled-back families. -/
@[reassoc (attr := simp)]
theorem iso_hom_snd (x : Comparison E E' T) :
    x.iso.hom ≫ Limits.pullback.snd E'.map x.snd = Limits.pullback.snd E.map x.fst :=
  x.iso_map

/-- The inverse isomorphism of a triple lies over the test scheme, in the form of the second
projections of the two pulled-back families. -/
@[reassoc (attr := simp)]
theorem iso_inv_snd (x : Comparison E E' T) :
    x.iso.inv ≫ Limits.pullback.snd E.map x.fst = Limits.pullback.snd E'.map x.snd :=
  x.iso_inv_map

/-- The square of `Comparison.IsBaseChange`, for any proofs of the two equalities of morphisms
to the bases. -/
theorem IsBaseChange.iso_hom {x : Comparison E E' T} {h : U ⟶ T} {y : Comparison E E' U}
    (hy : x.IsBaseChange h y) (hfst : y.fst = h ≫ x.fst) (hsnd : y.snd = h ≫ x.snd) :
    y.iso.hom ≫ E'.pullbackMap h hsnd = E.pullbackMap h hfst ≫ x.iso.hom :=
  hy.2.2

/-- The square of `Comparison.IsBaseChange` for the inverse isomorphisms. -/
theorem IsBaseChange.iso_inv {x : Comparison E E' T} {h : U ⟶ T} {y : Comparison E E' U}
    (hy : x.IsBaseChange h y) (hfst : y.fst = h ≫ x.fst) (hsnd : y.snd = h ≫ x.snd) :
    y.iso.inv ≫ E.pullbackMap h hfst = E'.pullbackMap h hsnd ≫ x.iso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hy.iso_hom hfst hsnd, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

variable {𝒰 : T.OpenCover}

/-- A family of triples over the members of an open cover of `T` is compatible when any two of
them agree on every test scheme mapping compatibly to the two members. -/
def CoverCompatible (𝒰 : T.OpenCover) (x : ∀ i, Comparison E E' (𝒰.X i)) : Prop :=
  ∀ (i j : 𝒰.I₀) (Y : Scheme.{u}) (p : Y ⟶ 𝒰.X i) (q : Y ⟶ 𝒰.X j), p ≫ 𝒰.f i = q ≫ 𝒰.f j →
    (x i).baseChange p = (x j).baseChange q

namespace CoverCompatible

variable {x : ∀ i, Comparison E E' (𝒰.X i)} (hx : CoverCompatible 𝒰 x)

include hx in
/-- The first morphisms of a compatible family of triples agree on the overlaps `Uᵢ ×_T Uⱼ`. -/
theorem fst_eq (i j : 𝒰.I₀) :
    Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).fst =
      Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).fst :=
  congrArg Comparison.fst (hx i j _ _ _ Limits.pullback.condition)

include hx in
/-- The second morphisms of a compatible family of triples agree on the overlaps `Uᵢ ×_T Uⱼ`. -/
theorem snd_eq (i j : 𝒰.I₀) :
    Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).snd =
      Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).snd :=
  congrArg Comparison.snd (hx i j _ _ _ Limits.pullback.condition)

/-- The glued morphism `a : T ⟶ S`. -/
def glueFst : T ⟶ S :=
  𝒰.glueMorphisms (fun i => (x i).fst) hx.fst_eq

/-- The glued morphism `a' : T ⟶ S'`. -/
def glueSnd : T ⟶ S' :=
  𝒰.glueMorphisms (fun i => (x i).snd) hx.snd_eq

/-- The glued morphism `a : T ⟶ S` restricts to the first morphism of each triple. -/
theorem fst_eq_glueFst (i : 𝒰.I₀) : (x i).fst = 𝒰.f i ≫ hx.glueFst :=
  (𝒰.ι_glueMorphisms (fun i => (x i).fst) hx.fst_eq i).symm

/-- The glued morphism `a' : T ⟶ S'` restricts to the second morphism of each triple. -/
theorem snd_eq_glueSnd (i : 𝒰.I₀) : (x i).snd = 𝒰.f i ≫ hx.glueSnd :=
  (𝒰.ι_glueMorphisms (fun i => (x i).snd) hx.snd_eq i).symm

/-- The local isomorphisms, followed by the open immersions of the pulled-back families. -/
def homFamily (i : 𝒰.I₀) : (E.pullback (x i).fst).total ⟶ (E'.pullback hx.glueSnd).total :=
  (x i).iso.hom ≫ E'.pullbackMap (𝒰.f i) (hx.snd_eq_glueSnd i)

/-- The inverses of the local isomorphisms, followed by the open immersions of the pulled-back
families. -/
def invFamily (i : 𝒰.I₀) : (E'.pullback (x i).snd).total ⟶ (E.pullback hx.glueFst).total :=
  (x i).iso.inv ≫ E.pullbackMap (𝒰.f i) (hx.fst_eq_glueFst i)

/-- A member of a compatible family is a base change of the base change of another member. -/
private theorem isBaseChange_baseChange_of_eq (h : CoverCompatible 𝒰 x) (i j : 𝒰.I₀)
    {Y : Scheme.{u}} (p : Y ⟶ 𝒰.X i) (q : Y ⟶ 𝒰.X j) (hpq : p ≫ 𝒰.f i = q ≫ 𝒰.f j) :
    (x j).IsBaseChange q ((x i).baseChange p) := by
  rw [h i j Y p q hpq]
  exact isBaseChange_baseChange (x j) q

/-- The family `homFamily` satisfies the compatibility condition for glueing. -/
theorem homFamily_compatible : E.CoverCompatible 𝒰 hx.homFamily := by
  intro i j Y p q c hp hq hpq
  dsimp only at hp hq
  subst hp
  have hj := isBaseChange_baseChange_of_eq hx i j p q hpq
  have hsj : p ≫ (x i).snd = q ≫ (x j).snd := hj.2.1
  have e₁ : E.pullbackMap p (rfl : p ≫ (x i).fst = _) ≫ (x i).iso.hom =
      ((x i).baseChange p).iso.hom ≫ E'.pullbackMap p (rfl : p ≫ (x i).snd = _) :=
    ((isBaseChange_baseChange (x i) p).iso_hom rfl rfl).symm
  have e₂ : E.pullbackMap q hq ≫ (x j).iso.hom =
      ((x i).baseChange p).iso.hom ≫ E'.pullbackMap q hsj :=
    (hj.iso_hom hq hsj).symm
  have c₁ := E'.pullbackMap_comp (𝒰.f i) p (hx.snd_eq_glueSnd i)
    (rfl : ((x i).baseChange p).snd = p ≫ (x i).snd)
  have c₂ := E'.pullbackMap_comp (𝒰.f j) q (hx.snd_eq_glueSnd j) hsj
  simp only [homFamily]
  rw [reassoc_of% e₁, reassoc_of% e₂, c₁, c₂]
  exact congrArg _ (PointedFamily.pullbackMap_congr _ hpq _ _)

/-- The family `invFamily` satisfies the compatibility condition for glueing. -/
theorem invFamily_compatible : E'.CoverCompatible 𝒰 hx.invFamily := by
  intro i j Y p q c hp hq hpq
  dsimp only at hp hq
  subst hp
  have hj := isBaseChange_baseChange_of_eq hx i j p q hpq
  have hfj : p ≫ (x i).fst = q ≫ (x j).fst := hj.1
  have e₁ : E'.pullbackMap p (rfl : p ≫ (x i).snd = _) ≫ (x i).iso.inv =
      ((x i).baseChange p).iso.inv ≫ E.pullbackMap p (rfl : p ≫ (x i).fst = _) :=
    ((isBaseChange_baseChange (x i) p).iso_inv rfl rfl).symm
  have e₂ : E'.pullbackMap q hq ≫ (x j).iso.inv =
      ((x i).baseChange p).iso.inv ≫ E.pullbackMap q hfj :=
    (hj.iso_inv hfj hq).symm
  have c₁ := E.pullbackMap_comp (𝒰.f i) p (hx.fst_eq_glueFst i)
    (rfl : ((x i).baseChange p).fst = p ≫ (x i).fst)
  have c₂ := E.pullbackMap_comp (𝒰.f j) q (hx.fst_eq_glueFst j) hfj
  simp only [invFamily]
  rw [reassoc_of% e₁, reassoc_of% e₂, c₁, c₂]
  exact congrArg _ (PointedFamily.pullbackMap_congr _ hpq _ _)

/-- The glued isomorphism of pulled-back families. -/
def glueHom : (E.pullback hx.glueFst).total ⟶ (E'.pullback hx.glueSnd).total :=
  E.glueHom 𝒰 hx.fst_eq_glueFst hx.homFamily hx.homFamily_compatible

/-- The inverse of the glued isomorphism. -/
def glueInv : (E'.pullback hx.glueSnd).total ⟶ (E.pullback hx.glueFst).total :=
  E'.glueHom 𝒰 hx.snd_eq_glueSnd hx.invFamily hx.invFamily_compatible

/-- The glued isomorphism restricts over `Uᵢ` to the `i`-th local isomorphism. -/
@[reassoc (attr := simp)]
theorem pullbackMap_glueHom (i : 𝒰.I₀) :
    E.pullbackMap (𝒰.f i) (hx.fst_eq_glueFst i) ≫ hx.glueHom =
      (x i).iso.hom ≫ E'.pullbackMap (𝒰.f i) (hx.snd_eq_glueSnd i) :=
  E.pullbackMap_glueHom 𝒰 _ _ _ i

/-- The inverse of the glued isomorphism restricts over `Uᵢ` to the inverse of the `i`-th local
isomorphism. -/
@[reassoc (attr := simp)]
theorem pullbackMap_glueInv (i : 𝒰.I₀) :
    E'.pullbackMap (𝒰.f i) (hx.snd_eq_glueSnd i) ≫ hx.glueInv =
      (x i).iso.inv ≫ E.pullbackMap (𝒰.f i) (hx.fst_eq_glueFst i) :=
  E'.pullbackMap_glueHom 𝒰 _ _ _ i

/-- The triple glued from a compatible family of triples over an open cover. -/
def glue : Comparison E E' T where
  fst := hx.glueFst
  snd := hx.glueSnd
  iso :=
    { hom := hx.glueHom
      inv := hx.glueInv
      hom_inv_id := E.hom_ext_of_cover 𝒰 hx.fst_eq_glueFst fun i => by simp
      inv_hom_id := E'.hom_ext_of_cover 𝒰 hx.snd_eq_glueSnd fun i => by simp }
  iso_map := E.hom_ext_of_cover 𝒰 hx.fst_eq_glueFst fun i => by simp
  zero_iso := 𝒰.hom_ext _ _ fun i => by
    have h₁ := E.zero_pullbackMap (𝒰.f i) (hx.fst_eq_glueFst i)
    have h₂ := E'.zero_pullbackMap (𝒰.f i) (hx.snd_eq_glueSnd i)
    rw [← h₂, ← reassoc_of% h₁]
    change (E.pullback (x i).fst).zero ≫ E.pullbackMap (𝒰.f i) _ ≫ hx.glueHom = _
    rw [pullbackMap_glueHom, ← Category.assoc, (x i).zero_iso]

/-- The glued triple restricts to the given triples. -/
theorem glue_baseChange (i : 𝒰.I₀) : hx.glue.baseChange (𝒰.f i) = x i := by
  have hb : hx.glue.IsBaseChange (𝒰.f i) (x i) :=
    ⟨hx.fst_eq_glueFst i, hx.snd_eq_glueSnd i, (hx.pullbackMap_glueHom i).symm⟩
  exact hb.eq_baseChange.symm

/-- A triple restricting to the given triples is the glued triple. -/
theorem eq_glue (t : Comparison E E' T) (ht : ∀ i, t.baseChange (𝒰.f i) = x i) :
    t = hx.glue := by
  have h₁ : t.fst = hx.glueFst := 𝒰.hom_ext _ _ fun i => by
    rw [← hx.fst_eq_glueFst i, ← ht i, baseChange_fst]
  have h₂ : t.snd = hx.glueSnd := 𝒰.hom_ext _ _ fun i => by
    rw [← hx.snd_eq_glueSnd i, ← ht i, baseChange_snd]
  have hb : ∀ i, t.IsBaseChange (𝒰.f i) (x i) := fun i => by
    rw [← ht i]
    exact isBaseChange_baseChange t (𝒰.f i)
  obtain ⟨c, c', β, hβ₁, hβ₂⟩ := t
  dsimp only at h₁ h₂ hb
  subst h₁ h₂
  obtain rfl : β = hx.glue.iso := Iso.ext (E.hom_ext_of_cover 𝒰 hx.fst_eq_glueFst fun i => by
    rw [← (hb i).iso_hom (hx.fst_eq_glueFst i) (hx.snd_eq_glueSnd i)]
    exact (hx.pullbackMap_glueHom i).symm)
  rfl

end CoverCompatible

end Comparison

/-- The functor of triples satisfies the sheaf condition for every open cover. -/
theorem comparisonFunctor_isSheafFor (E : PointedFamily S) (E' : PointedFamily S')
    {T : Scheme.{u}} (𝒰 : T.OpenCover) :
    Presieve.IsSheafFor (comparisonFunctor E E') 𝒰.presieve₀ := by
  rw [PreZeroHypercover.presieve₀, Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hx' : Comparison.CoverCompatible 𝒰 x := fun i j Y p q hpq => hx i j Y p q hpq
  exact ⟨hx'.glue, hx'.glue_baseChange, fun t ht => hx'.eq_glue t ht⟩

/-- **The functor of triples is a sheaf for the Zariski topology.** Triples over the members of
an open cover of a test scheme which agree on overlaps glue to a unique triple. -/
theorem comparisonFunctor_isSheaf (E : PointedFamily S) (E' : PointedFamily S') :
    Presheaf.IsSheaf Scheme.zariskiTopology (comparisonFunctor E E') := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange _).mpr
  intro T R hR
  obtain ⟨𝒱, rfl⟩ := R.exists_eq_preZeroHypercover
  exact comparisonFunctor_isSheafFor E E' ⟨𝒱, hR⟩

/-! ### Fibre products tested on affine schemes, and their uniqueness -/

namespace Comparison

variable {T : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- Two triples over `T` are equal as soon as their base changes to the members of an open cover
of `T` are. -/
theorem eq_of_baseChange_cover (𝒰 : T.OpenCover) {t₁ t₂ : Comparison E E' T}
    (h : ∀ i, t₁.baseChange (𝒰.f i) = t₂.baseChange (𝒰.f i)) : t₁ = t₂ := by
  have hx : CoverCompatible 𝒰 fun i => t₂.baseChange (𝒰.f i) := fun i j Y p q hpq => by
    rw [← baseChange_comp, ← baseChange_comp, hpq]
  exact (hx.eq_glue t₁ h).trans (hx.eq_glue t₂ fun _ => rfl).symm

end Comparison

section Affine

variable {E : PointedFamily S} {E' : PointedFamily S'} {P : Scheme.{u}}
  (c : ∀ T : Scheme.{u}, (T ⟶ P) → Comparison E E' T)
  (hc : ∀ {T U : Scheme.{u}} (h : U ⟶ T) (g : T ⟶ P), (c T g).IsBaseChange h (c U (h ≫ g)))

include hc in
/-- A family of maps from `T`-points of `P` to triples, natural in `T` and injective on affine
schemes, is injective on every scheme. -/
theorem injective_of_bijective_affine
    (hbij : ∀ R : CommRingCat.{u}, Function.Bijective (c (Spec R))) (T : Scheme.{u}) :
    Function.Injective (c T) := by
  intro g₁ g₂ hg
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => (hbij _).1 ?_
  have e₁ := (hc (T.affineCover.f i) g₁).eq_baseChange
  have e₂ := (hc (T.affineCover.f i) g₂).eq_baseChange
  rw [hg] at e₁
  exact e₁.trans e₂.symm

/-- **A fibre product over `𝓜₁,₁` may be tested on affine schemes.**  A family of maps from
`T`-points of `P` to triples over `T`, natural in `T`, which is bijective for every affine `T`,
makes `P` a fibre product `S ×_{𝓜₁,₁} S'`: the functor of triples is a Zariski sheaf, so both
injectivity and surjectivity pass from the members of an affine open cover to `T`. -/
def representsComparisons_of_bijective_affine
    (hbij : ∀ R : CommRingCat.{u}, Function.Bijective (c (Spec R))) :
    RepresentsComparisons E E' P where
  homEquiv T := Equiv.ofBijective (c T) ⟨injective_of_bijective_affine c hc hbij T, by
    intro x
    let 𝒰 := T.affineCover
    choose g hg using fun i => (hbij _).2 (x.baseChange (𝒰.f i))
    have hglue : ∀ i j, Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := fun i j => by
      apply injective_of_bijective_affine c hc hbij
      have e₁ := (hc (Limits.pullback.fst (𝒰.f i) (𝒰.f j)) (g i)).eq_baseChange
      have e₂ := (hc (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) (g j)).eq_baseChange
      have h₁ : (c _ (g i)).baseChange (Limits.pullback.fst (𝒰.f i) (𝒰.f j)) =
          x.baseChange (Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) :=
        (congrArg (fun y => Comparison.baseChange y (Limits.pullback.fst (𝒰.f i) (𝒰.f j)))
          (hg i)).trans (Comparison.baseChange_comp _ _ _).symm
      have h₂ : (c _ (g j)).baseChange (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) =
          x.baseChange (Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j) :=
        (congrArg (fun y => Comparison.baseChange y (Limits.pullback.snd (𝒰.f i) (𝒰.f j)))
          (hg j)).trans (Comparison.baseChange_comp _ _ _).symm
      refine (e₁.trans h₁).trans (Eq.trans ?_ (e₂.trans h₂).symm)
      rw [Limits.pullback.condition]
    refine ⟨𝒰.glueMorphisms g hglue, Comparison.eq_of_baseChange_cover 𝒰 fun i => ?_⟩
    refine (hc (𝒰.f i) _).eq_baseChange.symm.trans ?_
    have := congrArg (c _) (Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i)
    exact this.trans (hg i)⟩
  naturality h g := hc h g

/-- The bijection of `representsComparisons_of_bijective_affine` is the given family of maps. -/
@[simp]
theorem representsComparisons_of_bijective_affine_homEquiv
    (hbij : ∀ R : CommRingCat.{u}, Function.Bijective (c (Spec R))) (T : Scheme.{u})
    (g : T ⟶ P) :
    (representsComparisons_of_bijective_affine c hc hbij).homEquiv T g = c T g :=
  rfl

end Affine

namespace RepresentsComparisons

variable {E : PointedFamily S} {E' : PointedFamily S'} {P₁ P₂ : Scheme.{u}}
  (r₁ : RepresentsComparisons E E' P₁) (r₂ : RepresentsComparisons E E' P₂)

/-- **A fibre product over `𝓜₁,₁` is unique up to unique isomorphism**: the isomorphism of two
fibre products `P₁` and `P₂` matching their universal triples. -/
def uniqueIso : P₁ ≅ P₂ :=
  r₁.representableBy.uniqueUpToIso r₂.representableBy

/-- The triple of `P₂` classified by `uniqueIso r₁ r₂` is the universal triple of `P₁`. -/
theorem homEquiv_uniqueIso_hom :
    r₂.homEquiv P₁ (uniqueIso r₁ r₂).hom = r₁.homEquiv P₁ (𝟙 P₁) := by
  change r₂.homEquiv P₁ ((r₂.homEquiv P₁).symm (r₁.homEquiv P₁ (𝟙 P₁))) = _
  exact Equiv.apply_symm_apply _ _

/-- The isomorphism `uniqueIso r₁ r₂` is compatible with the first projections. -/
@[reassoc]
theorem uniqueIso_hom_fst :
    (uniqueIso r₁ r₂).hom ≫ (r₂.homEquiv P₂ (𝟙 P₂)).fst = (r₁.homEquiv P₁ (𝟙 P₁)).fst := by
  rw [← r₂.fst_homEquiv, homEquiv_uniqueIso_hom]

/-- The isomorphism `uniqueIso r₁ r₂` is compatible with the second projections. -/
@[reassoc]
theorem uniqueIso_hom_snd :
    (uniqueIso r₁ r₂).hom ≫ (r₂.homEquiv P₂ (𝟙 P₂)).snd = (r₁.homEquiv P₁ (𝟙 P₁)).snd := by
  rw [← r₂.snd_homEquiv, homEquiv_uniqueIso_hom]

end RepresentsComparisons

/-! ### Restricting the second family to an open of its base -/

section RestrictSnd

variable {S₀' T V : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- A point of an open subscheme maps into the open. -/
private theorem opens_ι_apply_mem {X : Scheme.{u}} (U : X.Opens) (t : U) :
    U.ι t ∈ (U : Set X) :=
  (Scheme.Opens.range_ι U).subset (Set.mem_range_self t)

/-- If `f ≫ U.ι = k ≫ g`, then `g` maps the image of `k` into the open `U`. -/
private theorem apply_mem_of_comp_ι_eq {X Y Z : Scheme.{u}} {U : Z.Opens} {f : X ⟶ U}
    {k : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ U.ι = k ≫ g) (t : X) : g (k t) ∈ (U : Set Z) := by
  rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  exact opens_ι_apply_mem U _

namespace Comparison

/-- The triple of `(E, E')` underlying a triple of `(E, E' ×_{S',c'} S₀')`. -/
def toRestrictSnd (c' : S₀' ⟶ S') (x : Comparison E (E'.pullback c') T) : Comparison E E' T :=
  ofFamilyIso x.fst (x.snd ≫ c') (x.familyIso.trans (E'.pullbackPullbackIso c' x.snd rfl))

/-- A triple of `(E, E' ×_{S',c'} S₀')` from a triple `y` of `(E, E')` whose second morphism
factors through `c'`. -/
def ofRestrictSnd (c' : S₀' ⟶ S') (a' : T ⟶ S₀') (y : Comparison E E' T)
    (h₂ : y.snd = a' ≫ c') : Comparison E (E'.pullback c') T :=
  ofFamilyIso y.fst a' (y.familyIso.trans (E'.pullbackPullbackIso c' a' h₂).symm)

/-- The first morphism of `Comparison.toRestrictSnd c' x` is that of `x`. -/
@[simp]
theorem toRestrictSnd_fst (c' : S₀' ⟶ S') (x : Comparison E (E'.pullback c') T) :
    (toRestrictSnd c' x).fst = x.fst :=
  rfl

/-- The second morphism of `Comparison.toRestrictSnd c' x` is `x.snd ≫ c'`. -/
@[simp]
theorem toRestrictSnd_snd (c' : S₀' ⟶ S') (x : Comparison E (E'.pullback c') T) :
    (toRestrictSnd c' x).snd = x.snd ≫ c' :=
  rfl

/-- The first morphism of `Comparison.ofRestrictSnd c' a' y h₂` is that of `y`. -/
@[simp]
theorem ofRestrictSnd_fst (c' : S₀' ⟶ S') (a' : T ⟶ S₀') (y : Comparison E E' T)
    (h₂ : y.snd = a' ≫ c') : (ofRestrictSnd c' a' y h₂).fst = y.fst :=
  rfl

/-- The second morphism of `Comparison.ofRestrictSnd c' a' y h₂` is `a'`. -/
@[simp]
theorem ofRestrictSnd_snd (c' : S₀' ⟶ S') (a' : T ⟶ S₀') (y : Comparison E E' T)
    (h₂ : y.snd = a' ≫ c') : (ofRestrictSnd c' a' y h₂).snd = a' :=
  rfl

/-- `Comparison.ofRestrictSnd` depends only on the morphism `a'` and the triple, not on the proof
of the factorization. -/
theorem ofRestrictSnd_congr (c' : S₀' ⟶ S') {a₁ a₂ : T ⟶ S₀'} {y₁ y₂ : Comparison E E' T}
    (h₁ : y₁.snd = a₁ ≫ c') (h₂ : y₂.snd = a₂ ≫ c') (ha : a₁ = a₂) (hy : y₁ = y₂) :
    ofRestrictSnd c' a₁ y₁ h₁ = ofRestrictSnd c' a₂ y₂ h₂ := by
  subst ha hy
  rfl

/-- `Comparison.ofRestrictSnd` is a left inverse of `Comparison.toRestrictSnd`. -/
theorem ofRestrictSnd_toRestrictSnd (c' : S₀' ⟶ S') (x : Comparison E (E'.pullback c') T) :
    ofRestrictSnd c' x.snd (toRestrictSnd c' x) rfl = x := by
  change Comparison.ofFamilyIso x.fst x.snd _ = Comparison.ofFamilyIso x.fst x.snd x.familyIso
  refine Comparison.ofFamilyIso_ext ?_
  dsimp only [toRestrictSnd, Comparison.ofFamilyIso, FamilyIso.trans_iso, FamilyIso.symm_iso,
    Comparison.familyIso_iso, Iso.trans_hom, Iso.symm_hom]
  simp

/-- `Comparison.toRestrictSnd` is a left inverse of `Comparison.ofRestrictSnd`. -/
theorem toRestrictSnd_ofRestrictSnd (c' : S₀' ⟶ S') (a' : T ⟶ S₀') (y : Comparison E E' T)
    (h₂ : y.snd = a' ≫ c') : toRestrictSnd c' (ofRestrictSnd c' a' y h₂) = y := by
  obtain ⟨b, b', i, hi₁, hi₂⟩ := y
  dsimp only at h₂
  subst h₂
  change Comparison.ofFamilyIso b (a' ≫ c') _ = Comparison.ofFamilyIso b (a' ≫ c') ⟨i, hi₁, hi₂⟩
  refine Comparison.ofFamilyIso_ext ?_
  dsimp only [ofRestrictSnd, Comparison.ofFamilyIso, FamilyIso.trans_iso, FamilyIso.symm_iso,
    Comparison.familyIso_iso, Iso.trans_hom, Iso.symm_hom]
  simp

/-- Restricting the second family preserves the base-change relation. -/
theorem IsBaseChange.ofRestrictSnd (c' : S₀' ⟶ S') {a' : T ⟶ S₀'} {y : Comparison E E' T}
    (h₂ : y.snd = a' ≫ c') {h : V ⟶ T} {z : Comparison E E' V} (k₂ : z.snd = (h ≫ a') ≫ c')
    (hyz : y.IsBaseChange h z) :
    (Comparison.ofRestrictSnd c' a' y h₂).IsBaseChange h
      (Comparison.ofRestrictSnd c' (h ≫ a') z k₂) := by
  obtain ⟨hf, hs, hiso⟩ := hyz
  refine ⟨hf, rfl, ?_⟩
  dsimp only [Comparison.ofRestrictSnd, Comparison.ofFamilyIso, Comparison.familyIso,
    FamilyIso.trans, FamilyIso.symm, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← PointedFamily.pullbackMap_pullbackPullbackIso_inv E' c' h rfl h₂ k₂ hs, reassoc_of% hiso]

end Comparison

namespace RepresentsComparisons

variable {P : Scheme.{u}} (r : RepresentsComparisons E E' P) (U : S'.Opens)

/-- The open of a fibre product `P` over which its second projection lands in `U`. -/
abbrev restrictSndOpen : P.Opens :=
  (r.homEquiv P (𝟙 P)).snd ⁻¹ᵁ U

/-- For a `T`-point `g` of `restrictSndOpen U`, the second morphism of the triple classified by
`g` followed by the inclusion factors through `U` via the restricted second projection. -/
theorem snd_homEquiv_comp_ι {T : Scheme.{u}} (g : T ⟶ r.restrictSndOpen U) :
    (r.homEquiv T (g ≫ (r.restrictSndOpen U).ι)).snd =
      (g ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U)) ≫ U.ι := by
  rw [r.snd_homEquiv, Category.assoc, Category.assoc, morphismRestrict_ι]

/-- The `T`-point of `P` classifying the triple underlying a triple of `(E, E'|_U)` lands in
`restrictSndOpen U`. -/
theorem range_homEquiv_symm_toRestrictSnd {T : Scheme.{u}}
    (x : Comparison E (E'.pullback U.ι) T) :
    Set.range ((r.homEquiv T).symm (Comparison.toRestrictSnd U.ι x)) ⊆
      Set.range (r.restrictSndOpen U).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  change (r.homEquiv P (𝟙 P)).snd _ ∈ U
  rw [← Scheme.Hom.comp_apply, ← r.snd_homEquiv, Equiv.apply_symm_apply,
    Comparison.toRestrictSnd_snd, Scheme.Hom.comp_apply]
  exact opens_ι_apply_mem U _

/-- **Restricting the second family to an open of its base restricts the fibre product to an
open.**  For a fibre product `P` of `(E, E')` and an open `U` of `S'`, the open of `P` over which
the second projection lands in `U` is a fibre product of `(E, E'|_U)`. -/
def restrictSnd : RepresentsComparisons E (E'.pullback U.ι) (r.restrictSndOpen U) where
  homEquiv T :=
    { toFun g := Comparison.ofRestrictSnd U.ι (g ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U))
        (r.homEquiv T (g ≫ (r.restrictSndOpen U).ι)) (r.snd_homEquiv_comp_ι U g)
      invFun x := IsOpenImmersion.lift (r.restrictSndOpen U).ι
        ((r.homEquiv T).symm (Comparison.toRestrictSnd U.ι x))
        (r.range_homEquiv_symm_toRestrictSnd U x)
      left_inv g := by
        apply (cancel_mono (r.restrictSndOpen U).ι).1
        rw [IsOpenImmersion.lift_fac, Comparison.toRestrictSnd_ofRestrictSnd,
          Equiv.symm_apply_apply]
      right_inv x := by
        have hy : r.homEquiv T (IsOpenImmersion.lift (r.restrictSndOpen U).ι
            ((r.homEquiv T).symm (Comparison.toRestrictSnd U.ι x))
            (r.range_homEquiv_symm_toRestrictSnd U x) ≫ (r.restrictSndOpen U).ι) =
            Comparison.toRestrictSnd U.ι x := by
          rw [IsOpenImmersion.lift_fac, Equiv.apply_symm_apply]
        have ha : IsOpenImmersion.lift (r.restrictSndOpen U).ι
            ((r.homEquiv T).symm (Comparison.toRestrictSnd U.ι x))
            (r.range_homEquiv_symm_toRestrictSnd U x) ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U) =
            x.snd := by
          apply (cancel_mono U.ι).1
          rw [← r.snd_homEquiv_comp_ι U, hy, Comparison.toRestrictSnd_snd]
        exact (Comparison.ofRestrictSnd_congr U.ι _ rfl ha hy).trans
          (Comparison.ofRestrictSnd_toRestrictSnd U.ι x) }
  naturality {T T'} h g := by
    have k₂ : (r.homEquiv T' (h ≫ g ≫ (r.restrictSndOpen U).ι)).snd =
        (h ≫ g ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U)) ≫ U.ι := by
      rw [← Category.assoc h g, ← Category.assoc h g, r.snd_homEquiv_comp_ι U]
    have hb := Comparison.IsBaseChange.ofRestrictSnd U.ι (r.snd_homEquiv_comp_ι U g) k₂
      (r.naturality h (g ≫ (r.restrictSndOpen U).ι))
    have e : Comparison.ofRestrictSnd U.ι ((h ≫ g) ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U))
        (r.homEquiv T' ((h ≫ g) ≫ (r.restrictSndOpen U).ι)) (r.snd_homEquiv_comp_ι U (h ≫ g)) =
        Comparison.ofRestrictSnd U.ι (h ≫ g ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U))
          (r.homEquiv T' (h ≫ g ≫ (r.restrictSndOpen U).ι)) k₂ :=
      Comparison.ofRestrictSnd_congr U.ι _ _ (Category.assoc _ _ _)
        (congrArg _ (Category.assoc _ _ _))
    change (Comparison.ofRestrictSnd U.ι (g ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U))
      (r.homEquiv T (g ≫ (r.restrictSndOpen U).ι)) (r.snd_homEquiv_comp_ι U g)).IsBaseChange h
      (Comparison.ofRestrictSnd U.ι ((h ≫ g) ≫ ((r.homEquiv P (𝟙 P)).snd ∣_ U))
        (r.homEquiv T' ((h ≫ g) ≫ (r.restrictSndOpen U).ι)) (r.snd_homEquiv_comp_ι U (h ≫ g)))
    rw [e]
    exact hb

/-- The second projection of the restricted fibre product is the restriction of the second
projection. -/
theorem restrictSnd_snd :
    ((r.restrictSnd U).homEquiv _ (𝟙 _)).snd = (r.homEquiv P (𝟙 P)).snd ∣_ U :=
  Category.id_comp _

/-- The first projection of the restricted fibre product is the restriction of the first
projection. -/
theorem restrictSnd_fst :
    ((r.restrictSnd U).homEquiv _ (𝟙 _)).fst =
      (r.restrictSndOpen U).ι ≫ (r.homEquiv P (𝟙 P)).fst := by
  change (r.homEquiv _ (𝟙 _ ≫ (r.restrictSndOpen U).ι)).fst = _
  rw [Category.id_comp, r.fst_homEquiv]

end RepresentsComparisons

end RestrictSnd

/-! ### Triples of restricted families as an open subfunctor -/

section Restrict

variable {S₀ S₀' T V : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

namespace Comparison

/-- Passing from a triple of restricted families to the underlying triple commutes with base
change. -/
theorem toRestrict_baseChange (c : S₀ ⟶ S) (c' : S₀' ⟶ S')
    (x : Comparison (E.pullback c) (E'.pullback c') T) (k : V ⟶ T) :
    toRestrict c c' (x.baseChange k) = (toRestrict c c' x).baseChange k := by
  have hx : x = ofRestrict c c' x.fst x.snd (toRestrict c c' x) rfl rfl :=
    (ofRestrict_toRestrict c c' x).symm
  have k₁ : ((toRestrict c c' x).baseChange k).fst = (k ≫ x.fst) ≫ c :=
    (Category.assoc _ _ _).symm
  have k₂ : ((toRestrict c c' x).baseChange k).snd = (k ≫ x.snd) ≫ c' :=
    (Category.assoc _ _ _).symm
  have hb := IsBaseChange.ofRestrict c c' rfl rfl k₁ k₂
    (isBaseChange_baseChange (toRestrict c c' x) k)
  rw [← hx] at hb
  rw [← hb.eq_baseChange, toRestrict_ofRestrict]

/-- Passing from a triple of restricted families to the underlying triple is injective when the
two restrictions are along monomorphisms. -/
theorem toRestrict_injective (c : S₀ ⟶ S) (c' : S₀' ⟶ S') [Mono c] [Mono c'] :
    Function.Injective (toRestrict (T := T) (F := E) (F' := E') c c') := by
  intro x y h
  rw [← ofRestrict_toRestrict c c' x, ← ofRestrict_toRestrict c c' y]
  exact ofRestrict_congr c c' rfl rfl rfl rfl
    ((cancel_mono c).1 (congrArg Comparison.fst h)) ((cancel_mono c').1 (congrArg Comparison.snd h))
    h

end Comparison

variable {U : S.Opens} {U' : S'.Opens} {P : Scheme.{u}}
  (r : RepresentsComparisons (E.pullback U.ι) (E'.pullback U'.ι) P)

/-- The morphism from the functor of points of a fibre product of the restricted families
`(E|_U, E'|_{U'})` to the functor of triples of `(E, E')`. -/
def restrictChart : yoneda.obj P ⟶ comparisonFunctor E E' where
  app T := ↾fun g => Comparison.toRestrict U.ι U'.ι (r.homEquiv T.unop g)
  naturality T₁ T₂ k := by
    ext g
    exact (congrArg (Comparison.toRestrict U.ι U'.ι) (r.naturality k.unop g).eq_baseChange).trans
      (Comparison.toRestrict_baseChange U.ι U'.ι _ k.unop)

/-- The chart `restrictChart r` sends a `T`-point of `P` to the triple of `(E, E')` underlying
the triple of restricted families it classifies. -/
theorem restrictChart_app_apply {T : Scheme.{u}} (g : T ⟶ P) :
    (restrictChart r).app (op T) g = Comparison.toRestrict U.ι U'.ι (r.homEquiv T g) :=
  rfl

/-- The open of a test scheme over which a triple of `(E, E')` comes from the restricted
families: the locus where both of its morphisms to the bases land in `U` and in `U'`. -/
def Comparison.restrictLocus (U : S.Opens) (U' : S'.Opens) (x : Comparison E E' T) : T.Opens :=
  x.fst ⁻¹ᵁ U ⊓ x.snd ⁻¹ᵁ U'

namespace Comparison

variable (x : Comparison E E' T)

/-- A point of `restrictLocus` lies in `restrictLocus` as an open of `T`. -/
theorem mem_restrictLocus (t : (x.restrictLocus U U').toScheme) :
    (x.restrictLocus U U').ι t ∈ x.restrictLocus U U' :=
  show _ ∈ ((x.restrictLocus U U' : T.Opens) : Set T) from
    opens_ι_apply_mem _ t

/-- On `restrictLocus`, the first morphism of the triple lands in `U`. -/
theorem range_restrictLocus_fst :
    Set.range ((x.restrictLocus U U').ι ≫ x.fst) ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (x.mem_restrictLocus t).1

/-- On `restrictLocus`, the second morphism of the triple lands in `U'`. -/
theorem range_restrictLocus_snd :
    Set.range ((x.restrictLocus U U').ι ≫ x.snd) ⊆ Set.range U'.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (x.mem_restrictLocus t).2

/-- The triple of restricted families over `restrictLocus` underlying a triple of `(E, E')`. -/
def restrictTo : Comparison (E.pullback U.ι) (E'.pullback U'.ι) (x.restrictLocus U U') :=
  ofRestrict U.ι U'.ι
    (IsOpenImmersion.lift U.ι _ x.range_restrictLocus_fst)
    (IsOpenImmersion.lift U'.ι _ x.range_restrictLocus_snd)
    (x.baseChange (x.restrictLocus U U').ι) (IsOpenImmersion.lift_fac _ _ _).symm
    (IsOpenImmersion.lift_fac _ _ _).symm

/-- The triple underlying `Comparison.restrictTo` is the base change of `x` to `restrictLocus`. -/
theorem toRestrict_restrictTo :
    toRestrict U.ι U'.ι (x.restrictTo (U := U) (U' := U')) =
      x.baseChange (x.restrictLocus U U').ι :=
  toRestrict_ofRestrict _ _ _ _ _ _ _

end Comparison

/-- The chart point: the morphism from `restrictLocus` to the fibre product of the restricted
families classifying `Comparison.restrictTo`. -/
def chartPoint {T : Scheme.{u}} (x : Comparison E E' T) : (x.restrictLocus U U').toScheme ⟶ P :=
  (r.homEquiv _).symm x.restrictTo

/-- For `t : T' ⟶ restrictLocus`, the triple of `(E, E')` underlying the triple classified by
`t ≫ chartPoint r x` is the base change of `x` along `t` followed by the inclusion. -/
theorem toRestrict_homEquiv_comp_chartPoint {T T' : Scheme.{u}} (x : Comparison E E' T)
    (t : T' ⟶ x.restrictLocus U U') :
    Comparison.toRestrict U.ι U'.ι (r.homEquiv T' (t ≫ chartPoint r x)) =
      x.baseChange (t ≫ (x.restrictLocus U U').ι) := by
  rw [(r.naturality t (chartPoint r x)).eq_baseChange, chartPoint, Equiv.apply_symm_apply,
    Comparison.toRestrict_baseChange, Comparison.toRestrict_restrictTo,
    Comparison.baseChange_comp]

/-- **The triples of the restricted families form an open subfunctor.**  The chart
`restrictChart r` is a relatively representable open immersion of presheaves: its pullback along
a triple `x` over `T` is represented by the open `restrictLocus` of `T`. -/
theorem isOpenImmersion_restrictChart : IsOpenImmersion.presheaf (restrictChart r) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective g
  refine ⟨x.restrictLocus U U', yoneda.map (chartPoint r x), (x.restrictLocus U U').ι, ?_,
    inferInstance⟩
  rw [IsPullback.iff_app]
  intro T'
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext t
    exact toRestrict_homEquiv_comp_chartPoint r x t
  · intro f₁ f₂ hf
    exact (cancel_mono (x.restrictLocus U U').ι).1 hf.2
  · intro (p : T'.unop ⟶ P) (k : T'.unop ⟶ T) hpk
    change Comparison.toRestrict U.ι U'.ι (r.homEquiv T'.unop p) = x.baseChange k at hpk
    have hfst : (r.homEquiv T'.unop p).fst ≫ U.ι = k ≫ x.fst := congrArg Comparison.fst hpk
    have hsnd : (r.homEquiv T'.unop p).snd ≫ U'.ι = k ≫ x.snd := congrArg Comparison.snd hpk
    have hk : Set.range k ⊆ Set.range (x.restrictLocus U U').ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      refine ⟨?_, ?_⟩
      · exact apply_mem_of_comp_ι_eq hfst t
      · exact apply_mem_of_comp_ι_eq hsnd t
    refine ⟨IsOpenImmersion.lift _ k hk, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    change IsOpenImmersion.lift _ k hk ≫ chartPoint r x = p
    apply (r.homEquiv T'.unop).injective
    apply Comparison.toRestrict_injective U.ι U'.ι
    refine (toRestrict_homEquiv_comp_chartPoint r x _).trans ?_
    rw [IsOpenImmersion.lift_fac, hpk]

end Restrict

/-! ### Glueing fibre products over open covers of the two bases -/

section Glue

variable {ι ι' : Type u} {E : PointedFamily S} {E' : PointedFamily S'}
  {U : ι → S.Opens} {U' : ι' → S'.Opens} {P : ι → ι' → Scheme.{u}}
  (r : ∀ i j, RepresentsComparisons (E.pullback (U i).ι) (E'.pullback (U' j).ι) (P i j))

/-- If the opens `Uᵢ` cover `S` and the opens `U'ⱼ` cover `S'`, the charts `restrictChart` of
all pairs `(i, j)` are jointly locally surjective onto the functor of triples for the Zariski
topology. -/
theorem restrictChart_isLocallySurjective (hU : ⨆ i, U i = ⊤) (hU' : ⨆ j, U' j = ⊤) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun k : ι × ι' => restrictChart (r k.1 k.2)) := by
  constructor
  intro T (x : Comparison E E' T)
  let W : ι × ι' → T.Opens := fun k => x.restrictLocus (U k.1) (U' k.2)
  have hW : TopologicalSpace.IsOpenCover W := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU ▸ trivial : x.fst t ∈ ⨆ i, U i)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU' ▸ trivial : x.snd t ∈ ⨆ j, U' j)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  apply Scheme.zariskiTopology.superset_covering _
    (T.openCoverOfIsOpenCover W hW).mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V g ⟨k⟩
  refine ⟨(Sigma.ι (fun k : ι × ι' => yoneda.obj (P k.1 k.2)) k).app (op (W k).toScheme)
    (chartPoint (r k.1 k.2) x), ?_⟩
  refine (congrArg (fun t => t.app (op (W k).toScheme) (chartPoint (r k.1 k.2) x))
    (Sigma.ι_comp_desc (fun k : ι × ι' => restrictChart (r k.1 k.2)) k)).trans ?_
  change Comparison.toRestrict _ _ ((r k.1 k.2).homEquiv _ (chartPoint (r k.1 k.2) x)) = _
  rw [chartPoint, Equiv.apply_symm_apply, Comparison.toRestrict_restrictTo]
  rfl

/-- **The fibre product over `𝓜₁,₁` is Zariski local on the two bases.**  If `S` and `S'` are
covered by opens `Uᵢ` and `U'ⱼ` such that for every pair `(i, j)` the restricted families
`E|_{Uᵢ}` and `E'|_{U'ⱼ}` have a fibre product `Uᵢ ×_{𝓜₁,₁} U'ⱼ`, then `E` and `E'` have a fibre
product `S ×_{𝓜₁,₁} S'`, glued from the `Uᵢ ×_{𝓜₁,₁} U'ⱼ`. -/
theorem exists_representsComparisons_of_openCover (E : PointedFamily S) (E' : PointedFamily S')
    (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤) (U' : ι' → S'.Opens) (hU' : ⨆ j, U' j = ⊤)
    (h : ∀ i j, ∃ P : Scheme.{u},
      Nonempty (RepresentsComparisons (E.pullback (U i).ι) (E'.pullback (U' j).ι) P)) :
    ∃ P : Scheme.{u}, Nonempty (RepresentsComparisons E E' P) := by
  choose P r using h
  have := restrictChart_isLocallySurjective (fun i j => (r i j).some) hU hU'
  obtain ⟨X, ⟨R⟩⟩ := (Scheme.LocalRepresentability.isRepresentable
    (F := ⟨comparisonFunctor E E', comparisonFunctor_isSheaf E E'⟩)
    (f := fun k : ι × ι' => restrictChart (r k.1 k.2).some)
    (fun k => isOpenImmersion_restrictChart _)).has_representation
  exact ⟨X, ⟨representsComparisonsOfRepresentableBy R⟩⟩

end Glue

end AlgebraicGeometry.ModuliEllipticCurves

end
