module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
import all StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension

/-!
# Families of curves and schemes

Glue between families of curves in the sense of Stacks 0D4Z — morphisms of algebraic spaces over
the big fppf site of `Spec(ℤ)` — and morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionLE_schemeSpaceMap_of_fiberDimension_le`: the
  relative-dimension field of `AlgebraicGeometry.CurveFamily`, at the bound `n`, for a morphism of
  the site whose fibres have dimension at most `n`.

## Implementation notes

The relative-dimension condition is derived from a bound on the dimension of the scheme-theoretic
fibres, at the points of the target. Over a positive-dimensional base this, and not a bound on the
dimension of the total space, is the condition of Stacks 0D4Z.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The germ of a morphism of schemes whose fibre through a point has dimension at most `n` has,
at that point, fibre dimension some natural number at most `n`. -/
theorem exists_hasFiberDimensionAt_ofSchemeHom_of_fiberDimension_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (n : ℕ) (hfib : f.fiberDimension (f x) ≤ ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ n ∧ HasFiberDimensionAt (e : ℕ∞) (MorphismOfGerms.ofSchemeHom f x) := by
  set h : ((⊤ : X.Opens) : Scheme.{u}) ⟶ Y := X.topIso.hom ≫ f with hh
  set z : ((⊤ : X.Opens) : Scheme.{u}) := ⟨x, by simp⟩ with hz
  have hfd : h.fiberDimension = f.fiberDimension :=
    Scheme.Hom.fiberDimension_eq_of_over_iso (S := Y) (A := Over.mk h) (B := Over.mk f)
      (Over.isoMk X.topIso)
  have hle : topologicalKrullDimAt (h.fiber (h z)) (h.asFiber z) ≤ ((n : ℕ∞) : WithBot ℕ∞) :=
    (Scheme.Hom.topologicalKrullDimAt_fiber_le_fiberDimension h rfl).trans (hfd ▸ hfib)
  obtain ⟨e, hen, hee⟩ := exists_nat_le_eq _ n (topologicalKrullDimAt_nonneg (h.asFiber z)) hle
  exact ⟨e, hen, { source := ⊤
                   mem_source := by simp
                   hom := X.topIso.hom ≫ f
                   map_point := rfl }, rfl, hee⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative-dimension condition of Stacks 0D4Z from the fibres.** A morphism of the big
fppf site of `S` all of whose scheme-theoretic fibres have dimension at most `n` induces a
morphism of algebraic spaces of relative dimension at most `n` in the sense of the
`relativeDimensionLE` field of `AlgebraicGeometry.CurveFamily`. -/
theorem relativeDimensionLE_schemeSpaceMap_of_fiberDimension_le {T U : BigFppfOver B S hS}
    (g : T ⟶ U) (n : ℕ)
    (hfib : ∀ y, ((BigFppfOver.toScheme B S hS).map g).fiberDimension y ≤
      ((n : ℕ∞) : WithBot ℕ∞))
    (x : points B S hS (schemeSpace T).obj) :
    ∃ e : ℕ, e ≤ n ∧
      HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (schemeSpaceMap g).hom x := by
  obtain ⟨e, hen, hee⟩ := exists_hasFiberDimensionAt_ofSchemeHom_of_fiberDimension_le
    ((BigFppfOver.toScheme B S hS).map g) (pointsToScheme B S hS T x) n (hfib _)
  exact ⟨e, hen, (holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B S hS
    (@HasFiberDimensionAt.{u} (e : ℕ∞))
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) g x).2 hee⟩

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

variable {B hZ}

/-- The base map of the identity morphism of a family of curves is the identity. -/
@[simp]
theorem id_baseMap (F : CurveFamily B hZ) : Hom.baseMap (𝟙 F) = 𝟙 F.base := rfl

/-- The total map of the identity morphism of a family of curves is the identity. -/
@[simp]
theorem id_totalMap (F : CurveFamily B hZ) : Hom.totalMap (𝟙 F) = 𝟙 F.total := rfl

/-- The base map of a composite of morphisms of families is the composite of base maps. -/
@[simp]
theorem comp_baseMap {F G H : CurveFamily B hZ} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).baseMap = f.baseMap ≫ g.baseMap := rfl

/-- The total map of a composite of morphisms of families is the composite of total maps. -/
@[simp]
theorem comp_totalMap {F G H : CurveFamily B hZ} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).totalMap = f.totalMap ≫ g.totalMap := rfl

/-- A family of curves with its base replaced by an equal object of the site; its structure
morphism is followed by the identification of the two bases. -/
abbrev ofBaseEq (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ} (e : F.base = V) :
    CurveFamily B hZ where
  base := V
  total := F.total
  toBase := F.toBase ≫ eqToHom (congrArg schemeSpace e)
  flat := by subst e; simpa using F.flat
  proper := by subst e; simpa using F.proper
  finitePresentation := by subst e; simpa using F.finitePresentation
  relativeDimensionLE := by subst e; simpa using F.relativeDimensionLE

/-- The base of `F.ofBaseEq e` is `V`. -/
@[simp]
theorem ofBaseEq_base (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) : (F.ofBaseEq e).base = V := rfl

/-- The total space of `F.ofBaseEq e` is that of `F`. -/
@[simp]
theorem ofBaseEq_total (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) : (F.ofBaseEq e).total = F.total := rfl

/-- The structure morphism of `F.ofBaseEq e` is that of `F` followed by the identification
of the bases. -/
theorem ofBaseEq_toBase (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) :
    (F.ofBaseEq e).toBase = F.toBase ≫ eqToHom (congrArg schemeSpace e) := rfl

/-- The identification of `F.ofBaseEq e` with `F`. -/
def ofBaseEqIso (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ} (e : F.base = V) :
    F.ofBaseEq e ≅ F :=
  isoMk (eqToIso e.symm) (Iso.refl _) (by
    subst e
    change 𝟙 _ ≫ F.toBase = (F.toBase ≫ 𝟙 _) ≫ schemeSpaceMap (𝟙 F.base)
    rw [show schemeSpaceMap (𝟙 F.base) = 𝟙 _ from (schemeSpaceFunctor B integerBase hZ).map_id _]
    simp)

/-- The base map of `F.ofBaseEqIso e` is the identification of the bases. -/
@[simp]
theorem ofBaseEqIso_hom_baseMap (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) : (F.ofBaseEqIso e).hom.baseMap = eqToHom e.symm := rfl

/-- The total map of `F.ofBaseEqIso e` is the identity. -/
@[simp]
theorem ofBaseEqIso_hom_totalMap (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) : (F.ofBaseEqIso e).hom.totalMap = 𝟙 _ := rfl

/-- **Base change of a family of curves along a morphism of bases**, with base the source of the
morphism on the nose: it is the base change of the fibred structure of Stacks 0D51
(`AlgebraicGeometry.CurveFamily.exists_hom_baseMap_eq`), with its base identified with the source
of the morphism by `AlgebraicGeometry.CurveFamily.ofBaseEq`. -/
theorem exists_hom_baseMap_eq_of_base_eq (F : CurveFamily B hZ)
    {T : BigFppfOver B integerBase hZ} (g : T ⟶ F.base) :
    ∃ (F' : CurveFamily B hZ) (hF' : F'.base = T) (φ : F' ⟶ F), φ.baseMap = eqToHom hF' ≫ g :=
  let ⟨F', φ, h, hφ⟩ := exists_hom_baseMap_eq F g
  ⟨F', h, φ, hφ⟩

/-- A chosen base change of `F` along `g`, with its base identified with `T`. -/
noncomputable def pullbackData (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    Σ' (F' : CurveFamily B hZ) (hF' : F'.base = T) (φ : F' ⟶ F), φ.baseMap = eqToHom hF' ≫ g :=
  Classical.choice (let ⟨F', hF', φ, hφ⟩ := exists_hom_baseMap_eq_of_base_eq F g
    ⟨⟨F', hF', φ, hφ⟩⟩)

/-- The base change of `F` along `g : T ⟶ F.base`, a family of curves with base `T`. -/
noncomputable abbrev pullback (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) : CurveFamily B hZ :=
  (F.pullbackData g).1.ofBaseEq (F.pullbackData g).2.1

/-- The base of the base change of `F` along `g : T ⟶ F.base` is `T`. -/
@[simp]
theorem pullback_base (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) : (F.pullback g).base = T := rfl

/-- The canonical morphism from the base change of `F` along `g` to `F`; its base map is `g`. -/
noncomputable def pullbackHom (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) : F.pullback g ⟶ F :=
  ((F.pullbackData g).1.ofBaseEqIso (F.pullbackData g).2.1).hom ≫ (F.pullbackData g).2.2.1

/-- The base map of the canonical morphism `F.pullback g ⟶ F` is `g`. -/
@[simp]
theorem pullbackHom_baseMap (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) : (F.pullbackHom g).baseMap = g :=
  (congrArg (eqToHom (F.pullbackData g).2.1.symm ≫ ·) (F.pullbackData g).2.2.2).trans
    (by rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp])

/-- The total space of the base change is the fibre product of the total space with the new
base. -/
theorem isPullback_pullbackHom (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    IsPullback (F.pullbackHom g).totalMap (F.pullback g).toBase F.toBase (schemeSpaceMap g) := by
  simpa using (F.pullbackHom g).cartesian

/-- A morphism of families of curves whose base map is an isomorphism has an isomorphism of
total spaces: its square is cartesian. -/
theorem isIso_totalMap_of_isIso_baseMap {F G : CurveFamily B hZ} (φ : F ⟶ G)
    [IsIso φ.baseMap] : IsIso φ.totalMap := by
  have : IsIso (schemeSpaceMap φ.baseMap) :=
    (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso (asIso φ.baseMap)).hom)
  exact φ.cartesian.isIso_fst_of_isIso

section BaseChange

/-- The comparison of two base changes of a family of curves through a factorization of the base
maps: for `p ≫ q = r`, the base change along `r` maps to the base change along `q` over `p`,
compatibly with the maps to the family. -/
theorem exists_hom_pullback_of_comp (F : CurveFamily B hZ) {U W : BigFppfOver B integerBase hZ}
    (q : W ⟶ F.base) (r : U ⟶ F.base) (p : U ⟶ W) (hpq : p ≫ q = r) :
    ∃ χ : F.pullback r ⟶ F.pullback q, χ.baseMap = p ∧ χ ≫ F.pullbackHom q = F.pullbackHom r := by
  obtain ⟨χ, ⟨hχ, hχc⟩, -⟩ :=
    ((curvesFiberedCategory B hZ).2 :
      (curvesProjectionOver B hZ).IsFiberedInGroupoids).unique_lift
      (F.pullbackHom q) (F.pullbackHom r) p
      (show p ≫ (F.pullbackHom q).baseMap = (F.pullbackHom r).baseMap by simpa using hpq)
  exact ⟨χ, hχ, hχc⟩

/-- The structure morphism of a family of curves, as a morphism of presheaves to the
representable presheaf of its base. -/
def toBaseYoneda (F : CurveFamily B hZ) : F.total.obj ⟶ yoneda.obj F.base := F.toBase.hom

/-- The cartesian square of a morphism of families of curves, on presheaves. -/
@[reassoc]
theorem totalMap_toBaseYoneda {F G : CurveFamily B hZ} (φ : F ⟶ G) :
    φ.totalMap.hom ≫ G.toBaseYoneda = F.toBaseYoneda ≫ yoneda.map φ.baseMap :=
  congrArg (fun t => t.hom) φ.cartesian.w

/-- The total space of the base change of a family along `g`, as the fibre product of presheaves
in the order `pullback (yoneda.map g) toBase`. -/
noncomputable def pullbackTotalIso (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    (F.pullback g).total.obj ≅ Limits.pullback (yoneda.map g) F.toBaseYoneda :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ (F.isPullback_pullbackHom g)).flip.isoPullback

/-- The identification `F.pullbackTotalIso g`, followed by the first projection, is the
structure morphism of the base change. -/
@[reassoc (attr := simp)]
theorem pullbackTotalIso_hom_fst (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    (F.pullbackTotalIso g).hom ≫ Limits.pullback.fst (yoneda.map g) F.toBaseYoneda =
      (F.pullback g).toBaseYoneda :=
  IsPullback.isoPullback_hom_fst _

/-- The identification `F.pullbackTotalIso g`, followed by the second projection, is the total
map of `F.pullbackHom g`. -/
@[reassoc (attr := simp)]
theorem pullbackTotalIso_hom_snd (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    (F.pullbackTotalIso g).hom ≫ Limits.pullback.snd (yoneda.map g) F.toBaseYoneda =
      (F.pullbackHom g).totalMap.hom :=
  IsPullback.isoPullback_hom_snd _

/-- The structure morphism of `F.ofBaseEq e`, as a morphism of presheaves to the representable
presheaf of `V`. -/
def toBaseYonedaOfEq (F : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ} (e : F.base = V) :
    F.total.obj ⟶ yoneda.obj V :=
  (F.ofBaseEq e).toBase.hom

/-- The cartesian square of a morphism of families into `F.ofBaseEq e`, on presheaves. -/
@[reassoc]
theorem totalMap_toBaseYonedaOfEq {X F : CurveFamily B hZ} {V : BigFppfOver B integerBase hZ}
    (e : F.base = V) (φ : X ⟶ F.ofBaseEq e) :
    φ.totalMap.hom ≫ F.toBaseYonedaOfEq e = X.toBaseYoneda ≫ yoneda.map φ.baseMap :=
  congrArg (fun t => t.hom) φ.cartesian.w

/-- The total space of the base change of `F.ofBaseEq e` along `g`, as a fibre product of
presheaves. -/
noncomputable def pullbackTotalIsoOfEq (F : CurveFamily B hZ)
    {T V : BigFppfOver B integerBase hZ} (e : F.base = V) (g : T ⟶ V) :
    ((F.ofBaseEq e).pullback g).total.obj ≅
      Limits.pullback (yoneda.map g) (F.toBaseYonedaOfEq e) :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ
    ((F.ofBaseEq e).isPullback_pullbackHom g)).flip.isoPullback

/-- The identification `F.pullbackTotalIsoOfEq e g`, followed by the first projection, is the
structure morphism of the base change. -/
@[reassoc (attr := simp)]
theorem pullbackTotalIsoOfEq_hom_fst (F : CurveFamily B hZ)
    {T V : BigFppfOver B integerBase hZ} (e : F.base = V) (g : T ⟶ V) :
    (F.pullbackTotalIsoOfEq e g).hom ≫ Limits.pullback.fst (yoneda.map g) (F.toBaseYonedaOfEq e) =
      ((F.ofBaseEq e).pullback g).toBaseYoneda :=
  IsPullback.isoPullback_hom_fst _

/-- The identification `F.pullbackTotalIsoOfEq e g`, followed by the second projection, is the
total map of `(F.ofBaseEq e).pullbackHom g`. -/
@[reassoc (attr := simp)]
theorem pullbackTotalIsoOfEq_hom_snd (F : CurveFamily B hZ)
    {T V : BigFppfOver B integerBase hZ} (e : F.base = V) (g : T ⟶ V) :
    (F.pullbackTotalIsoOfEq e g).hom ≫ Limits.pullback.snd (yoneda.map g) (F.toBaseYonedaOfEq e) =
      ((F.ofBaseEq e).pullbackHom g).totalMap.hom :=
  IsPullback.isoPullback_hom_snd _

/-- **Base change of a morphism of total spaces along a morphism of bases.** For families `P`, `Q`
over a common base `T` and a morphism `h` of their total spaces over `T`, the induced morphism of
the total spaces of their base changes along `τ : T' ⟶ T`. -/
noncomputable def pullbackTotalMap {P Q : CurveFamily B hZ} {T T' : BigFppfOver B integerBase hZ}
    (hP : P.base = T) (hQ : Q.base = T) (h : P.total.obj ⟶ Q.total.obj)
    (hh : h ≫ Q.toBaseYonedaOfEq hQ = P.toBaseYonedaOfEq hP) (τ : T' ⟶ T) :
    ((P.ofBaseEq hP).pullback τ).total.obj ⟶ ((Q.ofBaseEq hQ).pullback τ).total.obj :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ
    ((Q.ofBaseEq hQ).isPullback_pullbackHom τ)).lift
    (((P.ofBaseEq hP).pullbackHom τ).totalMap.hom ≫ h) ((P.ofBaseEq hP).pullback τ).toBaseYoneda
    (by
      rw [Category.assoc]
      change _ ≫ h ≫ Q.toBaseYonedaOfEq hQ = _
      rw [hh]
      exact (totalMap_toBaseYonedaOfEq hP ((P.ofBaseEq hP).pullbackHom τ)).trans
        (by rw [pullbackHom_baseMap]; rfl))

/-- `pullbackTotalMap` lies over `h` through the total maps of the base change morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackTotalMap_totalMap {P Q : CurveFamily B hZ} {T T' : BigFppfOver B integerBase hZ}
    (hP : P.base = T) (hQ : Q.base = T) (h : P.total.obj ⟶ Q.total.obj)
    (hh : h ≫ Q.toBaseYonedaOfEq hQ = P.toBaseYonedaOfEq hP) (τ : T' ⟶ T) :
    pullbackTotalMap hP hQ h hh τ ≫ ((Q.ofBaseEq hQ).pullbackHom τ).totalMap.hom =
      ((P.ofBaseEq hP).pullbackHom τ).totalMap.hom ≫ h :=
  IsPullback.lift_fst _ _ _ _

/-- `pullbackTotalMap` commutes with the structure morphisms of the base changes. -/
@[reassoc (attr := simp)]
theorem pullbackTotalMap_toBaseYoneda {P Q : CurveFamily B hZ}
    {T T' : BigFppfOver B integerBase hZ}
    (hP : P.base = T) (hQ : Q.base = T) (h : P.total.obj ⟶ Q.total.obj)
    (hh : h ≫ Q.toBaseYonedaOfEq hQ = P.toBaseYonedaOfEq hP) (τ : T' ⟶ T) :
    pullbackTotalMap hP hQ h hh τ ≫ ((Q.ofBaseEq hQ).pullback τ).toBaseYoneda =
      ((P.ofBaseEq hP).pullback τ).toBaseYoneda :=
  IsPullback.lift_snd _ _ _ _

/-- The cartesian square of the base change of `F.ofBaseEq e` along `g`, on presheaves. -/
theorem isPullback_pullbackHom_yoneda (F : CurveFamily B hZ) {T V : BigFppfOver B integerBase hZ}
    (e : F.base = V) (g : T ⟶ V) :
    IsPullback ((F.ofBaseEq e).pullbackHom g).totalMap.hom ((F.ofBaseEq e).pullback g).toBaseYoneda
      (F.toBaseYonedaOfEq e) (yoneda.map g) :=
  AlgebraicSpaces.isPullback_hom B integerBase hZ ((F.ofBaseEq e).isPullback_pullbackHom g)

/-- **Base change is transitive**: the base change along `k` of the base change along `g` has the
total space of the base change along `k ≫ g`, compatibly with the maps to the base and to `F`. -/
theorem exists_iso_pullback_pullback (F : CurveFamily B hZ) {U W V : BigFppfOver B integerBase hZ}
    (e : F.base = V) (g : W ⟶ V) (k : U ⟶ W) :
    ∃ i : (((F.ofBaseEq e).pullback g).pullback k).total.obj ≅
        ((F.ofBaseEq e).pullback (k ≫ g)).total.obj,
      i.hom ≫ ((F.ofBaseEq e).pullback (k ≫ g)).toBaseYoneda =
        (((F.ofBaseEq e).pullback g).pullback k).toBaseYoneda ∧
      i.hom ≫ ((F.ofBaseEq e).pullbackHom (k ≫ g)).totalMap.hom =
        (((F.ofBaseEq e).pullback g).pullbackHom k).totalMap.hom ≫
          ((F.ofBaseEq e).pullbackHom g).totalMap.hom := by
  have sq1 := AlgebraicSpaces.isPullback_hom B integerBase hZ
    (((F.ofBaseEq e).pullback g).isPullback_pullbackHom k)
  have sq2 := F.isPullback_pullbackHom_yoneda e g
  have sq := sq1.paste_horiz sq2
  have sq3 := F.isPullback_pullbackHom_yoneda e (k ≫ g)
  rw [Functor.map_comp] at sq3
  exact ⟨sq.isoIsPullback _ _ sq3, sq.isoIsPullback_hom_snd _ _ sq3,
    sq.isoIsPullback_hom_fst _ _ sq3⟩

/-- **A morphism of families of curves exhibits its source as a base change of its target.** -/
theorem exists_iso_pullback_of_hom {G H : CurveFamily B hZ} {V T : BigFppfOver B integerBase hZ}
    (hG : G.base = V) (hH : H.base = T) (g : V ⟶ T) (δ : G ⟶ H)
    (hδ : δ.baseMap = eqToHom hG ≫ g ≫ eqToHom hH.symm) :
    ∃ i : G.total.obj ≅ ((H.ofBaseEq hH).pullback g).total.obj,
      i.hom ≫ ((H.ofBaseEq hH).pullback g).toBaseYoneda = G.toBaseYonedaOfEq hG ∧
      i.hom ≫ ((H.ofBaseEq hH).pullbackHom g).totalMap.hom = δ.totalMap.hom := by
  subst hG hH
  have sq := AlgebraicSpaces.isPullback_hom B integerBase hZ δ.cartesian
  have sq' : IsPullback δ.totalMap.hom (G.toBaseYonedaOfEq rfl) (H.toBaseYonedaOfEq rfl)
      (yoneda.map g) := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hδ
    have e (F : CurveFamily B hZ) : F.toBaseYonedaOfEq rfl = F.toBase.hom := by
      simp [toBaseYonedaOfEq, ofBaseEq]
      rfl
    rw [e, e, ← hδ]
    exact sq
  have sq3 := H.isPullback_pullbackHom_yoneda rfl g
  exact ⟨sq'.isoIsPullback _ _ sq3, sq'.isoIsPullback_hom_snd _ _ sq3,
    sq'.isoIsPullback_hom_fst _ _ sq3⟩

end BaseChange

end CurveFamily

end AlgebraicGeometry

end
