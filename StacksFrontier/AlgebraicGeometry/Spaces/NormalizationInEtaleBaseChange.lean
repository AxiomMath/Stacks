module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraEtaleBaseChangeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion

/-!
# The normalization of an algebraic space in another commutes with étale base change

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S`, let `Y ⟶ X' ⟶ X` be a relative
normalization of it (the universal property of Stacks 0823,
`AlgebraicGeometry.Space.IsRelativeNormalization`), and let `g : W ⟶ X` be étale.  Part (1) of
Stacks 0ABP says that `W ×_X X' ⟶ W`, with the base change `W ×_X Y ⟶ W ×_X X'` of the
factorization, is the normalization of `W` in `W ×_X Y`.  This file proves the reduction of that
statement to a condition on the factorization alone, which is étale local and is checked on
sections.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegrallyClosed`: the structure sheaf is integrally
  closed in an algebra sheaf `𝒜`: on every étale chart the structure-algebra map is injective
  with image the locally integral sections.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegrallyClosed.of_iso` and
  `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegrallyClosed.etaleAlgebraRestriction`: the
  condition is invariant under isomorphism and under restriction along an étale morphism.
* `AlgebraicGeometry.Space.isRelativeNormalization_id_of_isIntegrallyClosed`: if `𝒪_T` is
  integrally closed in `q_* 𝒪_Y`, then `T` is the normalization of `T` in `Y`.
* `AlgebraicGeometry.Space.isIntegrallyClosed_of_isRelativeNormalization_id`: the converse, given
  some normalization of `T` in `Y` whose algebra is the integral closure.
* `AlgebraicGeometry.Space.IsRelativeNormalization.comp_of_id`: if `P` is the normalization of
  `P` in `Y'` and `ν : P ⟶ W` is integral, then `P` is the normalization of `W` in `Y'`.
* `AlgebraicGeometry.Space.isRelativeNormalization_of_isPullback_of_isEtale`: **the reduction of
  part (1) of Stacks 0ABP**: the base change of `Y ⟶ X' ⟶ X` along an étale `W ⟶ X` is a
  relative normalization, as soon as `𝒪_{X'}` is integrally closed in `f'_* 𝒪_Y`.

## Implementation notes

**Why the identity normalization.**  The source says part (1) is "immediate from the
construction": the integral closure of `𝒪_X` in `f_* 𝒪_Y` commutes with étale restriction, and
so does the relative spectrum.  Comparing the base change of the factorization `f'` with the
factorization of the base change along those identifications needs the base-change isomorphism
of Stacks 03LX for the direct image of the structure sheaf to be natural in the morphism `f'`,
which is not proved here.  The argument below avoids it.  The condition that `𝒪_{X'}` be
integrally closed in `f'_* 𝒪_Y` — that `X'` is the normalization of *itself* in `Y` — is about
the structure map `f'^♯` only, and the base-change isomorphism of Stacks 03LX *is* compatible
with structure maps: it is an isomorphism of algebra sheaves,
`AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeIso`.  The integral closure commutes
with étale restriction on the nose,
`AlgebraicGeometry.Space.locallyIntegralSections_etaleAlgebraRestriction`.  So the condition
passes to `P = W ×_X X'`, the algebra criterion of Stacks 0823
(`AlgebraicGeometry.Space.isRelativeNormalization_of_pushforwardAlgebraMap_eq`) makes `P` the
normalization of itself in `W ×_X Y`, and an integral `P ⟶ W` then makes it the normalization of
`W` in `W ×_X Y` by a formal argument with fibre products
(`AlgebraicGeometry.Space.IsRelativeNormalization.comp_of_id`).

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Integral closedness of the structure sheaf in an algebra -/

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The structure sheaf is integrally closed in the algebra sheaf `𝒜`**: on every étale chart
the structure-algebra map is injective, and its image is the subring of locally integral
sections, the sections of the integral closure of the structure sheaf in `𝒜`. -/
def IsIntegrallyClosed (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : (SmallEtale B S hS F)ᵒᵖ,
    Function.Injective (A.algebraMap U) ∧ (A.algebraMap U).range = A.locallyIntegralSections U

/-- A morphism of algebra sheaves whose underlying morphism of sheaves of rings is invertible is
an isomorphism of algebra sheaves. -/
def isoOfIsIsoRight {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C) [IsIso φ.right] :
    A ≅ C where
  hom := φ
  inv :=
    { right := inv φ.right
      comm := fun U r => by
        rw [← φ.comm U r]
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (congrArg (fun m => m.hom) (IsIso.hom_inv_id φ.right)) U)
          (A.algebraMap U r) }
  hom_inv_id := Hom.ext (IsIso.hom_inv_id φ.right)
  inv_hom_id := Hom.ext (IsIso.inv_hom_id φ.right)

/-- The inverse of an isomorphism of algebra sheaves undoes it on sections. -/
theorem iso_inv_right_app_hom_right_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ≅ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : A.right.obj.obj U) :
    (φ.inv.right.hom.app U) (φ.hom.right.hom.app U x) = x :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun m => (Hom.right m).hom) φ.hom_inv_id) U) x

/-- **Integral closedness is invariant under isomorphism of algebra sheaves.** -/
theorem IsIntegrallyClosed.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ≅ C)
    (hA : A.IsIntegrallyClosed) : C.IsIntegrallyClosed := by
  intro U
  have hcomm : ∀ r, C.algebraMap U r = φ.hom.right.hom.app U (A.algebraMap U r) :=
    fun r => (φ.hom.comm U r).symm
  refine ⟨fun r s hrs => (hA U).1 ?_, ?_⟩
  · rw [hcomm, hcomm] at hrs
    have := congrArg (φ.inv.right.hom.app U) hrs
    rwa [iso_inv_right_app_hom_right_app, iso_inv_right_app_hom_right_app] at this
  · ext x
    constructor
    · rintro ⟨r, rfl⟩
      rw [hcomm]
      refine map_mem_locallyIntegralSections φ.hom U ?_
      rw [← (hA U).2]
      exact ⟨r, rfl⟩
    · intro hx
      have hx' : φ.inv.right.hom.app U x ∈ A.locallyIntegralSections U :=
        map_mem_locallyIntegralSections φ.inv U hx
      rw [← (hA U).2] at hx'
      obtain ⟨r, hr⟩ := hx'
      refine ⟨r, ?_⟩
      rw [hcomm, hr]
      exact iso_inv_right_app_hom_right_app φ.symm U x

end AlgebraSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Integral closedness is étale local**: it passes to the restriction of an algebra sheaf
along an étale morphism.  The structure-algebra maps and the locally integral sections of the
restriction are those of the original algebra on the same charts read as charts of the target
(`AlgebraicGeometry.Space.locallyIntegralSections_etaleAlgebraRestriction`). -/
theorem AlgebraSheaf.IsIntegrallyClosed.etaleAlgebraRestriction {W X : AlgebraicSpaces B S hS}
    (g : W ⟶ X) (hg : IsEtale B S hS g.hom) {A : AlgebraSheaf.{u, m} B S hS X.1 X.2}
    (hA : A.IsIntegrallyClosed) :
    ((etaleAlgebraRestriction.{u, m} B S hS g hg).obj A).IsIntegrallyClosed := by
  intro U
  refine ⟨(hA ((smallEtalePostcomp B S hS g hg).op.obj U)).1, ?_⟩
  rw [locallyIntegralSections_etaleAlgebraRestriction]
  exact (hA ((smallEtalePostcomp B S hS g hg).op.obj U)).2

/-! ### The normalization of an algebraic space in another over itself -/

/-- The structure map of the identity of an algebraic space is bijective on every chart: it is
an isomorphism by the identity clause of Stacks 03G8, `AlgebraicGeometry.Space.isIso_fSharp_id`. -/
theorem bijective_pushforwardAlgebra_id_algebraMap (T : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS T.1)ᵒᵖ) :
    Function.Bijective ((pushforwardAlgebra B S hS (idAffineOver B S hS T).obj).algebraMap U) := by
  have := isIso_fSharp_id B S hS T
  let e := asIso (smallEtaleRingedToposHom B S hS (𝟙 T)).fSharp
  have h1 : ∀ x, (e.inv.hom.app U) (e.hom.hom.app U x) = x := fun x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom) e.hom_inv_id) U) x
  have h2 : ∀ y, (e.hom.hom.app U) (e.inv.hom.app U y) = y := fun y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom) e.inv_hom_id) U) y
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/-- The direct image of the structure sheaf along the identity is integral over the structure
sheaf: its structure-algebra map is surjective. -/
theorem isIntegral_pushforwardAlgebra_id (T : AlgebraicSpaces B S hS) :
    (pushforwardAlgebra B S hS (idAffineOver B S hS T).obj).IsIntegral := by
  intro U _ x
  obtain ⟨r, rfl⟩ := (bijective_pushforwardAlgebra_id_algebraMap B S hS T (op U)).2 x
  exact AlgebraSheaf.isIntegralElem_apply _ r

/-- A morphism `q : Y ⟶ T`, as a morphism over `T` from `Y` to `T` itself. -/
def overHomToId {T Y : AlgebraicSpaces B S hS} (q : Y ⟶ T) :
    Over.mk q ⟶ (idAffineOver B S hS T).obj :=
  Over.homMk q (Category.comp_id q)

/-- The direct-image map of `q : Y ⟶ T` over `T`, read through the identification of the direct
image along the identity, is the structure-algebra map of `q_* 𝒪_Y`. -/
theorem pushforwardAlgebraMap_overHomToId_algebraMap {T Y : AlgebraicSpaces B S hS} (q : Y ⟶ T)
    (U : (SmallEtale B S hS T.1)ᵒᵖ) (r : (structureSheaf B S hS T.1 T.2).obj.obj U) :
    (pushforwardAlgebraMap B S hS (overHomToId B S hS q)).right.hom.app U
        ((pushforwardAlgebra B S hS (idAffineOver B S hS T).obj).algebraMap U r) =
      (pushforwardAlgebra B S hS (Over.mk q)).algebraMap U r :=
  (pushforwardAlgebraMap B S hS (overHomToId B S hS q)).comm U r

/-- On every chart, the direct-image map of `q` over `T` is the structure-algebra map of
`q_* 𝒪_Y` composed with the inverse of the bijective structure map of the identity. -/
theorem range_pushforwardAlgebraMap_overHomToId {T Y : AlgebraicSpaces B S hS} (q : Y ⟶ T)
    (U : (SmallEtale B S hS T.1)ᵒᵖ) :
    ((pushforwardAlgebraMap B S hS (overHomToId B S hS q)).right.hom.app U).hom.range =
      ((pushforwardAlgebra B S hS (Over.mk q)).algebraMap U).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨r, rfl⟩ := (bijective_pushforwardAlgebra_id_algebraMap B S hS T U).2 x
    exact ⟨r, (pushforwardAlgebraMap_overHomToId_algebraMap B S hS q U r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨_, pushforwardAlgebraMap_overHomToId_algebraMap B S hS q U r⟩

/-- **If `𝒪_T` is integrally closed in `q_* 𝒪_Y`, then `T` is the normalization of `T` in `Y`.**

This is the algebra criterion of Stacks 0823,
`AlgebraicGeometry.Space.isRelativeNormalization_of_pushforwardAlgebraMap_eq`, at the identity
of `T`: the direct image of the structure sheaf along the identity is integral, so its map to
`q_* 𝒪_Y` factors through the integral closure, and integral closedness says that the
factorization is bijective on every chart. -/
theorem isRelativeNormalization_id_of_isIntegrallyClosed {T Y : AlgebraicSpaces B S hS}
    (q : Y ⟶ T) (hq : (pushforwardAlgebra B S hS (Over.mk q)).IsIntegrallyClosed) :
    IsRelativeNormalization B S hS q.hom (𝟙 T.1) q.hom := by
  let φ := pushforwardAlgebraMap B S hS (overHomToId B S hS q)
  obtain ⟨ψ, hψ, -⟩ := AlgebraSheaf.existsUnique_hom_integralClosureSheaf φ
    (isIntegral_pushforwardAlgebra_id B S hS T)
  have hψU : ∀ U x, ((ψ.right.hom.app U) x).1 = (φ.right.hom.app U) x := fun U x =>
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun m => (AlgebraSheaf.Hom.right m).hom) hψ) U) x
  have hbij : ∀ U, Function.Bijective (ψ.right.hom.app U) := by
    intro U
    have hinj : Function.Injective (φ.right.hom.app U) := by
      intro x y hxy
      obtain ⟨r, rfl⟩ := (bijective_pushforwardAlgebra_id_algebraMap B S hS T U).2 x
      obtain ⟨s, rfl⟩ := (bijective_pushforwardAlgebra_id_algebraMap B S hS T U).2 y
      rw [pushforwardAlgebraMap_overHomToId_algebraMap,
        pushforwardAlgebraMap_overHomToId_algebraMap] at hxy
      rw [(hq U).1 hxy]
    refine ⟨fun x y hxy => hinj ?_, fun z => ?_⟩
    · rw [← hψU, ← hψU, hxy]
    · have hz : z.1 ∈ ((φ.right.hom.app U).hom).range := by
        rw [range_pushforwardAlgebraMap_overHomToId, (hq U).2]
        exact z.2
      obtain ⟨x, hx⟩ := hz
      exact ⟨x, Subtype.ext ((hψU U x).trans hx)⟩
  have : IsIso ψ.right := by
    have : IsIso ((sheafToPresheaf _ _).map ψ.right) := by
      have : ∀ U, IsIso (((sheafToPresheaf _ _).map ψ.right).app U) := fun U =>
        (ConcreteCategory.isIso_iff_bijective _).2 (hbij U)
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  let e := (AlgebraSheaf.isoOfIsIsoRight ψ).symm
  exact isRelativeNormalization_of_pushforwardAlgebraMap_eq B S hS q (idAffineOver B S hS T)
    (isIntegralHom_of_isIso B S hS (𝟙 T.1)) (overHomToId B S hS q) e
    (by
      show (AlgebraSheaf.isoOfIsIsoRight ψ).inv ≫ φ = _
      rw [← hψ]
      exact (AlgebraSheaf.isoOfIsIsoRight ψ).inv_hom_id_assoc _)

/-- If the direct image along the identity of `T` is identified with the integral closure of
`𝒪_T` in `q_* 𝒪_Y` compatibly with the maps to `q_* 𝒪_Y`, then `𝒪_T` is integrally closed in
`q_* 𝒪_Y`. -/
theorem isIntegrallyClosed_of_iso_integralClosureSheaf {T Y : AlgebraicSpaces B S hS}
    (q : Y ⟶ T)
    (σ : pushforwardAlgebra B S hS (idAffineOver B S hS T).obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk q)))
    (hσ : pushforwardAlgebraMap B S hS (overHomToId B S hS q) =
      σ.hom ≫ AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk q))) :
    (pushforwardAlgebra B S hS (Over.mk q)).IsIntegrallyClosed := by
  intro U
  have hval : ∀ r, (pushforwardAlgebra B S hS (Over.mk q)).algebraMap U r =
      (σ.hom.right.hom.app U
        ((pushforwardAlgebra B S hS (idAffineOver B S hS T).obj).algebraMap U r)).1 := by
    intro r
    rw [← pushforwardAlgebraMap_overHomToId_algebraMap, hσ]
    rfl
  refine ⟨fun r s hrs => ?_, ?_⟩
  · rw [hval, hval] at hrs
    have h2 := congrArg (σ.inv.right.hom.app U) (Subtype.ext hrs)
    rw [AlgebraSheaf.iso_inv_right_app_hom_right_app,
      AlgebraSheaf.iso_inv_right_app_hom_right_app] at h2
    exact (bijective_pushforwardAlgebra_id_algebraMap B S hS T U).1 h2
  · ext y
    constructor
    · rintro ⟨r, rfl⟩
      rw [hval]
      exact (σ.hom.right.hom.app U _).2
    · intro hy
      obtain ⟨r, hr⟩ := (bijective_pushforwardAlgebra_id_algebraMap B S hS T U).2
        (σ.inv.right.hom.app U ⟨y, hy⟩)
      refine ⟨r, ?_⟩
      rw [hval, hr]
      exact congrArg Subtype.val (AlgebraSheaf.iso_inv_right_app_hom_right_app σ.symm U ⟨y, hy⟩)

/-- **The converse: if `T` is the normalization of `T` in `Y`, and some normalization of `T` in
`Y` has the integral closure for its algebra, then `𝒪_T` is integrally closed in `q_* 𝒪_Y`.**

The two normalizations are identified over `T` by the characterization of Stacks 0823, so the
direct image along `T ⟶ T` is identified with the integral closure compatibly with the maps to
`q_* 𝒪_Y`. -/
theorem isIntegrallyClosed_of_isRelativeNormalization_id {T Y : AlgebraicSpaces B S hS}
    (q : Y ⟶ T) (h : IsRelativeNormalization B S hS q.hom (𝟙 T.1) q.hom)
    (N : AffineOver B S hS T) (q' : Over.mk q ⟶ N.obj)
    (hN : IsRelativeNormalization B S hS q.hom N.obj.hom.hom q'.left.hom)
    (e : AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk q)) ≅
      pushforwardAlgebra B S hS N.obj)
    (he : e.hom ≫ pushforwardAlgebraMap B S hS q' =
      AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk q))) :
    (pushforwardAlgebra B S hS (Over.mk q)).IsIntegrallyClosed := by
  obtain ⟨φ, ⟨hφ1, hφ2⟩, -⟩ := h.existsUnique_iso hN T.2 N.obj.left.2
  let Φ : (idAffineOver B S hS T).obj ⟶ N.obj :=
    Over.homMk (ObjectProperty.homMk φ.hom) (ObjectProperty.hom_ext _ hφ2)
  let Φinv : N.obj ⟶ (idAffineOver B S hS T).obj :=
    Over.homMk (ObjectProperty.homMk φ.inv) (ObjectProperty.hom_ext _ (by
      show φ.inv ≫ 𝟙 T.1 = N.obj.hom.hom
      simpa using (congrArg (φ.inv ≫ ·) hφ2).symm))
  have hΦ : Φ ≫ Φinv = 𝟙 _ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ φ.hom_inv_id)
  have hΦ' : Φinv ≫ Φ = 𝟙 _ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ φ.inv_hom_id)
  have hq' : overHomToId B S hS q ≫ Φ = q' :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hφ1)
  -- the direct-image map of `Φ` is an isomorphism of algebra sheaves
  let ΦA : pushforwardAlgebra B S hS (idAffineOver B S hS T).obj ≅
      pushforwardAlgebra B S hS N.obj :=
    { hom := pushforwardAlgebraMap B S hS Φinv
      inv := pushforwardAlgebraMap B S hS Φ
      hom_inv_id := by
        rw [← pushforwardAlgebraMap_comp, hΦ, pushforwardAlgebraMap_id]
      inv_hom_id := by
        rw [← pushforwardAlgebraMap_comp, hΦ', pushforwardAlgebraMap_id] }
  -- `q'^♯ = Φ^♯ ≫ q^♯`, so `q^♯ = Φinv^♯ ≫ q'^♯ = (ΦA.hom ≫ e.inv) ≫ ι`
  have hmap : pushforwardAlgebraMap B S hS (overHomToId B S hS q) =
      (ΦA ≪≫ e.symm).hom ≫
        AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk q)) := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc, ← hq',
      pushforwardAlgebraMap_comp, ← Category.assoc, ΦA.hom_inv_id, Category.id_comp]
  exact isIntegrallyClosed_of_iso_integralClosureSheaf B S hS q (ΦA ≪≫ e.symm) hmap

/-! ### From the normalization of `P` in `Y'` to the normalization of `W` in `Y'` -/

/-- **If `P` is the normalization of itself in `Y'` and `ν : P ⟶ W` is integral, then `P` is the
normalization of `W` in `Y'`.**

A factorization of `q ≫ ν` through an integral `π : Z ⟶ W` gives one of `q` through the base
change `P ×_W Z ⟶ P`, which is integral; the universal property of `P` over itself supplies a
unique section of it compatible with `q`, and its second component is the required morphism
`P ⟶ Z`. -/
theorem IsRelativeNormalization.comp_of_id {Y P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q : Y ⟶ P} {ν : P ⟶ W} (h : IsRelativeNormalization B S hS q (𝟙 P) q)
    (hν : IsIntegralHom B S hS ν) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) :
    IsRelativeNormalization B S hS (q ≫ ν) ν q := by
  refine ⟨Category.id_comp _ |>.symm.trans (by rw [Category.id_comp]), hν, ?_⟩
  intro Z hZ π hπ g hg
  have hZ' := isAlgebraicSpace_pullback B S hS ν π hP hZ hW
  have hint : IsIntegralHom B S hS (pullback.fst ν π) :=
    isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback ν π).flip hπ
  obtain ⟨s, ⟨hs1, hs2⟩, hsu⟩ := h.existsUnique_lift hZ' (pullback.fst ν π) hint
    (pullback.lift q g hg.symm) (pullback.lift_fst _ _ _)
  refine ⟨s ≫ pullback.snd ν π, ⟨by rw [← Category.assoc, hs1, pullback.lift_snd], ?_⟩, ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs2, Category.id_comp]
  · rintro k ⟨hk1, hk2⟩
    have hk : pullback.lift (𝟙 P) k (by rw [Category.id_comp, hk2]) = s :=
      hsu _ ⟨pullback.hom_ext
        (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hk1]),
        pullback.lift_fst _ _ _⟩
    rw [← hk, pullback.lift_snd]

/-! ### Part (1) of Stacks 0ABP, reduced to integral closedness -/

/-- **The base change of a factorization along an étale morphism is a relative normalization,
as soon as `𝒪_{X'}` is integrally closed in `f'_* 𝒪_Y`.**

Let `f' : Y ⟶ X'` and `ν : X' ⟶ X` be morphisms of algebraic spaces with `ν` integral, let
`g : W ⟶ X` be étale, and let `P = W ×_X X'` and `Y' = P ×_{X'} Y`.  If the structure sheaf of
`X'` is integrally closed in `f'_* 𝒪_Y`, then `Y' ⟶ P ⟶ W` is a relative normalization of
`Y' ⟶ W`.

Integral closedness passes from `X'` to `P` along the étale `P ⟶ X'`: by
`AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeIso` (Stacks 03LX for the direct image
of the structure sheaf, as algebras) the direct image along `Y' ⟶ P` is the étale restriction of
`f'_* 𝒪_Y`, and integral closedness is étale local.  So `P` is the normalization of itself in
`Y'` (`AlgebraicGeometry.Space.isRelativeNormalization_id_of_isIntegrallyClosed`), and, `P ⟶ W`
being integral as a base change of `ν`, the normalization of `W` in `Y'`
(`AlgebraicGeometry.Space.IsRelativeNormalization.comp_of_id`). -/
theorem isRelativeNormalization_of_isPullback_of_isEtale
    {X Y X' W P Y' : AlgebraicSpaces B S hS} (f' : Y ⟶ X') (ν : X' ⟶ X)
    (hν : IsIntegralHom B S hS ν.hom)
    (hcl : (pushforwardAlgebra B S hS (Over.mk f')).IsIntegrallyClosed)
    (g : W ⟶ X) (hg : IsEtale B S hS g.hom) (i : P ⟶ X') (νP : P ⟶ W)
    (hP : IsPullback i νP ν g) (j : Y' ⟶ Y) (fP : Y' ⟶ P) (hY : IsPullback j fP f' i) :
    IsRelativeNormalization B S hS (fP ≫ νP).hom νP.hom fP.hom := by
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS νP i g ν hP.flip hg
  have hclP : (pushforwardAlgebra B S hS (Over.mk fP)).IsIntegrallyClosed :=
    AlgebraSheaf.IsIntegrallyClosed.of_iso
      (pushforwardAlgebraEtaleBaseChangeIso B S hS j fP f' i hY hi).symm
      (hcl.etaleAlgebraRestriction B S hS i hi)
  have hPp : IsPullback i.hom νP.hom ν.hom g.hom := hP.map (ObjectProperty.ι _)
  exact IsRelativeNormalization.comp_of_id B S hS
    (isRelativeNormalization_id_of_isIntegrallyClosed B S hS fP hclP)
    (isIntegralHom_of_isPullback B S hS hPp hν) P.2 W.2

end AlgebraicGeometry.Space

end
