module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedFamilies
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteOpenSubfunctorGluing

/-!
# The normalized subfunctor of the Picard functor of a curve is an open of `Hilb^g`

Let `X` be a geometrically irreducible smooth projective curve of genus `g` over a field `k` with
a rational point `σ`. The subfunctor `F ⊂ Pic_{X/k}` of points whose fibres have `H¹ = 0` and
`dim H⁰ = 1` ([Stacks, Tag 0B9V], in fibrewise form) is represented by an open subscheme `W` of
any scheme `H` representing the degree-`g` Hilbert functor of `X`: `W` is the open over which
the class of the universal divisor is normalized, and `h_W ≅ F` sends a `T`-point of `W`, a
degree-`g` family `D` on `X_T`, to the class of `𝒪(D)` ([Stacks, Tag 0B9X]).

## Main results

* `Stacks.PicardFunctor.familyClass`: the point `[𝒪(D)]` of the Picard functor of a family `D`.
* `Stacks.PicardFunctor.familyClass_injective`: injectivity on normalized points.
* `Stacks.PicardFunctor.exists_familyClass_eq_map`: local surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor divisorSheaf invertibleSheaf')
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.PicardCurve

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
include σ hσ in
/-- **The hypothesis of [Stacks, Tag 0B9N] for a pointed smooth projective curve**
([Stacks, Tag 0B9U]). -/
theorem isIso_c_of_isCurve (U : BigFppfOver B (Spec (.of k)) hk) :
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c :=
  isIso_c_baseChange_of_isCurve_of_section (B.inclusion.map f) σ hσ (B.inclusion.map U.hom)

/-- The point `[𝒪(D)]` of the Picard functor of a degree-`d` family of divisors `D` on `X_T`. -/
abbrev familyClass {d : ℕ} (T : BigFppfOver B (Spec (.of k)) hk)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) : (picardFunctor B hX hk f).obj (op T) :=
  (toPicardFunctor B hX hk f).app (op T) D.picardClass

/-- The normalized subfunctor of a pointed curve. -/
abbrev curveNormalized : Subfunctor (picardFunctor B hX hk f) :=
  normalizedSubfunctor B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
/-- The fibre rank of the point `toPicardFunctorHom x` of the Picard functor is the fibre rank
`classFibreRank` of the class `x`. -/
theorem fibreRank_eq (T : BigFppfOver B (Spec (.of k)) hk) (x : picardAt B hX hk f T)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) (n : ℕ) :
    fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T
      (toPicardFunctorHom B hX hk f T x) t n = classFibreRank (baseChangeProj B hX hk f T) x t n :=
  fibreRank_toPicardFunctorHom B hX hk f σ hσ _ T x t n

omit [GeometricallyIrreducible (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] in
include B hX hk f in
/-- A two-affine cover of the curve. -/
theorem exists_cover : ∃ U : Stacks.TwoAffineCech.Cover.{u} → X.Opens,
    (⊤ : X.Opens) = ⨆ i, U i ∧ ∀ i, IsAffineOpen (U i) :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  Stacks.TwoAffineCech.exists_cover_isAffineOpen X (topologicalKrullDim_le_one_of_isCurve B hX hk f)

/-- The fibre ranks `(h¹, h⁰) = (0, 1)` of a class `x` whose point of the Picard functor is
normalized. -/
private theorem classFibreRank_eq_of_mem (f : B.obj hX ⟶ B.obj hk)
    [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
    [IsProjectiveVariety k (B.inclusion.map f)] {σ : Spec (.of k) ⟶ X}
    {hσ : σ ≫ B.inclusion.map f = 𝟙 _} (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T)
    (hx : toPicardFunctorHom B hX hk f T x ∈ (curveNormalized B hX hk f σ hσ).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    classFibreRank (baseChangeProj B hX hk f T) x t 1 = 0 ∧
      classFibreRank (baseChangeProj B hX hk f T) x t 0 = 1 := by
  simpa only [fibreRank_eq B hX hk f σ hσ T x t] using hx t

omit [GeometricallyIrreducible (B.inclusion.map f)] in
include σ hσ in
/-- **Injectivity on normalized points**: two degree-`d` families of divisors on `X_T` with the
same normalized class in the Picard functor are equal. -/
theorem familyClass_injective {d : ℕ} (T : BigFppfOver B (Spec (.of k)) hk)
    (D₁ D₂ : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d)
    (h : familyClass B hX hk f T D₁ = familyClass B hX hk f T D₂)
    (hmem : familyClass B hX hk f T D₁ ∈ (curveNormalized B hX hk f σ hσ).obj (op T)) :
    D₁ = D₂ := by
  obtain ⟨U, hU, hUaff⟩ := exists_cover B hX hk f
  have hD₁ := D₁.isEffectiveCartierDivisor_ideal
  have hD₂ := D₂.isEffectiveCartierDivisor_ideal
  obtain ⟨N, hN⟩ := exists_eq_add_of_toPicardFunctorHom_eq B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) T h
  have hfib : ∀ t n, Module.finrank ((B.inclusion.obj T.left).residueField t)
      (fibreCohomology (baseChangeProj B hX hk f T) (divisorSheaf D₁.ideal) t n) =
        classFibreRank (baseChangeProj B hX hk f T) D₁.picardClass t n := fun t n =>
    (classFibreRank_picardClass (baseChangeProj B hX hk f T) (invertibleSheaf' D₁.ideal)
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard D₁.ideal) t n).symm
  have hcls := classFibreRank_eq_of_mem B hX hk f T D₁.picardClass hmem
  exact eq_of_picardClass_eq_add (B.inclusion.map f) U hU hUaff (B.inclusion.map T.hom) D₁ D₂ N hN
    (fun t => (hfib t 1).trans (hcls t).1) (fun t => (hfib t 0).trans (hcls t).2)

include σ hσ in
/-- **Local surjectivity**: a normalized point of the Picard functor is, near every point of the
base, the class of a degree-`g` family of divisors. -/
theorem exists_familyClass_eq_map (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T))
    (hξ : ξ ∈ (curveNormalized B hX hk f σ hσ).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    ∃ (O : T.left.obj.Opens) (_ : t ∈ O) (D : Stacks.Hilbert.HilbertFamily
        (Over.mk (B.inclusion.map f))
        (Over.mk (B.inclusion.map (BigFppfOver.openSubObj B _ hk T O).hom))
        (genus (B.inclusion.map f))),
      familyClass B hX hk f _ D =
        (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T O).op ξ := by
  obtain ⟨U, hU, hUaff⟩ := exists_cover B hX hk f
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) T ξ
  have hcls := classFibreRank_eq_of_mem B hX hk f T x hξ
  obtain ⟨O, ht, D, hD⟩ := exists_hilbertFamily_picardClass_eq (B.inclusion.map f) U hU hUaff
    (B.inclusion.map T.hom) x (fun t => (hcls t).1)
    (fun t => (hcls t).2) t
  exact ⟨O, ht, D,
    (congrArg ((toPicardFunctor B hX hk f).app (op (BigFppfOver.openSubObj B _ hk T O))) hD).trans
      (toPicardFunctor_app_naturality B hX hk f (BigFppfOver.openSubHom B _ hk T O) x)⟩

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **The Picard functor is separated for Zariski coverings by opens.** -/
theorem eq_of_map_openSubHom_eq (T : BigFppfOver B (Spec (.of k)) hk) {ι : Type u}
    (O : ι → T.left.obj.Opens) (hO : ∀ t, ∃ i, t ∈ O i)
    (ξ η : (picardFunctor B hX hk f).obj (op T))
    (h : ∀ i, (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T (O i)).op ξ =
      (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T (O i)).op η) : ξ = η := by
  have hS := BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B _ hk
    (fun i => BigFppfOver.openSubObj B _ hk T (O i)) T
    (fun i => BigFppfOver.openSubHom B _ hk T (O i))
    (fun i => by rw [AlgebraicGeometry.Space.openSubHom_toScheme]; infer_instance)
    (fun y => by
      obtain ⟨i, hi⟩ := hO y
      exact ⟨i, by rwa [AlgebraicGeometry.Space.openSubHom_toScheme, Scheme.Opens.range_ι]⟩)
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_picardFunctor B hX hk f)
  refine (hsh _ hS).isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨Z, a, b, ⟨i⟩, rfl⟩ := hg
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h i]

section Universal

variable (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f)))

/-- The class of the universal divisor in the Picard functor of a scheme representing the
degree-`g` Hilbert functor. -/
abbrev universalClass : (picardFunctor B hX hk f).obj (op H) :=
  familyClass B hX hk f H (hH.family (𝟙 _))

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The class of the family classified by a `T`-point of `H` is the restriction of the universal
class. -/
theorem familyClass_family {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ H) :
    familyClass B hX hk f T (hH.family (testMap B hk m)) =
      (picardFunctor B hX hk f).map m.op (universalClass B hX hk f H hH) := by
  rw [familyClass, ← Stacks.AbelMap.picardMap_universal B hX hk f H hH m]
  exact toPicardFunctor_app_naturality B hX hk f m _

omit [GeometricallyIrreducible (B.inclusion.map f)] in
include σ hσ in
/-- **Two `T`-points of `H` with the same normalized class are equal.** -/
theorem eq_of_map_universalClass_eq {T : BigFppfOver B (Spec (.of k)) hk} (m m' : T ⟶ H)
    (h : (picardFunctor B hX hk f).map m.op (universalClass B hX hk f H hH) =
      (picardFunctor B hX hk f).map m'.op (universalClass B hX hk f H hH))
    (hmem : (picardFunctor B hX hk f).map m.op (universalClass B hX hk f H hH) ∈
      (curveNormalized B hX hk f σ hσ).obj (op T)) : m = m' := by
  have hfam := familyClass_injective B hX hk f σ hσ T (hH.family (testMap B hk m))
    (hH.family (testMap B hk m'))
    (by rw [familyClass_family, familyClass_family, h])
    (by rwa [familyClass_family])
  exact BigFppfOver.map_toScheme_injective B _ hk
    (congrArg CommaMorphism.left (hH.family.injective hfam))

/-- The `T`-point of `H` classifying a family over a test scheme, as a morphism of the site. -/
def familyHom {T : BigFppfOver B (Spec (.of k)) hk}
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) (genus (B.inclusion.map f))) : T ⟶ H :=
  Over.homMk (B.inclusion.preimage (hH.family.symm D).left) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact Over.w (hH.family.symm D))

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The family classified by the `T`-point `familyHom D` of `H` is `D`. -/
theorem family_testMap_familyHom {T : BigFppfOver B (Spec (.of k)) hk}
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) (genus (B.inclusion.map f))) :
    hH.family (testMap B hk (familyHom B hX hk f H hH D)) = D := by
  have : testMap B hk (familyHom B hX hk f H hH D) = hH.family.symm D := by
    ext
    exact Functor.map_preimage B.inclusion _
  rw [this, Equiv.apply_symm_apply]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The Picard functor sends a composite `a ≫ b` to the composite of the maps along `b` and `a`. -/
theorem picardFunctor_map_comp_apply {T₁ T₂ T₃ : BigFppfOver B (Spec (.of k)) hk} (a : T₁ ⟶ T₂)
    (b : T₂ ⟶ T₃) (z : (picardFunctor B hX hk f).obj (op T₃)) :
    (picardFunctor B hX hk f).map (a ≫ b).op z =
      (picardFunctor B hX hk f).map a.op ((picardFunctor B hX hk f).map b.op z) := by
  rw [op_comp, Functor.map_comp_apply]

omit [GeometricallyIrreducible (B.inclusion.map f)] in
include σ hσ in
/-- Two `T`-points of `H`, on opens `O₁` and `O₂` of `T`, whose restrictions of the universal
class are the restrictions of a normalized point `ξ` agree on `O₁ ∩ O₂`. -/
theorem pullback_fst_map_eq_pullback_snd_map (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T))
    (hξ : ξ ∈ (curveNormalized B hX hk f σ hσ).obj (op T)) {O₁ O₂ : T.left.obj.Opens}
    (m₁ : BigFppfOver.openSubObj B _ hk T O₁ ⟶ H) (m₂ : BigFppfOver.openSubObj B _ hk T O₂ ⟶ H)
    (h₁ : (picardFunctor B hX hk f).map m₁.op (universalClass B hX hk f H hH) =
      (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T O₁).op ξ)
    (h₂ : (picardFunctor B hX hk f).map m₂.op (universalClass B hX hk f H hH) =
      (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T O₂).op ξ) :
    pullback.fst O₁.ι O₂.ι ≫ (BigFppfOver.toScheme B (Spec (.of k)) hk).map m₁ =
      pullback.snd O₁.ι O₂.ι ≫ (BigFppfOver.toScheme B (Spec (.of k)) hk).map m₂ := by
  have hc : B.Contains (pullback O₁.ι O₂.ι) :=
    B.contains_of_mono (pullback.fst O₁.ι O₂.ι) (BigFppfOver.contains_opens B T.left.property O₁)
  let Q : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (X := B.obj hc) (Y := B.obj hk)
      (pullback.fst O₁.ι O₂.ι ≫ O₁.ι ≫ T.hom.hom))
  let p₁ : Q ⟶ BigFppfOver.openSubObj B _ hk T O₁ :=
    Over.homMk (ObjectProperty.homMk (pullback.fst O₁.ι O₂.ι)) (by
      apply ObjectProperty.hom_ext
      rfl)
  let p₂ : Q ⟶ BigFppfOver.openSubObj B _ hk T O₂ :=
    Over.homMk (ObjectProperty.homMk (pullback.snd O₁.ι O₂.ι)) (by
      apply ObjectProperty.hom_ext
      change pullback.snd O₁.ι O₂.ι ≫ O₂.ι ≫ T.hom.hom = pullback.fst O₁.ι O₂.ι ≫ O₁.ι ≫ T.hom.hom
      exact (pullback.condition_assoc _).symm)
  have hsq : p₁ ≫ BigFppfOver.openSubHom B _ hk T O₁ = p₂ ≫ BigFppfOver.openSubHom B _ hk T O₂ := by
    apply BigFppfOver.map_toScheme_injective B _ hk
    change pullback.fst O₁.ι O₂.ι ≫ O₁.ι = pullback.snd O₁.ι O₂.ι ≫ O₂.ι
    exact pullback.condition
  have heq : (picardFunctor B hX hk f).map (p₁ ≫ m₁).op (universalClass B hX hk f H hH) =
      (picardFunctor B hX hk f).map (p₂ ≫ m₂).op (universalClass B hX hk f H hH) := by
    rw [picardFunctor_map_comp_apply, picardFunctor_map_comp_apply, h₁, h₂,
      ← picardFunctor_map_comp_apply, ← picardFunctor_map_comp_apply, hsq]
  have hmem : (picardFunctor B hX hk f).map (p₁ ≫ m₁).op (universalClass B hX hk f H hH) ∈
      (curveNormalized B hX hk f σ hσ).obj (op Q) := by
    rw [picardFunctor_map_comp_apply, h₁, ← picardFunctor_map_comp_apply]
    exact (curveNormalized B hX hk f σ hσ).map (p₁ ≫ BigFppfOver.openSubHom B _ hk T O₁).op hξ
  have h := congrArg (fun a => (BigFppfOver.toScheme B (Spec (.of k)) hk).map a)
    (eq_of_map_universalClass_eq B hX hk f σ hσ H hH (p₁ ≫ m₁) (p₂ ≫ m₂) heq hmem)
  simp only [Functor.map_comp] at h
  exact h

include σ hσ in
/-- **Every normalized point of the Picard functor is the restriction of the universal class**
along a `T`-point of `H`: the local families of divisors glue, by uniqueness. -/
theorem exists_map_universalClass_eq (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T))
    (hξ : ξ ∈ (curveNormalized B hX hk f σ hσ).obj (op T)) :
    ∃ m : T ⟶ H, (picardFunctor B hX hk f).map m.op (universalClass B hX hk f H hH) = ξ := by
  choose O hO D hD using exists_familyClass_eq_map B hX hk f σ hσ T ξ hξ
  have hmt : ∀ t, (picardFunctor B hX hk f).map (familyHom B hX hk f H hH (D t)).op
      (universalClass B hX hk f H hH) =
      (picardFunctor B hX hk f).map (BigFppfOver.openSubHom B _ hk T (O t)).op ξ := fun t => by
    rw [← familyClass_family, family_testMap_familyHom, hD]
  have hcompat : ∀ x y, pullback.fst (O x).ι (O y).ι ≫
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (familyHom B hX hk f H hH (D x)) =
      pullback.snd (O x).ι (O y).ι ≫
        (BigFppfOver.toScheme B (Spec (.of k)) hk).map (familyHom B hX hk f H hH (D y)) :=
    fun x y => pullback_fst_map_eq_pullback_snd_map B hX hk f σ hσ H hH T ξ hξ _ _ (hmt x) (hmt y)
  let 𝒰 : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).OpenCover :=
    { I₀ := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T, X t := (O t), f t := (O t).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨x, by rw [Scheme.Opens.range_ι]; exact hO x⟩, inferInstance⟩ }
  let g := 𝒰.glueMorphisms
    (fun t => (BigFppfOver.toScheme B (Spec (.of k)) hk).map (familyHom B hX hk f H hH (D t)))
    hcompat
  have hg : ∀ t, (O t).ι ≫ g =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (familyHom B hX hk f H hH (D t)) := fun t =>
    𝒰.ι_glueMorphisms _ hcompat t
  have hgw : g ≫ B.inclusion.map H.hom = B.inclusion.map T.hom := by
    refine 𝒰.hom_ext _ _ fun t => ?_
    change (O t).ι ≫ g ≫ B.inclusion.map H.hom = (O t).ι ≫ B.inclusion.map T.hom
    calc (O t).ι ≫ g ≫ B.inclusion.map H.hom = ((O t).ι ≫ g) ≫ B.inclusion.map H.hom :=
          (Category.assoc _ _ _).symm
      _ = B.inclusion.map ((familyHom B hX hk f H hH (D t)).left ≫ H.hom) := by
          rw [hg, B.inclusion.map_comp]
          rfl
      _ = (O t).ι ≫ B.inclusion.map T.hom := by
          rw [Over.w (familyHom B hX hk f H hH (D t))]
          rfl
  let m : T ⟶ H := Over.homMk (B.inclusion.preimage g) (by
    apply B.inclusion.map_injective
    rwa [Functor.map_comp, Functor.map_preimage])
  have hm : ∀ t, BigFppfOver.openSubHom B _ hk T (O t) ≫ m = familyHom B hX hk f H hH (D t) :=
    fun t => by
      apply BigFppfOver.map_toScheme_injective B _ hk
      change (O t).ι ≫ B.inclusion.map (B.inclusion.preimage g) = _
      rw [Functor.map_preimage, hg]
  refine ⟨m, eq_of_map_openSubHom_eq B hX hk f T O (fun t => ⟨t, hO t⟩) _ _ fun t => ?_⟩
  rw [← picardFunctor_map_comp_apply, hm, hmt]

/-- **The open `W ⊂ H` over which the universal class is normalized.** -/
def normalizedOpen : H.left.obj.Opens :=
  haveI := isSeparated_of_isCurve B hX hk f
  haveI := isNoetherian_of_isCurve B hX hk f
  normalizedLocus B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) H (universalClass B hX hk f H hH)

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- A `T`-point of `H` gives a normalized class exactly when it lands in `W`. -/
theorem map_universalClass_mem_iff {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ H) :
    (picardFunctor B hX hk f).map m.op (universalClass B hX hk f H hH) ∈
        (curveNormalized B hX hk f σ hσ).obj (op T) ↔
      ∀ t, B.inclusion.map m.left t ∈ normalizedOpen B hX hk f σ hσ H hH :=
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  map_mem_normalizedSubfunctor_iff B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) m (universalClass B hX hk f H hH)

/-- **`W` as an object of the site.** -/
abbrev normalizedHilbertOpen : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.openSubObj B _ hk H (normalizedOpen B hX hk f σ hσ H hH)

/-- The value at a `T`-point of `W` of the comparison `h_W ⟶ F`. -/
def normalizedHilbertPoint {T : BigFppfOver B (Spec (.of k)) hk}
    (a : T ⟶ normalizedHilbertOpen B hX hk f σ hσ H hH) :
    (curveNormalized B hX hk f σ hσ).toFunctor.obj (op T) :=
  ⟨(picardFunctor B hX hk f).map (a ≫ BigFppfOver.openSubHom B _ hk H _).op
      (universalClass B hX hk f H hH),
    (map_universalClass_mem_iff B hX hk f σ hσ H hH _).2 fun t => by
      change (BigFppfOver.toScheme B _ hk).map (a ≫ BigFppfOver.openSubHom B _ hk H _) t ∈ _
      rw [Functor.map_comp, AlgebraicGeometry.Space.openSubHom_toScheme]
      have h : (normalizedOpen B hX hk f σ hσ H hH).ι ((BigFppfOver.toScheme B _ hk).map a t) ∈
          Set.range (normalizedOpen B hX hk f σ hσ H hH).ι := Set.mem_range_self _
      rw [Scheme.Opens.range_ι] at h
      exact h⟩

/-- The comparison `h_W ⟶ F` is bijective at every `T`. -/
theorem normalizedHilbertPoint_bijective (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Bijective (normalizedHilbertPoint B hX hk f σ hσ H hH (T := T)) := by
  refine ⟨fun a₁ a₂ h => (AlgebraicGeometry.Space.mono_openSubHom B _ hk H _).right_cancellation
    _ _ (eq_of_map_universalClass_eq B hX hk f σ hσ H hH _ _ (congrArg Subtype.val h)
      (normalizedHilbertPoint B hX hk f σ hσ H hH a₁).2), fun ζ => ?_⟩
  obtain ⟨m, hm⟩ := exists_map_universalClass_eq B hX hk f σ hσ H hH T ζ.1 ζ.2
  have hW := (map_universalClass_mem_iff B hX hk f σ hσ H hH m).1 (hm ▸ ζ.2)
  have hrange : Set.range ⇑((BigFppfOver.toScheme B _ hk).map m) ⊆
      (normalizedOpen B hX hk f σ hσ H hH : Set H.left.obj) := Set.range_subset_iff.2 hW
  refine ⟨AlgebraicGeometry.Space.openSubObjLift B _ hk H _ m hrange, Subtype.ext ?_⟩
  change (picardFunctor B hX hk f).map
    (AlgebraicGeometry.Space.openSubObjLift B _ hk H _ m hrange ≫
      BigFppfOver.openSubHom B _ hk H _).op _ = _
  rw [AlgebraicGeometry.Space.openSubObjLift_comp_openSubHom, hm]

/-- **[Stacks, Tag 0B9X], fibrewise form: the normalized subfunctor `F ⊂ Pic_{X/k}` is
represented by the open `W` of the Hilbert scheme `H = Hilb^g_{X/k}`.** -/
def normalizedRepresentableBy :
    (curveNormalized B hX hk f σ hσ).toFunctor.RepresentableBy
      (normalizedHilbertOpen B hX hk f σ hσ H hH) where
  homEquiv := Equiv.ofBijective _ (normalizedHilbertPoint_bijective B hX hk f σ hσ H hH _)
  homEquiv_comp {T T'} g a := by
    apply Subtype.ext
    change (picardFunctor B hX hk f).map ((g ≫ a) ≫ BigFppfOver.openSubHom B _ hk H _).op _ =
      (picardFunctor B hX hk f).map g.op
        ((picardFunctor B hX hk f).map (a ≫ BigFppfOver.openSubHom B _ hk H _).op _)
    rw [Category.assoc, picardFunctor_map_comp_apply]

end Universal

end Stacks.PicardFunctor
