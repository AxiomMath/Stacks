module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.DiagonalFamily
public import StacksFrontier.AlgebraicGeometry.Scheme.AutomorphismFunctor

/-!
# The automorphism scheme of a pointed curve from the moduli stack of elliptic curves

Let `X` be a scheme over a field `k` with a rational point `p`, let `E₁ = (X, p)` over `Spec k`
and let `E₂` be the diagonal family `X ×_k X ⟶ X` over `X`. A `T`-point of the fibre product
`P = Spec k ×_{𝓜₁,₁} X` is a triple `(a, a', α)` with `a : T ⟶ Spec k`, `a' : T ⟶ X` and an
isomorphism `α : X ×_{k,a} T ≅ X ×_{k,a'f} T` of pointed families over `T` from the section `p`
to the section `(a', 𝟙)`. Imposing `a = a' ≫ f`, that is pulling `P ⟶ Spec k × X` back along the
graph `X ⟶ Spec k × X` of `f`, leaves the pairs `(a', α)`: an automorphism `ψ` of `X_T` over `T`
together with `a' = ψ ∘ p_T`, and `a'` is determined by `ψ`. So the closed subscheme
`G = P ×_{Spec k × X} X` of `P` represents the automorphism functor `T ↦ Aut_T(X_T)` of `X` over
`k`.

## Main definitions

* `AlgebraicGeometry.GenusOne.autSchemeOver`: the scheme `G = P ×_{Spec k × X} X`, as a scheme
  over `k`.
* `AlgebraicGeometry.GenusOne.comparisonToAut`: the automorphism of `X_T` attached to a triple
  `(a, a', α)` with `a = a' ≫ f` the structure morphism of `T`.
* `AlgebraicGeometry.GenusOne.autToComparison`: the triple attached to an automorphism.
* `AlgebraicGeometry.GenusOne.autFunctorRepresentableBy`: **`G` represents the automorphism
  functor of `X` over `k`.**

## Implementation notes

The fibre product `P` is an arbitrary scheme representing the triples, given by
`AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons`; nothing in this file uses that
the families are elliptic curves, which matters only for the existence of `P` and for its
properties. The restriction of `E₂` along `a'` is identified with `X ×_k T` by
`AlgebraicGeometry.GenusOne.diagonalFamilyPullbackIso`, and the restriction of `E₁` along `a` with
`X ×_k T` along the equality `a = T ⟶ Spec k` by
`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.pullbackIsoOfEq`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

variable {S T : Scheme.{u}} (E : PointedFamily S)

/-- The isomorphism `E.pullbackIsoOfEq h` is compatible with the projections to the total space of
`E`. -/
@[reassoc (attr := simp)]
theorem pullbackIsoOfEq_hom_fst {a b : T ⟶ S} (h : a = b) :
    (E.pullbackIsoOfEq h).hom ≫ Limits.pullback.fst E.map b = Limits.pullback.fst E.map a := by
  subst h; simp

/-- The isomorphism `E.pullbackIsoOfEq h` is compatible with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem pullbackIsoOfEq_hom_snd {a b : T ⟶ S} (h : a = b) :
    (E.pullbackIsoOfEq h).hom ≫ Limits.pullback.snd E.map b = Limits.pullback.snd E.map a := by
  subst h; simp

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

namespace AlgebraicGeometry.GenusOne

open ModuliEllipticCurves

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-! ### Triples and automorphisms -/

variable {f p hp} in
/-- The automorphism of `X_T = X ×_k T` over `T` attached to a triple `(a, a', α)` for `(X, p)`
and the diagonal family with `a` the structure morphism `t` of `T` and `a' ≫ f = t`. -/
def comparisonToAut {T : Over (Spec (.of k))}
    (x : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left)
    (h₁ : x.fst = T.hom) (h₂ : x.snd ≫ f = T.hom) :
    (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f) where
  hom := Over.homMk (((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫ x.iso.hom ≫
      (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom) (by
    change _ ≫ ((pointedFamily f p hp).pullback T.hom).map =
      ((pointedFamily f p hp).pullback T.hom).map
    rw [Category.assoc, Category.assoc, diagonalFamilyPullbackIso_hom_snd]
    change _ ≫ x.iso.hom ≫ ((diagonalFamily f).pullback x.snd).map = _
    rw [x.iso_map, PointedFamily.pullbackIsoOfEq_inv, PointedFamily.pullbackIsoOfEq_hom_map])
  inv := Over.homMk ((diagonalFamilyPullbackIso f x.snd T.hom h₂).inv ≫ x.iso.inv ≫
      ((pointedFamily f p hp).pullbackIsoOfEq h₁).hom) (by
    change _ ≫ ((pointedFamily f p hp).pullback T.hom).map =
      ((pointedFamily f p hp).pullback T.hom).map
    rw [Category.assoc, Category.assoc, PointedFamily.pullbackIsoOfEq_hom_map,
      Comparison.iso_inv_map]
    exact diagonalFamilyPullbackIso_inv_snd f x.snd T.hom h₂)
  hom_inv_id := by
    ext1
    change (((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫ x.iso.hom ≫
      (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom) ≫
      ((diagonalFamilyPullbackIso f x.snd T.hom h₂).inv ≫ x.iso.inv ≫
      ((pointedFamily f p hp).pullbackIsoOfEq h₁).hom) = 𝟙 (pullback f T.hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  inv_hom_id := by
    ext1
    change ((diagonalFamilyPullbackIso f x.snd T.hom h₂).inv ≫ x.iso.inv ≫
      ((pointedFamily f p hp).pullbackIsoOfEq h₁).hom) ≫
      (((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫ x.iso.hom ≫
      (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom) = 𝟙 (pullback f T.hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The underlying morphism of `comparisonToAut x h₁ h₂` is the composite of the identification of
`X ×_k T` with the restriction of `(X, p)` along `x.fst`, the isomorphism `x.iso`, and the
identification of the restriction of the diagonal family along `x.snd` with `X ×_k T`. -/
@[simp]
theorem comparisonToAut_hom_left {T : Over (Spec (.of k))}
    (x : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left)
    (h₁ : x.fst = T.hom) (h₂ : x.snd ≫ f = T.hom) :
    (comparisonToAut x h₁ h₂).hom.left = ((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫
      x.iso.hom ≫ (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom :=
  rfl

/-- The rational point `p_T` of `X_T` over `T` induced by `p`. -/
abbrev basePointAt (T : Over (Spec (.of k))) : T.left ⟶ pullback f T.hom :=
  ((pointedFamily f p hp).pullback T.hom).zero

/-- The morphism `T ⟶ X` attached to an automorphism `ψ` of `X_T`: the image `ψ ∘ p_T` of the
base point, read in `X`. -/
def autPoint {T : Over (Spec (.of k))}
    (ψ : (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) :
    T.left ⟶ X :=
  basePointAt f p hp T ≫ ψ.hom.left ≫ pullback.fst f T.hom

/-- The composite of `autPoint f p hp ψ` with `f` is the structure morphism of `T`. -/
theorem autPoint_comp {T : Over (Spec (.of k))}
    (ψ : (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) :
    autPoint f p hp ψ ≫ f = T.hom := by
  have hψ : ψ.hom.left ≫ pullback.snd f T.hom = pullback.snd f T.hom := Over.w ψ.hom
  rw [autPoint, Category.assoc, Category.assoc, pullback.condition, reassoc_of% hψ]
  simp [basePointAt]

/-- The triple attached to an automorphism `ψ` of `X_T` over `T`: the structure morphism of `T`,
the image `ψ ∘ p_T` of the base point, and `ψ` itself. -/
def autToComparison {T : Over (Spec (.of k))}
    (ψ : (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) :
    Comparison (pointedFamily f p hp) (diagonalFamily f) T.left where
  fst := T.hom
  snd := autPoint f p hp ψ
  iso := (Over.forget _).mapIso ψ ≪≫
    (diagonalFamilyPullbackIso f (autPoint f p hp ψ) T.hom (autPoint_comp f p hp ψ)).symm
  iso_map := by
    have hψ : ψ.hom.left ≫ pullback.snd f T.hom = pullback.snd f T.hom := Over.w ψ.hom
    change (ψ.hom.left ≫ (diagonalFamilyPullbackIso f (autPoint f p hp ψ) T.hom
      (autPoint_comp f p hp ψ)).inv) ≫ pullback.snd (pullback.snd f f) _ = pullback.snd f T.hom
    rw [Category.assoc, diagonalFamilyPullbackIso_inv_snd, hψ]
  zero_iso := by
    have hψ : ψ.hom.left ≫ pullback.snd f T.hom = pullback.snd f T.hom := Over.w ψ.hom
    change basePointAt f p hp T ≫ ψ.hom.left ≫ (diagonalFamilyPullbackIso f (autPoint f p hp ψ)
      T.hom (autPoint_comp f p hp ψ)).inv = _
    rw [← cancel_mono (diagonalFamilyPullbackIso f (autPoint f p hp ψ) T.hom
      (autPoint_comp f p hp ψ)).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, zero_diagonalFamilyPullbackIso_hom]
    refine pullback.hom_ext (f := f) (g := T.hom) ?_ ?_
    · simp [autPoint]
    · rw [Category.assoc, hψ]
      simp [basePointAt]

/-! ### The two constructions are inverse -/

/-- For `a' = a`, the identifications of `X ×_k T` with the restrictions of the diagonal family
along `a` and along `a'` differ by `pullbackIsoOfEq`. -/
theorem diagonalFamilyPullbackIso_hom_inv_pullbackIsoOfEq {T : Scheme.{u}} {a a' : T ⟶ X}
    (t : T ⟶ Spec (.of k)) (ha : a ≫ f = t) (ha' : a' ≫ f = t) (h : a' = a) :
    (diagonalFamilyPullbackIso f a t ha).hom ≫ (diagonalFamilyPullbackIso f a' t ha').inv ≫
      ((diagonalFamily f).pullbackIsoOfEq h).hom = 𝟙 _ := by
  subst h
  simp

/-- The automorphism attached to the triple of an automorphism `ψ` of `X_T` is `ψ`. -/
theorem comparisonToAut_autToComparison {T : Over (Spec (.of k))}
    (ψ : (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) :
    comparisonToAut (autToComparison f p hp ψ) rfl (autPoint_comp f p hp ψ) = ψ := by
  apply Iso.ext
  ext1
  show ((pointedFamily f p hp).pullbackIsoOfEq rfl).inv ≫ (ψ.hom.left ≫
    (diagonalFamilyPullbackIso f _ T.hom (autPoint_comp f p hp ψ)).inv) ≫
    (diagonalFamilyPullbackIso f _ T.hom (autPoint_comp f p hp ψ)).hom = ψ.hom.left
  rw [PointedFamily.pullbackIsoOfEq_inv, PointedFamily.pullbackIsoOfEq_self_hom,
    Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The image of the base point under the automorphism attached to a triple `x`, read in `X`, is
the morphism `x.snd`. -/
theorem autPoint_comparisonToAut {T : Over (Spec (.of k))}
    (x : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left)
    (h₁ : x.fst = T.hom) (h₂ : x.snd ≫ f = T.hom) :
    autPoint f p hp (comparisonToAut x h₁ h₂) = x.snd := by
  show basePointAt f p hp T ≫ (((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫ x.iso.hom ≫
    (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom) ≫ pullback.fst f T.hom = x.snd
  rw [PointedFamily.pullbackIsoOfEq_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (basePointAt f p hp T), PointedFamily.zero_pullbackIsoOfEq_hom,
    ← Category.assoc _ x.iso.hom, x.zero_iso, zero_diagonalFamilyPullbackIso_hom_assoc,
    pullback.lift_fst]

/-- The triple attached to the automorphism of a triple `x` is `x`. -/
theorem autToComparison_comparisonToAut {T : Over (Spec (.of k))}
    (x : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left)
    (h₁ : x.fst = T.hom) (h₂ : x.snd ≫ f = T.hom) :
    autToComparison f p hp (comparisonToAut x h₁ h₂) = x := by
  refine Comparison.ext_of_eq h₁.symm (autPoint_comparisonToAut f p hp x h₁ h₂) ?_
  show ((((pointedFamily f p hp).pullbackIsoOfEq h₁).inv ≫ x.iso.hom ≫
    (diagonalFamilyPullbackIso f x.snd T.hom h₂).hom) ≫
    (diagonalFamilyPullbackIso f (autPoint f p hp (comparisonToAut x h₁ h₂)) T.hom
      (autPoint_comp f p hp _)).inv) ≫
    ((diagonalFamily f).pullbackIsoOfEq (autPoint_comparisonToAut f p hp x h₁ h₂)).hom =
    ((pointedFamily f p hp).pullbackIsoOfEq h₁.symm).hom ≫ x.iso.hom
  simp only [Category.assoc]
  rw [diagonalFamilyPullbackIso_hom_inv_pullbackIsoOfEq, Category.comp_id,
    PointedFamily.pullbackIsoOfEq_inv]

/-- Equal triples have equal attached automorphisms. -/
theorem comparisonToAut_congr {T : Over (Spec (.of k))}
    {x y : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left} (hxy : x = y)
    (h₁ : x.fst = T.hom) (h₂ : x.snd ≫ f = T.hom) (h₁' : y.fst = T.hom)
    (h₂' : y.snd ≫ f = T.hom) : comparisonToAut x h₁ h₂ = comparisonToAut y h₁' h₂' := by
  subst hxy
  rfl

/-- **Naturality of the automorphism attached to a triple.** If the triple `x'` over `T` is the
base change of the triple `x` over `T'` along `h : T ⟶ T'`, the automorphism attached to `x'` is
the base change of the one attached to `x`, as tested on the projection to `X`. -/
theorem comparisonToAut_baseChange {T T' : Over (Spec (.of k))} {h : T ⟶ T'}
    {x : Comparison (pointedFamily f p hp) (diagonalFamily f) T'.left}
    {x' : Comparison (pointedFamily f p hp) (diagonalFamily f) T.left}
    (hb : x.IsBaseChange h.left x') (h₁ : x.fst = T'.hom) (h₂ : x.snd ≫ f = T'.hom)
    (h₁' : x'.fst = T.hom) (h₂' : x'.snd ≫ f = T.hom) :
    (comparisonToAut x' h₁' h₂').hom.left ≫ pullback.fst f T.hom =
      Scheme.baseChangeMap (Over.mk f) h ≫ (comparisonToAut x h₁ h₂).hom.left ≫
        pullback.fst f T'.hom := by
  obtain ⟨hf, hs, hiso⟩ := hb
  rw [comparisonToAut_hom_left, comparisonToAut_hom_left]
  simp only [Category.assoc, diagonalFamilyPullbackIso_hom_fst]
  have k₁ : x'.iso.hom ≫ pullback.fst (pullback.snd f f) x'.snd =
      (pointedFamily f p hp).pullbackMap h.left hf ≫ x.iso.hom ≫
        pullback.fst (pullback.snd f f) x.snd := by
    rw [← (diagonalFamily f).pullbackMap_fst h.left hs, ← Category.assoc, hiso, Category.assoc]
  rw [reassoc_of% k₁]
  have k₂ : ((pointedFamily f p hp).pullbackIsoOfEq h₁').inv ≫
      (pointedFamily f p hp).pullbackMap h.left hf =
      Scheme.baseChangeMap (Over.mk f) h ≫ ((pointedFamily f p hp).pullbackIsoOfEq h₁).inv := by
    rw [PointedFamily.pullbackIsoOfEq_inv, PointedFamily.pullbackIsoOfEq_inv]
    refine pullback.hom_ext (f := f) (g := x.fst) ?_ ?_
    · rw [Category.assoc, Category.assoc, PointedFamily.pullbackMap_fst,
        PointedFamily.pullbackIsoOfEq_hom_fst, PointedFamily.pullbackIsoOfEq_hom_fst]
      exact (Scheme.baseChangeMap_fst (Over.mk f) h).symm
    · rw [Category.assoc, Category.assoc, PointedFamily.pullbackMap_snd,
        PointedFamily.pullbackIsoOfEq_hom_snd_assoc, PointedFamily.pullbackIsoOfEq_hom_snd]
      exact (Scheme.baseChangeMap_snd (Over.mk f) h).symm
  rw [reassoc_of% k₂]

/-! ### The automorphism scheme -/

section Representability

variable {P : Scheme.{u}} (r : RepresentsComparisons (pointedFamily f p hp) (diagonalFamily f) P)

/-- The morphism `P ⟶ Spec k × X` recording the two morphisms of a triple. -/
abbrev comparisonProjection : P ⟶ Spec (.of k) ⨯ X :=
  prod.lift (r.homEquiv P (𝟙 P)).fst (r.homEquiv P (𝟙 P)).snd

/-- The graph `X ⟶ Spec k × X` of `f`. -/
abbrev graphOf : X ⟶ Spec (.of k) ⨯ X := prod.lift f (𝟙 X)

/-- **The automorphism scheme** `G = P ×_{Spec k × X} X` of `X` over `k`: the closed subscheme of
the fibre product `P = Spec k ×_{𝓜₁,₁} X` where the morphism to `Spec k` is the composite of the
morphism to `X` with `f`, as a scheme over `k` through `X`. -/
abbrev autSchemeOver : Over (Spec (.of k)) :=
  Over.mk (pullback.snd (comparisonProjection f p hp r) (graphOf f) ≫ f)

variable {f p hp r}

/-- On `G`, the morphism to `Spec k` of the universal triple is the composite of the projection
`G ⟶ X` with `f`. -/
theorem fst_comparisonProjection_eq :
    pullback.fst (comparisonProjection f p hp r) (graphOf f) ≫ (r.homEquiv P (𝟙 P)).fst =
      pullback.snd (comparisonProjection f p hp r) (graphOf f) ≫ f := by
  have h := pullback.condition (f := comparisonProjection f p hp r) (g := graphOf f) =≫ prod.fst
  simpa using h

/-- On `G`, the morphism to `X` of the universal triple is the projection `G ⟶ X`. -/
theorem snd_comparisonProjection_eq :
    pullback.fst (comparisonProjection f p hp r) (graphOf f) ≫ (r.homEquiv P (𝟙 P)).snd =
      pullback.snd (comparisonProjection f p hp r) (graphOf f) := by
  have h := pullback.condition (f := comparisonProjection f p hp r) (g := graphOf f) =≫ prod.snd
  simpa using h

/-- For a `T`-point `g` of `G` over `k`, the morphism to `Spec k` of the triple attached to `g` is
the structure morphism of `T`. -/
theorem fst_homEquiv_autScheme {T : Over (Spec (.of k))} (g : T ⟶ autSchemeOver f p hp r) :
    (r.homEquiv T.left (g.left ≫ pullback.fst _ _)).fst = T.hom := by
  rw [r.fst_homEquiv, Category.assoc, fst_comparisonProjection_eq]
  exact Over.w g

/-- For a `T`-point `g` of `G` over `k`, the morphism to `X` of the triple attached to `g` is the
composite of `g` with the projection `G ⟶ X`. -/
theorem snd_homEquiv_autScheme {T : Over (Spec (.of k))} (g : T ⟶ autSchemeOver f p hp r) :
    (r.homEquiv T.left (g.left ≫ pullback.fst _ _)).snd = g.left ≫ pullback.snd _ _ := by
  rw [r.snd_homEquiv, Category.assoc, snd_comparisonProjection_eq]

/-- For a `T`-point `g` of `G` over `k`, the morphism to `X` of the triple attached to `g`,
composed with `f`, is the structure morphism of `T`. -/
theorem snd_homEquiv_autScheme_comp {T : Over (Spec (.of k))} (g : T ⟶ autSchemeOver f p hp r) :
    (r.homEquiv T.left (g.left ≫ pullback.fst _ _)).snd ≫ f = T.hom := by
  rw [snd_homEquiv_autScheme, Category.assoc]
  exact Over.w g

/-- The `T`-point of `P` given by the triple of an automorphism `ψ` maps to `Spec k × X` as the
composite of `autPoint f p hp ψ` with the graph of `f`. -/
theorem comparisonProjection_symm_autToComparison {T : Over (Spec (.of k))}
    (ψ : (Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) :
    (r.homEquiv T.left).symm (autToComparison f p hp ψ) ≫ comparisonProjection f p hp r =
      autPoint f p hp ψ ≫ graphOf f := by
  refine prod.hom_ext ?_ ?_
  · simp only [Category.assoc, prod.lift_fst, ← r.fst_homEquiv, Equiv.apply_symm_apply,
      autPoint_comp]
    rfl
  · simp only [Category.assoc, prod.lift_snd, ← r.snd_homEquiv, Equiv.apply_symm_apply,
      Category.comp_id]
    rfl

variable (f p hp r)

/-- The bijection between the `T`-points of the automorphism scheme over `k` and the
automorphisms of `X_T` over `T`. -/
def autSchemeHomEquiv (T : Over (Spec (.of k))) :
    (T ⟶ autSchemeOver f p hp r) ≃
      ((Over.pullback T.hom).obj (Over.mk f) ≅ (Over.pullback T.hom).obj (Over.mk f)) where
  toFun g := comparisonToAut (r.homEquiv T.left (g.left ≫ pullback.fst _ _))
    (fst_homEquiv_autScheme g) (snd_homEquiv_autScheme_comp g)
  invFun ψ := Over.homMk (pullback.lift ((r.homEquiv T.left).symm (autToComparison f p hp ψ))
    (autPoint f p hp ψ) (comparisonProjection_symm_autToComparison ψ)) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ f = T.hom
      rw [pullback.lift_snd_assoc]
      exact autPoint_comp f p hp ψ)
  left_inv g := by
    dsimp only
    ext1
    refine pullback.hom_ext ?_ ?_
    · refine (pullback.lift_fst _ _ _).trans ?_
      rw [autToComparison_comparisonToAut, Equiv.symm_apply_apply]
    · refine (pullback.lift_snd _ _ _).trans ?_
      rw [autPoint_comparisonToAut, snd_homEquiv_autScheme]
  right_inv ψ := by
    dsimp only
    refine (comparisonToAut_congr f p hp ?_ _ _ rfl (autPoint_comp f p hp ψ)).trans
      (comparisonToAut_autToComparison f p hp ψ)
    exact (congrArg (r.homEquiv T.left) (pullback.lift_fst _ _ _)).trans
      (Equiv.apply_symm_apply _ _)

/-- **The automorphism scheme represents the automorphism functor.** For every `k`-scheme `T`,
the `T`-points of `G` over `k` are the automorphisms of `X_T = X ×_k T` over `T`, naturally in
`T`. -/
def autFunctorRepresentableBy :
    (Scheme.autFunctor (Over.mk f)).RepresentableBy (autSchemeOver f p hp r) where
  homEquiv {T} := autSchemeHomEquiv f p hp r T
  homEquiv_comp {T T'} h g := by
    apply Iso.ext
    apply Scheme.endo_ext
    have hx : r.homEquiv T.left ((h ≫ g).left ≫ pullback.fst _ _) =
        r.homEquiv T.left (h.left ≫ g.left ≫ pullback.fst _ _) := by
      rw [Over.comp_left, Category.assoc]
    have h₁ : (r.homEquiv T.left (h.left ≫ g.left ≫ pullback.fst _ _)).fst = T.hom :=
      hx ▸ fst_homEquiv_autScheme (h ≫ g)
    have h₂ : (r.homEquiv T.left (h.left ≫ g.left ≫ pullback.fst _ _)).snd ≫ f = T.hom :=
      hx ▸ snd_homEquiv_autScheme_comp (h ≫ g)
    change (comparisonToAut (r.homEquiv T.left ((h ≫ g).left ≫ pullback.fst _ _)) _ _).hom.left ≫
      _ = (Scheme.endBaseChange (Over.mk f) h (comparisonToAut
        (r.homEquiv T'.left (g.left ≫ pullback.fst _ _)) _ _).hom).left ≫ _
    rw [Scheme.endBaseChange_left_fst, comparisonToAut_congr f p hp hx _ _ h₁ h₂]
    exact comparisonToAut_baseChange f p hp (r.naturality h.left (g.left ≫ pullback.fst _ _))
      _ _ _ _

end Representability

end AlgebraicGeometry.GenusOne
