module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Cover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCharacterBaseChange

/-!
# Base change of the Artin–Schreier cover

For a morphism `φ : A → A'` of `𝔽_q`-algebras, the Artin–Schreier cover `t^q - t = φ(g)` of
`Spec A'` maps `𝔽_q`-equivariantly to the base change along `Spec A' → Spec A` of the cover
`t^q - t = g` of `Spec A`: `A[T]/(T^q - T - g) → A'[T]/(T^q - T - φ(g))`, `T ↦ T`. Hence the
character of `π₁(Spec A')` attached to `φ(g)` is the character attached to `g` composed with the
map of fundamental groups (`AlgebraicGeometry.TorsorCover.baseChange_character`,
`AlgebraicGeometry.TorsorCover.character_eq_of_hom`). For `A = A₀[t]` and `φ` the evaluation
`t ↦ c`, this identifies the restriction of `L_ψ(t·x)` to the fibre `t = c` with `L_ψ(c·x)`, the
fibres of the family of Laumon's Fourier transform.

## Main definitions

* `Stacks.ArtinSchreier.ringMap`: `A[T]/(T^q - T - g) → A'[T]/(T^q - T - φ(g))`.
* `Stacks.ArtinSchreier.coverBaseChangeHom`: the induced equivariant morphism of covers.

## Main results

* `Stacks.ArtinSchreier.torsorCover_character_map`: the character of `φ(g)` is the character of
  `g` composed with `π₁(Spec A') → π₁(Spec A)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')

/-- The image of the Artin–Schreier polynomial of `g` is that of `φ(g)`. -/
public theorem map_poly : (poly k g).map φ.toRingHom = poly k (φ g) := by
  simp [poly]

/-- **`A[T]/(T^q - T - g) → A'[T]/(T^q - T - φ(g))`, `T ↦ T`.** -/
public def ringMap : Ring k g →+* Ring k (φ g) :=
  AdjoinRoot.map φ.toRingHom (poly k g) (poly k (φ g)) (map_poly k g φ).symm.dvd

@[simp]
public theorem ringMap_root : ringMap k g φ (AdjoinRoot.root (poly k g)) =
    AdjoinRoot.root (poly k (φ g)) :=
  AdjoinRoot.map_root _ _ _ _

@[simp]
public theorem ringMap_algebraMap (r : A) :
    ringMap k g φ (algebraMap A (Ring k g) r) = algebraMap A' (Ring k (φ g)) (φ r) :=
  AdjoinRoot.map_of φ.toRingHom (poly k g) (poly k (φ g)) _ r

/-- `ringMap` intertwines the translations. -/
public theorem ringMap_comp_translate (a : k) :
    (ringMap k g φ).comp (translate k g a).toRingHom =
      (translate k (φ g) a).toRingHom.comp (ringMap k g φ) := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show AdjoinRoot.of (poly k g) r = algebraMap A (Ring k g) r from rfl, AlgHom.commutes,
      ringMap_algebraMap, AlgHom.commutes]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      translate_root, map_add, ringMap_root]
    congr 1
    rw [IsScalarTower.algebraMap_apply k A (Ring k g), ringMap_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

/-- The square `Spec A'[T]/(T^q - T - φ g) → Spec A[T]/(T^q - T - g)` over `Spec A' → Spec A`. -/
public theorem specMap_ringMap_comp_coverHom :
    Spec.map (CommRingCat.ofHom (ringMap k g φ)) ≫ coverHom k A g =
      coverHom k A' (φ g) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact ringMap_algebraMap k g φ r

/-- **The equivariant morphism from the Artin–Schreier cover of `φ(g)` to the base change of that
of `g`**, over `Spec A'`. -/
public def coverBaseChangeHom :
    cover k A' (φ g) ⟶ (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
      (cover k A g) :=
  MorphismProperty.Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom (ringMap k g φ)))
    (coverHom k A' (φ g)) (specMap_ringMap_comp_coverHom k g φ)) (pullback.lift_snd _ _ _)

public theorem coverTranslate_comp_coverBaseChangeHom (a : k) :
    coverTranslate k A' (φ g) a ≫ coverBaseChangeHom k g φ =
      coverBaseChangeHom k g φ ≫
        (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom φ.toRingHom))).map
          (coverTranslate k A g a) := by
  ext : 1
  have hf := pullback.lift_fst (Spec.map (CommRingCat.ofHom (ringMap k g φ)))
    (coverHom k A' (φ g)) (specMap_ringMap_comp_coverHom k g φ)
  have hs := pullback.lift_snd (Spec.map (CommRingCat.ofHom (ringMap k g φ)))
    (coverHom k A' (φ g)) (specMap_ringMap_comp_coverHom k g φ)
  have hb := finiteEtaleBaseChange_map_left_fst (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (coverTranslate k A g a)
  have hb' : ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom φ.toRingHom))).map
      (coverTranslate k A g a)).left ≫
        pullback.snd (cover k A g).hom (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      pullback.snd (cover k A g).hom (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    pullback.lift_snd _ _ _
  have ht : Spec.map (CommRingCat.ofHom (translate k (φ g) a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ringMap k g φ)) =
      Spec.map (CommRingCat.ofHom (ringMap k g φ)) ≫
        Spec.map (CommRingCat.ofHom (translate k g a).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ringMap_comp_translate k g φ a).symm
  apply pullback.hom_ext
  · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hf).trans (ht.trans
      ((congrArg (· ≫ _) hf).symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hb).symm.trans (Category.assoc _ _ _).symm)))))).trans rfl
  · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hs).trans
      ((MorphismProperty.Over.w (coverTranslate k A' (φ g) a)).trans (hs.symm.trans
        ((congrArg (_ ≫ ·) hb').symm.trans (Category.assoc _ _ _).symm)))))

/-- **The character of the Artin–Schreier cover of `φ(g)` is that of `g` composed with
`π₁(Spec A') → π₁(Spec A)`.** -/
public theorem torsorCover_character_map [ConnectedSpace (Spec (.of A))]
    [ConnectedSpace (Spec (.of A'))] (y : GeometricPoint (Spec (.of A')))
    (p₀ : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g)))
    (σ : EtaleFundamentalGroup (Spec (.of A')) y) :
    (torsorCover k A' (φ g)).character y p₀ σ =
      (torsorCover k A g).character (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))
        (finiteEtaleFiberProjection (Spec.map (CommRingCat.ofHom φ.toRingHom)) y (cover k A g)
          ((finiteEtaleFiberFunctor y).map (coverBaseChangeHom k g φ) p₀))
        (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y σ) :=
  (TorsorCover.character_eq_of_hom (T₁ := torsorCover k A' (φ g))
    (T₂ := (torsorCover k A g).baseChange (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (coverBaseChangeHom k g φ) (coverTranslate_comp_coverBaseChangeHom k g φ) y p₀ σ).trans
    (TorsorCover.baseChange_character (torsorCover k A g)
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) y _ σ)

end Stacks.ArtinSchreier
