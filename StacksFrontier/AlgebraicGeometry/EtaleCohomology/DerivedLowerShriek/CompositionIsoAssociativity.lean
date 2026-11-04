module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroCounitCube
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompactificationShriek

/-!
# The associativity of the composition isomorphisms of `Rf_!` ([Stacks, Tag 0F7K])

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` be separated morphisms of finite type of
quasi-compact and quasi-separated schemes. The two isomorphisms
`R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` built from the isomorphisms of [Stacks, Tag 0F7J] agree.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.ofFactorHom`: a morphism of compactifications over `S'`
  read over `S`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekHom_ofFactorHom`: the comparison of
  [Stacks, Tag 0F7I] along a morphism of compactifications pushed to `S` is the derived direct
  image of the comparison over `S'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S S' X : Scheme.{u}} {p' : X ⟶ S'} (q : S' ⟶ S) (p : X ⟶ S)

/-- A morphism of compactifications over `S'` read over `S`: for compactifications `j'`, `k'` of
`p'` over `S'` and structure morphisms `bj`, `bk` to `S` through `q`, the same ambient morphism is
a morphism of the compactifications `CompactificationOf.ofFactor` over `S`. -/
def ofFactorHom {j' k' : CompactificationOf (Over.mk p')} (ψ : j' ⟶ k') (bj : j'.space ⟶ S)
    [IsProper bj] (hbj : bj = j'.toBase ≫ q) (bk : k'.space ⟶ S) [IsProper bk]
    (hbk : bk = k'.toBase ≫ q) (hj : j'.immersion ≫ bj = p) (hk : k'.immersion ≫ bk = p) :
    ofFactor j'.immersion bj p hj ⟶ ofFactor k'.immersion bk p hk :=
  homOfSpaceMap _ _ (Hom.map (j := j') (k := k') ψ) (immersion_comp_map ψ)
    (by
      change Hom.map ψ ≫ bk = bj
      rw [hbj, hbk, ← Category.assoc, map_comp_toBase])

end AlgebraicGeometry.CompactificationOf

/-! ### The tower of compactifications `X̄ ⟶ Ȳ ⟶ Z̄` -/

namespace AlgebraicGeometry.CompactificationOf.Tower

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

include jY in
/-- `(g ≫ i_Z)`'s compactification `Ȳ`, read as a compactification of `g ≫ h` over `T`. -/
abbrev jgh : CompactificationOf (Over.mk (g ≫ h)) := compOver jh jY

include jY in
/-- The compactification `Y ⟶ W = Ȳ ×_Z̄ Z` of `g` over `Z`. -/
abbrev jg : CompactificationOf (Over.mk g) := restrictBase jh jY

include jY in
/-- The structure morphism `Ȳ ⟶ Z̄`, from the ambient scheme of `jgh`. -/
abbrev gbar : (jgh jh jY).space ⟶ jh.space := jY.toBase

/-- The morphism `gbar : Ȳ ⟶ Z̄` is proper. -/
instance isProper_gbar : IsProper (gbar jh jY) := (inferInstance : IsProper jY.toBase)

/-- The composite `Y ⟶ Ȳ ⟶ Z̄` equals `g ≫ i_Z`. -/
lemma jgh_immersion_toBase : (jgh jh jY).immersion ≫ gbar jh jY = g ≫ jh.immersion :=
  immersion_toBase (overBar jh jY)

include jY jX in
/-- `X̄` as a compactification of `(f ≫ g) ≫ i_Z` over `Z̄`. -/
abbrev jXZ : CompactificationOf (Over.mk ((f ≫ g) ≫ jh.immersion)) :=
  ofFactor (overBar (jgh jh jY) jX).immersion ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY)
    ((f ≫ g) ≫ jh.immersion)
    ((Category.assoc _ _ _).symm.trans ((eq_whisker (immersion_toBase (overBar (jgh jh jY) jX))
      _).trans ((Category.assoc _ _ _).trans ((whisker_eq _ (jgh_immersion_toBase jh jY)).trans
        (Category.assoc _ _ _).symm))))

include jY jX in
/-- The compactification `X ⟶ X̄` of `f ≫ g ≫ h` through `Ȳ`. -/
abbrev jfgh₁ : CompactificationOf (Over.mk (f ≫ g ≫ h)) := compOver (jgh jh jY) jX

include jY jX in
/-- The compactification `X ⟶ X̄ ×_Ȳ Y` of `f`. -/
abbrev jf₁ : CompactificationOf (Over.mk f) := restrictBase (jgh jh jY) jX

include jY jX in
/-- The compactification `X ⟶ X̄` of `f ≫ g ≫ h` through `Z̄`. -/
abbrev jfgh₃ : CompactificationOf (Over.mk ((f ≫ g) ≫ h)) := compOver jh (jXZ jh jY jX)

include jY jX in
/-- The compactification `X ⟶ X̄ ×_Z̄ Z` of `f ≫ g`. -/
abbrev jfg₃ : CompactificationOf (Over.mk (f ≫ g)) := restrictBase jh (jXZ jh jY jX)

/-- The open immersion `W = Ȳ ×_Z̄ Z ⟶ Ȳ`, into the ambient scheme of `jgh`. -/
abbrev iW : (jg jh jY).space ⟶ (jgh jh jY).space := restrictBaseι jh jY

/-- The morphism `iW : Ȳ ×_Z̄ Z ⟶ Ȳ` is an open immersion. -/
instance isOpenImmersion_iW : IsOpenImmersion (iW jh jY) :=
  isOpenImmersion_restrictBaseι jh jY

include jY jX in
/-- The projection `X̄ ×_Z̄ Z ⟶ X̄`. -/
abbrev fst₃ : (jfg₃ jh jY jX).space ⟶ (overBar (jgh jh jY) jX).space :=
  pullback.fst (jXZ jh jY jX).toBase jh.immersion

include jY jX in
/-- The morphism `X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z` induced by `X̄ ⟶ Ȳ`. -/
abbrev pmap : (jfg₃ jh jY jX).space ⟶ (jg jh jY).space :=
  pullback.lift (fst₃ jh jY jX ≫ (overBar (jgh jh jY) jX).toBase)
    (pullback.snd (jXZ jh jY jX).toBase jh.immersion)
    ((Category.assoc _ _ _).trans (pullback.condition (f := (jXZ jh jY jX).toBase)))

/-- The composite `X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z ⟶ Z` is the projection `X̄ ×_Z̄ Z ⟶ Z`. -/
lemma pmap_snd : pmap jh jY jX ≫ (jg jh jY).toBase = (jfg₃ jh jY jX).toBase :=
  pullback.lift_snd _ _ _

/-- The composite `X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z ⟶ Ȳ` equals `X̄ ×_Z̄ Z ⟶ X̄ ⟶ Ȳ`. -/
lemma pmap_iW : pmap jh jY jX ≫ iW jh jY = fst₃ jh jY jX ≫ (overBar (jgh jh jY) jX).toBase :=
  pullback.lift_fst _ _ _

/-- `X̄ ×_Z̄ Z = X̄ ×_Ȳ (Ȳ ×_Z̄ Z)`: the square of `pmap` over `X̄ ⟶ Ȳ` is cartesian. -/
theorem isPullback_pmap : IsPullback (fst₃ jh jY jX) (pmap jh jY jX)
    (overBar (jgh jh jY) jX).toBase (iW jh jY) := by
  refine IsPullback.of_bot ?_ (pmap_iW jh jY jX).symm
    (IsPullback.of_hasPullback jY.toBase jh.immersion)
  have e : pmap jh jY jX ≫ pullback.snd jY.toBase jh.immersion =
      pullback.snd (jXZ jh jY jX).toBase jh.immersion := pmap_snd jh jY jX
  exact e ▸ IsPullback.of_hasPullback (jXZ jh jY jX).toBase jh.immersion

/-- The morphism `pmap : X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z` is proper. -/
instance isProper_pmap : IsProper (pmap jh jY jX) :=
  MorphismProperty.of_isPullback (isPullback_pmap jh jY jX) inferInstance

/-- The composite `X ⟶ X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z` equals `X ⟶ Y ⟶ Ȳ ×_Z̄ Z`. -/
lemma jfg₃_immersion_pmap :
    (jfg₃ jh jY jX).immersion ≫ pmap jh jY jX = f ≫ (jg jh jY).immersion := by
  have h1 : (jfg₃ jh jY jX).immersion ≫ fst₃ jh jY jX = (overBar (jgh jh jY) jX).immersion :=
    restrictBase_immersion_restrictBaseι jh (jXZ jh jY jX)
  have h2 : (jfg₃ jh jY jX).immersion ≫ pullback.snd (jXZ jh jY jX).toBase jh.immersion = f ≫ g :=
    baseChangeImmersion_snd (isPullback_id_comp_immersion jh) (jXZ jh jY jX)
  have h3 : (jg jh jY).immersion ≫ pullback.snd jY.toBase jh.immersion = g :=
    baseChangeImmersion_snd (isPullback_id_comp_immersion jh) jY
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pmap_iW jh jY jX)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((eq_whisker h1 _).trans ?_)
    exact (immersion_toBase (overBar (jgh jh jY) jX)).trans (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pmap_snd jh jY jX)).trans ?_)
    exact h2.trans ((whisker_eq _ h3).symm.trans (Category.assoc _ _ _).symm)

include jY jX in
/-- `X̄ ×_Z̄ Z` as a compactification of `X` over `W = Ȳ ×_Z̄ Z`. -/
abbrev jXW : CompactificationOf (Over.mk (f ≫ (jg jh jY).immersion)) :=
  ofFactor (jfg₃ jh jY jX).immersion (pmap jh jY jX) (f ≫ (jg jh jY).immersion)
    (jfg₃_immersion_pmap jh jY jX)

include jY jX in
/-- The compactification `X ⟶ (X̄ ×_Z̄ Z) ×_W Y` of `f`. -/
abbrev jf₄ : CompactificationOf (Over.mk f) := restrictBase (jg jh jY) (jXW jh jY jX)

include jY jX in
/-- The compactification `X ⟶ X̄ ×_Z̄ Z` of `f ≫ g`, through `W`. -/
abbrev jfg₄ : CompactificationOf (Over.mk (f ≫ g)) := compOver (jg jh jY) (jXW jh jY jX)

/-- The composite `X ⟶ X̄ ×_Ȳ Y ⟶ X̄` is the immersion `X ⟶ X̄`. -/
lemma jf₁_immersion_fst :
    (jf₁ jh jY jX).immersion ≫ restrictBaseι (jgh jh jY) jX = jX.immersion :=
  restrictBase_immersion_restrictBaseι (jgh jh jY) jX

/-- The composite `X ⟶ X̄ ×_Z̄ Z ⟶ X̄` is the immersion `X ⟶ X̄`. -/
lemma jfg₃_immersion_fst :
    (jfg₃ jh jY jX).immersion ≫ fst₃ jh jY jX = (overBar (jgh jh jY) jX).immersion :=
  restrictBase_immersion_restrictBaseι jh (jXZ jh jY jX)

include jY jX in
/-- The morphism `X̄ ×_Ȳ Y ⟶ X̄ ×_Z̄ Z`. -/
abbrev φ₁₃ : (jf₁ jh jY jX).space ⟶ (jfg₃ jh jY jX).space :=
  pullback.lift (restrictBaseι (jgh jh jY) jX)
    ((jf₁ jh jY jX).toBase ≫ g)
    ((Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.condition (f := jX.toBase)
      (g := (jgh jh jY).immersion)) _).trans ((Category.assoc _ _ _).trans
        ((whisker_eq _ (jgh_immersion_toBase jh jY)).trans (Category.assoc _ _ _).symm))))

/-- The composite `X̄ ×_Ȳ Y ⟶ X̄ ×_Z̄ Z ⟶ X̄` is the projection `X̄ ×_Ȳ Y ⟶ X̄`. -/
lemma φ₁₃_fst : φ₁₃ jh jY jX ≫ fst₃ jh jY jX = restrictBaseι (jgh jh jY) jX :=
  pullback.lift_fst _ _ _

/-- The composite `X̄ ×_Ȳ Y ⟶ X̄ ×_Z̄ Z ⟶ Z` equals `X̄ ×_Ȳ Y ⟶ Y ⟶ Z`. -/
lemma φ₁₃_snd : φ₁₃ jh jY jX ≫ pullback.snd (jXZ jh jY jX).toBase jh.immersion =
    (jf₁ jh jY jX).toBase ≫ g :=
  pullback.lift_snd _ _ _

/-- The two morphisms `X̄ ×_Ȳ Y ⟶ Ȳ ×_Z̄ Z`, through `Y` and through `X̄ ×_Z̄ Z`, agree. -/
lemma φ₁₃_pmap : (jf₁ jh jY jX).toBase ≫ (jg jh jY).immersion = φ₁₃ jh jY jX ≫ pmap jh jY jX := by
  refine pullback.hom_ext ?_ ?_
  · calc ((jf₁ jh jY jX).toBase ≫ (jg jh jY).immersion) ≫ iW jh jY
        = (jf₁ jh jY jX).toBase ≫ (jgh jh jY).immersion := Category.assoc _ _ _
      _ = restrictBaseι (jgh jh jY) jX ≫ jX.toBase :=
          (pullback.condition (f := jX.toBase) (g := (jgh jh jY).immersion)).symm
      _ = (φ₁₃ jh jY jX ≫ fst₃ jh jY jX) ≫ (overBar (jgh jh jY) jX).toBase :=
          (eq_whisker (φ₁₃_fst jh jY jX) _).symm
      _ = (φ₁₃ jh jY jX ≫ pmap jh jY jX) ≫ iW jh jY :=
          (Category.assoc _ _ _).trans ((whisker_eq _ (pmap_iW jh jY jX)).symm.trans
            (Category.assoc _ _ _).symm)
  · calc ((jf₁ jh jY jX).toBase ≫ (jg jh jY).immersion) ≫ pullback.snd jY.toBase jh.immersion
        = (jf₁ jh jY jX).toBase ≫ g :=
          (Category.assoc _ _ _).trans
            (whisker_eq _ (baseChangeImmersion_snd (isPullback_id_comp_immersion jh) jY))
      _ = φ₁₃ jh jY jX ≫ pullback.snd (jXZ jh jY jX).toBase jh.immersion := (φ₁₃_snd jh jY jX).symm
      _ = (φ₁₃ jh jY jX ≫ pmap jh jY jX) ≫ pullback.snd jY.toBase jh.immersion :=
          (whisker_eq _ (pmap_snd jh jY jX)).symm.trans (Category.assoc _ _ _).symm

/-- The comparison `jf₁ ⟶ jf₄` of compactifications of `f`. -/
def r₁₄ : jf₁ jh jY jX ⟶ jf₄ jh jY jX :=
  toBaseChange (isPullback_id_comp_immersion (jg jh jY)) (jXW jh jY jX) (jf₁ jh jY jX)
    (φ₁₃ jh jY jX)
    (by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_fst _ _ _)).trans ?_)
        refine (jf₁_immersion_fst jh jY jX).trans ?_
        exact (jf₁_immersion_fst jh jY jX).symm.trans
          (((restrictBase_immersion_restrictBaseι jh (jXZ jh jY jX)).symm.trans
            (Category.id_comp _).symm).trans (Category.assoc _ _ _).symm)
      · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_snd _ _ _)).trans ?_)
        refine (Category.assoc _ _ _).symm.trans
          ((eq_whisker (immersion_toBase (jf₁ jh jY jX)) _).trans ?_)
        exact ((baseChangeImmersion_snd (isPullback_id_comp_immersion jh) (jXZ jh jY jX)).symm.trans
          (Category.id_comp _).symm).trans (Category.assoc _ _ _).symm)
    (φ₁₃_pmap jh jY jX)

/-- The comparison `jXZ ⟶ overBar jh jXZ` (the identity of `X̄`). -/
def c₁₃' : jXZ jh jY jX ⟶ overBar jh (jXZ jh jY jX) :=
  homOfSpaceMap _ _ (𝟙 _)
    ((Category.comp_id _).trans (restrictBase_immersion_restrictBaseι jh (jXZ jh jY jX)).symm)
    (Category.id_comp _)

/-- The comparison `overBar jg jXW ⟶ jXW` (the identity of `X̄ ×_Z̄ Z`). -/
def c₃₄' : overBar (jg jh jY) (jXW jh jY jX) ⟶ jXW jh jY jX :=
  homOfSpaceMap _ _ (𝟙 _)
    ((Category.comp_id _).trans (restrictBase_immersion_restrictBaseι (jg jh jY) (jXW jh jY jX)))
    (Category.id_comp _)

include jY jX in
/-- The projection `X̄ ×_Z̄ Z ⟶ X̄`, from the ambient scheme of `jXW`. -/
abbrev fstXW : (jXW jh jY jX).space ⟶ (overBar (jgh jh jY) jX).space := fst₃ jh jY jX

include jY jX in
/-- The projection `X̄ ×_Ȳ Y ⟶ X̄`, into the ambient scheme of `overBar`. -/
abbrev fst₁ : (jf₁ jh jY jX).space ⟶ (overBar (jgh jh jY) jX).space :=
  restrictBaseι (jgh jh jY) jX

include jY jX in
/-- The projection `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z`. -/
abbrev fst₄ : (jf₄ jh jY jX).space ⟶ (jXW jh jY jX).space :=
  restrictBaseι (jg jh jY) (jXW jh jY jX)

/-- The composite `X̄ ×_Z̄ Z ⟶ Ȳ ×_Z̄ Z ⟶ Ȳ` equals `X̄ ×_Z̄ Z ⟶ X̄ ⟶ Ȳ`, stated for `jXW`. -/
lemma pmap_iW' : (jXW jh jY jX).toBase ≫ iW jh jY =
    fstXW jh jY jX ≫ (overBar (jgh jh jY) jX).toBase :=
  pmap_iW jh jY jX

/-- The square `X = X ×_{X̄} (X̄ ×_Z̄ Z)`. -/
theorem hc₃ : IsPullback (𝟙 X) (jXW jh jY jX).immersion (overBar (jgh jh jY) jX).immersion
    (fstXW jh jY jX) :=
  isPullback_baseChange (isPullback_id_comp_immersion jh) (jXZ jh jY jX)

/-- The square `X = X ×_{X̄ ×_Z̄ Z} ((X̄ ×_Z̄ Z) ×_W Y)`. -/
theorem hc₄ : IsPullback (𝟙 X) (jf₄ jh jY jX).immersion (jXW jh jY jX).immersion
    (fst₄ jh jY jX) :=
  isPullback_baseChange (isPullback_id_comp_immersion (jg jh jY)) (jXW jh jY jX)

/-- The square `(X̄ ×_Z̄ Z) ×_W Y ⟶ Y ⟶ W` and `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z ⟶ W` commutes. -/
lemma w₄ : (jf₄ jh jY jX).toBase ≫ (jg jh jY).immersion =
    fst₄ jh jY jX ≫ (jXW jh jY jX).toBase :=
  (pullback.condition (f := (jXW jh jY jX).toBase) (g := (jg jh jY).immersion)).symm

/-- The two morphisms `(X̄ ×_Z̄ Z) ×_W Y ⟶ Ȳ`, through `Y ⟶ W` and through `X̄`, agree. -/
lemma w₄₃ : (jf₄ jh jY jX).toBase ≫ ((jg jh jY).immersion ≫ iW jh jY) =
    (fst₄ jh jY jX ≫ fstXW jh jY jX) ≫ (overBar (jgh jh jY) jX).toBase :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (w₄ jh jY jX) _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ (pmap_iW' jh jY jX)).trans
      (Category.assoc _ _ _).symm)))

/-- The ambient morphism of `r₁₄` followed by the projection `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` is the
projection `X̄ ×_Ȳ Y ⟶ X̄`. -/
lemma r₁₄_map_fst : Hom.map (r₁₄ jh jY jX) ≫ (fst₄ jh jY jX ≫ fstXW jh jY jX) =
    fst₁ jh jY jX ≫ Hom.map (𝟙 (overBar (jgh jh jY) jX)) :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (toBaseChange_map_fst _ _ _ _ _ _) _).trans
    ((φ₁₃_fst jh jY jX).trans (Category.comp_id _).symm))

/-- The square `X = X ×_{X̄} (X̄ ×_Z̄ Z)`, for `jXZ`. -/
theorem hcZ₃ : IsPullback (𝟙 X) (jfg₃ jh jY jX).immersion (jXZ jh jY jX).immersion
    (fst₃ jh jY jX) :=
  isPullback_baseChange (isPullback_id_comp_immersion jh) (jXZ jh jY jX)

include jY jX in
/-- The structure morphism `X̄ ×_Z̄ Z ⟶ Z`, from the ambient scheme of `jXW`. -/
abbrev snd₃ : (jXW jh jY jX).space ⟶ Z := (jfg₃ jh jY jX).toBase

/-- The projection `snd₃ : X̄ ×_Z̄ Z ⟶ Z` is proper. -/
instance isProper_snd₃ : IsProper (snd₃ jh jY jX) :=
  (inferInstance : IsProper (jfg₃ jh jY jX).toBase)

/-- The projection `X̄ ×_Z̄ Z ⟶ Z` factors as `X̄ ×_Z̄ Z ⟶ W ⟶ Z`. -/
lemma jfg₃_toBase_eq : snd₃ jh jY jX = (jXW jh jY jX).toBase ≫ (jg jh jY).toBase :=
  (pmap_snd jh jY jX).symm

/-- The comparison `compOver jg jXW ⟶ jfg₃` (the identity of `X̄ ×_Z̄ Z`) of compactifications of
`f ≫ g` over `Z`, read from `overBar jg jXW ⟶ jXW` over `W`. -/
abbrev c₃₄ : jfg₄ jh jY jX ⟶ jfg₃ jh jY jX :=
  ofFactorHom (jg jh jY).toBase (f ≫ g) (c₃₄' jh jY jX)
    ((overBar (jg jh jY) (jXW jh jY jX)).toBase ≫ (jg jh jY).toBase) rfl (snd₃ jh jY jX)
    (jfg₃_toBase_eq jh jY jX) (immersion_toBase (jfg₄ jh jY jX))
    (immersion_toBase (jfg₃ jh jY jX))

/-- The comparison `jfgh₁ ⟶ jfgh₃` (the identity of `X̄`) of compactifications of `f ≫ g ≫ h`
over `T`, read from `jXZ ⟶ overBar jh jXZ` over `Z̄`. -/
abbrev c₁₃ : jfgh₁ jh jY jX ⟶ jfgh₃ jh jY jX :=
  ofFactorHom jh.toBase (f ≫ g ≫ h) (c₁₃' jh jY jX)
    ((jXZ jh jY jX).toBase ≫ jh.toBase) rfl ((overBar jh (jXZ jh jY jX)).toBase ≫ jh.toBase) rfl
    (immersion_toBase (jfgh₁ jh jY jX)) (immersion_toBase (jfgh₃ jh jY jX))

end AlgebraicGeometry.CompactificationOf.Tower

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

section Chain

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)

/-- A diagram chase for a functor `G`: given the commuting squares `hn`, `hA` and the one-sided
inverses `hbc`, `hbb`, `hJ`, `t ≫ ibc = eK ≫ G.map (tθ ≫ ibb) ≫ eJinv`. -/
lemma ofFactor_chain {A₀ A₁ A₂ : D} {P₀ P₁ P₂ : C} (t : A₀ ⟶ A₁) (ibc : A₁ ⟶ A₂) (bc : A₂ ⟶ A₁)
    (eK : A₀ ⟶ G.obj P₀) (tθ : P₀ ⟶ P₁) (ibb : P₁ ⟶ P₂) (bb : P₂ ⟶ P₁) (eM : A₁ ⟶ G.obj P₁)
    (eJ : A₂ ⟶ G.obj P₂) (eJinv : G.obj P₂ ⟶ A₂)
    (hn : t ≫ eM = eK ≫ G.map tθ) (hA : eJ ≫ G.map bb = bc ≫ eM) (hbc : ibc ≫ bc = 𝟙 _)
    (hbb : bb ≫ ibb = 𝟙 _) (hJ : eJ ≫ eJinv = 𝟙 _) :
    t ≫ ibc = eK ≫ G.map (tθ ≫ ibb) ≫ eJinv := by
  have h1 : ibc = eM ≫ G.map ibb ≫ eJinv := by
    calc ibc = ibc ≫ eJ ≫ G.map (bb ≫ ibb) ≫ eJinv := by
          rw [hbb, G.map_id, Category.id_comp, hJ, Category.comp_id]
      _ = (ibc ≫ bc) ≫ eM ≫ G.map ibb ≫ eJinv := by
          simp only [G.map_comp, Category.assoc]
          rw [reassoc_of% hA]
      _ = eM ≫ G.map ibb ≫ eJinv := by rw [hbc, Category.id_comp]
  rw [h1, reassoc_of% hn, G.map_comp, Category.assoc]

/-- A diagram chase for a functor `G`: given the commutations `F1`, …, `F5` and the one-sided
inverse `i`, `G.map (A ≫ Bι ≫ Cc ≫ Dd ≫ E) ≫ ε₁ = cDh ≫ big ≫ Rι₄ ≫ Hr`. -/
lemma ewr_chain {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {a0 a1 a2 a3 a4 a5 : C}
    {Q s1 s3 t1 t4 : D} (A : a0 ⟶ a1) (Bι : a1 ⟶ a2) (Cc : a2 ⟶ a3) (Dd : a3 ⟶ a4)
    (E : a4 ⟶ a5) (ε₁ : G.obj a5 ⟶ t1) (ε₄ : G.obj a4 ⟶ t4) (Hr : t4 ⟶ t1)
    (cubeW : G.obj a3 ⟶ s3) (Rι₄ : s3 ⟶ t4) (cube₂K : G.obj a2 ⟶ s3) (cube₂' : G.obj a1 ⟶ s1)
    (Rι' : s1 ⟶ s3) (cDh : G.obj a0 ⟶ Q) (cDinv : Q ⟶ G.obj a0) (big : Q ⟶ s3)
    (F1 : G.map E ≫ ε₁ = ε₄ ≫ Hr) (F2 : G.map Dd ≫ ε₄ = cubeW ≫ Rι₄)
    (F3 : G.map Cc ≫ cubeW = cube₂K) (F4 : G.map Bι ≫ cube₂K = cube₂' ≫ Rι')
    (F5 : big = cDinv ≫ G.map A ≫ cube₂' ≫ Rι') (i : cDh ≫ cDinv = 𝟙 _) :
    G.map (A ≫ Bι ≫ Cc ≫ Dd ≫ E) ≫ ε₁ = cDh ≫ big ≫ Rι₄ ≫ Hr := by
  simp only [G.map_comp, Category.assoc]
  rw [F1, reassoc_of% F2, reassoc_of% F3, reassoc_of% F4, F5]
  simp only [Category.assoc]
  rw [reassoc_of% i]

/-- A diagram chase for functors `H` and `G`: given the commutations `n1`, `EpsC`, `n2` and the
one-sided inverse `i`, `G.map (ψ ≫ cI ≫ jι) ≫ ε₁ = cDh ≫ ψY ≫ εY`. -/
lemma ewl_chain {C' C D : Type*} [Category* C'] [Category* C] [Category* D] (G : C ⥤ D)
    (H : C' ⥤ C) {b0 : C'} {b1 b2 b3 : C} {Q t u v : D}
    (ψ : H.obj b0 ⟶ b1) (cI : b1 ⟶ b2) (jι : b2 ⟶ b3) (ε₁ : G.obj b3 ⟶ t) (εB : G.obj b2 ⟶ u)
    (ιB : u ⟶ t) (cDh : G.obj (H.obj b0) ⟶ Q) (ψY : Q ⟶ v) (εY : v ⟶ t) (cDh' : G.obj b1 ⟶ v)
    (cDinv : v ⟶ G.obj b1)
    (n1 : G.map jι ≫ ε₁ = εB ≫ ιB)
    (EpsC : εY = cDinv ≫ G.map cI ≫ εB ≫ ιB)
    (n2 : G.map ψ ≫ cDh' = cDh ≫ ψY) (i : cDh' ≫ cDinv = 𝟙 _) :
    G.map (ψ ≫ cI ≫ jι) ≫ ε₁ = cDh ≫ ψY ≫ εY := by
  rw [EpsC, ← reassoc_of% n2, reassoc_of% i]
  simp only [G.map_comp, Category.assoc, n1]

/-- A diagram chase: two morphisms `x = c ≫ p ≫ e` and `y = c ≫ bg ≫ r4 ≫ hr` agree, given the
commutations `hY`, `N2` and `nr`. -/
lemma ew_final_chain {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ A₇ : C}
    (x y : A₀ ⟶ A₇) (c : A₀ ⟶ A₁) (p : A₁ ⟶ A₂) (e : A₂ ⟶ A₇) (cy : A₁ ⟶ A₃) (r1 : A₃ ⟶ A₇)
    (bg : A₁ ⟶ A₄) (hr' : A₄ ⟶ A₃) (r4 : A₄ ⟶ A₅) (hr : A₅ ⟶ A₇)
    (L : x = c ≫ p ≫ e) (hY : p ≫ e = cy ≫ r1) (N2 : 𝟙 _ ≫ cy = bg ≫ hr')
    (nr : r4 ≫ hr = hr' ≫ r1) (R : y = c ≫ bg ≫ r4 ≫ hr) : x = y := by
  rw [L, R, hY, ← Category.id_comp cy, N2, Category.assoc, nr]

end Chain

section PushBase

variable {S S' X : Scheme.{u}} {p' : X ⟶ S'} (q : S' ⟶ S) [IsProper q] (p : X ⟶ S)
  {j' k' : CompactificationOf (Over.mk p')} (ψ : j' ⟶ k') (bj : j'.space ⟶ S) [IsProper bj]
  (hbj : bj = j'.toBase ≫ q) (bk : k'.space ⟶ S) [IsProper bk] (hbk : bk = k'.toBase ≫ q)
  (hj : j'.immersion ≫ bj = p) (hk : k'.immersion ≫ bk = p)

omit [IsProper q] in
/-- The comparison of [Stacks, Tag 0F7I] along a pushed morphism of compactifications is the
derived direct image along `q` of the comparison over `S'`, read through the composition
isomorphisms of derived direct images. -/
theorem derivedLowerShriekHom_ofFactorHom (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekHom Λ (CompactificationOf.ofFactorHom q p ψ bj hbj bk hbk hj hk)).app K =
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ k'.toBase q bk hbk).hom.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ k'.immersion).obj K) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ q).map ((derivedLowerShriekHom Λ ψ).app K) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ j'.toBase q bj hbj).inv.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j'.immersion).obj K) := by
  let M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ j'.space) :=
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ j'.immersion).obj K
  let bb := derivedBaseComparison Λ ψ
  let bc := derivedBaseComparison Λ (CompactificationOf.ofFactorHom q p ψ bj hbj bk hbk hj hk)
  let θ := derivedRefinementComparison Λ ψ
  have hA := congrArg (fun t => NatTrans.app t M)
    (rightDerivedFunctorPlusComp_etaleModuleDirectImageComp_assoc Λ
      (CompactificationOf.Hom.map ψ) k'.toBase q j'.toBase
      (CompactificationOf.map_comp_toBase ψ).symm bk hbk bj hbj
      (by rw [hbj, hbk, ← Category.assoc, CompactificationOf.map_comp_toBase]))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA
  have hbc : (inv bc).app _ ≫ bc.app _ = 𝟙 _ := NatTrans.congr_app (IsIso.inv_hom_id bc)
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
      (CompactificationOf.ofFactor j'.immersion bj p hj).immersion).obj K)
  have hbb : bb.app M ≫ (inv bb).app M = 𝟙 _ := NatTrans.congr_app (IsIso.hom_inv_id bb) M
  have hn := (etaleModuleDerivedDirectImageComp.{u, 0} Λ k'.toBase q bk hbk).hom.naturality
    (θ.app K)
  rw [etaleModuleDerivedDirectImageComp_hom_eq] at hn
  have hJ := Iso.hom_inv_id_app
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ j'.toBase q bj hbj) M
  rw [etaleModuleDerivedDirectImageComp_hom_eq] at hJ
  rw [derivedLowerShriekHom_app, derivedLowerShriekHom_app,
    etaleModuleDerivedDirectImageComp_hom_eq]
  exact ofFactor_chain (etaleModuleDerivedDirectImage.{u, 0} Λ q) _ _ _ _ _ _ _ _ _ _
    hn hA hbc hbb hJ

end PushBase

/-- The comparison of [Stacks, Tag 0F7I] along an identity is the identity, at a torsion
object. -/
lemma derivedLowerShriekHom_id_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) : (derivedLowerShriekHom Λ (𝟙 j)).app K = 𝟙 _ := by
  have := congrArg (fun e => e.hom.app (⟨K, hK⟩ : (isTorsionPlus.{u, 0} Λ X).FullSubcategory))
    (derivedLowerShriekHomIso_id Λ j)
  simpa using this

/-- For a natural isomorphism `η : F ≅ 𝟭`, `F η_X = η_{F X}`. -/
lemma map_hom_app_eq_hom_app_obj {C : Type*} [Category* C] {F : C ⥤ C} (η : F ≅ 𝟭 C) (X : C) :
    F.map (η.hom.app X) = η.hom.app (F.obj X) := by
  have n := η.hom.naturality (η.hom.app X)
  simp only [Functor.id_map] at n
  rw [← cancel_mono (η.hom.app X)]
  exact n

/-- Naturality of the base change cube along `ψ : j₁ ⟶ j₂` over the identity of `X`. -/
private lemma map_derivedLowerShriekHom_comp_cube_id {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {f' : X ⟶ Y'} {g : Y' ⟶ Y} {j₁ j₂ : CompactificationOf (Over.mk f)}
    {j' : CompactificationOf (Over.mk f')} (ψ : j₁ ⟶ j₂) (φ₁ : j'.space ⟶ j₁.space)
    (φ₂ : j'.space ⟶ j₂.space) (hc₁ : IsPullback (𝟙 X) j'.immersion j₁.immersion φ₁)
    (hc₂ : IsPullback (𝟙 X) j'.immersion j₂.immersion φ₂)
    (wp : φ₂ = φ₁ ≫ CompactificationOf.Hom.map ψ) (w₁ : j'.toBase ≫ g = φ₁ ≫ j₁.toBase)
    (w₂ : j'.toBase ≫ g = φ₂ ≫ j₂.toBase) (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((derivedLowerShriekHom Λ ψ).app K.obj) ≫
      (derivedLowerShriekBaseChangeCube Λ j₁ j' φ₁ hc₁ w₁).app K.obj =
    (derivedLowerShriekBaseChangeCube Λ j₂ j' φ₂ hc₂ w₂).app K.obj := by
  have N := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ ψ (𝟙 j') φ₁ φ₂
    hc₁ hc₂ ((Category.id_comp _).trans wp) w₁ w₂) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at N
  rw [derivedLowerShriekHom_id_app Λ _ _ (isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ
    (𝟙 X) K.obj K.property)] at N
  exact N.trans (Category.comp_id _)

section TowerW

open CompactificationOf CompactificationOf.Tower

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

/-- Over `W = Ȳ ×_Z̄ Z`: the restriction to `W` of `Ψ : R(f ≫ i_Y)_! ≅ i_{Y!} Rf_!` for `Y ⊂ Ȳ` is
the base change map to `X̄ ×_Z̄ Z` followed by `Ψ` for `Y ⊂ W`, read through the comparisons of
[Stacks, Tag 0F7I] and the isomorphisms of [Stacks, Tag 03S6]. -/
theorem tower_W (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iW jh jY)).map
        ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K) ≫
      (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_restrictBase_overBar jh jY)).inv.app
        ((derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj) ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ (jg jh jY).immersion).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom.app
          ((derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj)) =
    (derivedLowerShriekBaseChangeCube Λ (overBar (jgh jh jY) jX) (jXW jh jY jX) (fstXW jh jY jX)
        (hc₃ jh jY jX) (pmap_iW' jh jY jX)).app K.obj ≫
      (derivedLowerShriek.{u, 0} (f ≫ (jg jh jY).immersion) (jXW jh jY jX) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj) ≫
      (derivedLowerShriekHom Λ (c₃₄' jh jY jX)).app K.obj ≫
      (derivedLowerShriekRestrictBaseIso Λ (jg jh jY) (jXW jh jY jX)).hom.app K ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ (jg jh jY).immersion).map
        ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj) := by
  let B := (derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj
  let jW := (jg jh jY).immersion
  let ε := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jW
  let ι := etaleModuleDerivedInverseImagePlusIdIso Λ X
  let ιY := etaleModuleDerivedInverseImagePlusIdIso Λ Y
  let cD := etaleModuleDerivedInverseImagePlusCompIso Λ jW (iW jh jY)
  let Ψ := derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX
  let ΨW := derivedLowerShriekRestrictBaseIso Λ (jg jh jY) (jXW jh jY jX)
  let cube₁ := derivedLowerShriekBaseChangeCube Λ (overBar (jgh jh jY) jX) (jXW jh jY jX)
    (fstXW jh jY jX) (hc₃ jh jY jX) (pmap_iW' jh jY jX)
  let cube₂ := derivedLowerShriekBaseChangeCube Λ (jXW jh jY jX) (jf₄ jh jY jX) (fst₄ jh jY jX)
    (hc₄ jh jY jX) (w₄ jh jY jX)
  let cubeW := derivedLowerShriekBaseChangeCube Λ (overBar (jg jh jY) (jXW jh jY jX))
    (jf₄ jh jY jX) (fst₄ jh jY jX) (isPullback_restrictBase_overBar (jg jh jY) (jXW jh jY jX))
    (w₄ jh jY jX)
  let big := derivedLowerShriekBaseChangeCube Λ (overBar (jgh jh jY) jX) (jf₄ jh jY jX)
    (fst₄ jh jY jX ≫ fstXW jh jY jX) ((hc₄ jh jY jX).paste_horiz (hc₃ jh jY jX)) (w₄₃ jh jY jX)
  let cubeY := derivedLowerShriekBaseChangeCube Λ (overBar (jgh jh jY) jX) (jf₁ jh jY jX)
    (fst₁ jh jY jX) (isPullback_restrictBase_overBar (jgh jh jY) jX) pullback.condition.symm
  have : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iW jh jY)).map (Ψ.hom.app K) ≫
      (etaleModuleDerivedExtensionByZeroCubeIso Λ
        (isPullback_restrictBase_overBar jh jY)).inv.app B ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ jW).map (ιY.hom.app B)) :=
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iW jh jY)).mapIso (Ψ.app K) ≪≫
      ((etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_restrictBase_overBar jh jY)).app
        B).symm ≪≫ (etaleModuleDerivedExtensionByZero.{u, 0} Λ jW).mapIso (ιY.app B)).isIso_hom
  refine eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_isIso Λ jW _ _ ?_
  refine (cancel_mono (ε.hom.app B)).mp ?_
  have n1 := ε.hom.naturality (ιY.hom.app B)
  simp only [Functor.comp_map, Functor.id_map] at n1
  have L := ewl_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jW)
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iW jh jY))
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (iW jh jY)).map (Ψ.hom.app K)) _ _ _ _ _
    (cD.hom.app _) ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jgh jh jY).immersion).map
      (Ψ.hom.app K)) _ (cD.hom.app _) (cD.inv.app _) n1
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp_cube Λ jW (iW jh jY)
      (isPullback_restrictBase_overBar jh jY) B)
    (cD.hom.naturality (Ψ.hom.app K)) (Iso.hom_inv_id_app cD _)
  have F1 := ε.hom.naturality ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj)
  simp only [Functor.comp_map, Functor.id_map] at F1
  have F2 := derivedLowerShriekRestrictBaseIso_restrict_cube Λ (jg jh jY) (jXW jh jY jX) K
  have F3 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jW).map
      ((derivedLowerShriekHom Λ (c₃₄' jh jY jX)).app K.obj) ≫ cubeW.app K.obj =
        cube₂.app K.obj := by
    exact map_derivedLowerShriekHom_comp_cube_id Λ (c₃₄' jh jY jX) (fst₄ jh jY jX)
      (fst₄ jh jY jX) (isPullback_restrictBase_overBar (jg jh jY) (jXW jh jY jX)) (hc₄ jh jY jX)
      (Category.comp_id _).symm (w₄ jh jY jX) (w₄ jh jY jX) K
  have F4 := cube₂.naturality (ι.hom.app K.obj)
  simp only [Functor.comp_map] at F4
  have F5 : big.app K.obj = cD.inv.app _ ≫ (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jW).map
      (cube₁.app K.obj) ≫
        cube₂.app ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj) ≫
      (derivedLowerShriek.{u, 0} f (jf₄ jh jY jX) Λ).map
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).map (ι.hom.app K.obj)) := by
    have P := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_paste Λ
      (overBar (jgh jh jY) jX) (jXW jh jY jX) (jf₄ jh jY jX) (fstXW jh jY jX) (fst₄ jh jY jX)
      (hc₃ jh jY jX) (hc₄ jh jY jX) (pmap_iW' jh jY jX) (w₄ jh jY jX) (w₄₃ jh jY jX)) K.obj
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at P
    rw [map_hom_app_eq_hom_app_obj ι, ← etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app]
    exact P
  have R := ewr_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jW) (cube₁.app K.obj)
    ((derivedLowerShriek.{u, 0} (f ≫ (jg jh jY).immersion) (jXW jh jY jX) Λ).map (ι.hom.app K.obj))
    ((derivedLowerShriekHom Λ (c₃₄' jh jY jX)).app K.obj) (ΨW.hom.app K)
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jW).map
      ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj)) (ε.hom.app B) _ _ (cubeW.app K.obj)
    _ (cube₂.app K.obj) _ _ (cD.hom.app _) (cD.inv.app _) (big.app K.obj) F1 F2 F3 F4 F5
    (Iso.hom_inv_id_app cD _)
  have hY := derivedLowerShriekRestrictBaseIso_restrict_cube Λ (jgh jh jY) jX K
  have N2 := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ
    (𝟙 (overBar (jgh jh jY) jX)) (r₁₄ jh jY jX) (fst₁ jh jY jX) (fst₄ jh jY jX ≫ fstXW jh jY jX)
    (isPullback_restrictBase_overBar (jgh jh jY) jX) ((hc₄ jh jY jX).paste_horiz (hc₃ jh jY jX))
    (r₁₄_map_fst jh jY jX) pullback.condition.symm (w₄₃ jh jY jX)) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at N2
  rw [derivedLowerShriekHom_id_app Λ _ _ K.property, CategoryTheory.Functor.map_id] at N2
  have nr := (derivedLowerShriekHom Λ (r₁₄ jh jY jX)).naturality (ι.hom.app K.obj)
  exact ew_final_chain _ _ _ _ _ _ _ _ _ _ _ L hY N2 nr R

end TowerW

section TowerZ

open CompactificationOf CompactificationOf.Tower

/-- A diagram chase for functors `G`, `P` and `R3`: given the stated commutations and the
one-sided inverse `hb`, `x0 ≫ x1 ≫ cubeZY ≫ Rjgι = cube₃K ≫ Rjfg3ι ≫ Hc4 ≫ CO ≫ Rjgr`. -/
lemma ez_chain {C' C E : Type*} [Category* C'] [Category* C] [Category* E] (G : C ⥤ E)
    (P : C' ⥤ C) (R3 : C' ⥤ E) {e0 e1 e2 e3 : E} {c0 c1 c2 c3 c6 c7 : C} {d0 d1 d2 : C'}
    (x0 : e0 ⟶ e1) (x1 : e1 ⟶ e2) (cubeZY : e2 ⟶ G.obj c1) (pbcG : e2 ⟶ G.obj c0)
    (cY : c0 ⟶ c1) (jgι : c1 ⟶ c2) (Rjgι : G.obj c1 ⟶ G.obj c2) (pbcG0 : e1 ⟶ G.obj c3)
    (ψW : c3 ⟶ c0) (cube₁K : c3 ⟶ P.obj d1) (RXWι : P.obj d1 ⟶ P.obj d2) (Hc : P.obj d2 ⟶ c6)
    (ΨW : c6 ⟶ c7) (jgHr : c7 ⟶ c2) (pbcF : c3 ⟶ P.obj d0) (cE : d0 ⟶ d1) (jι : d1 ⟶ d2)
    (cube₃K : e0 ⟶ R3.obj d1) (pbc3 : e0 ⟶ R3.obj d0) (Rjfg3ι : R3.obj d1 ⟶ R3.obj d2)
    (Hc4 : R3.obj d2 ⟶ e3) (e₂2 : R3.obj d2 ⟶ G.obj (P.obj d2)) (e₂binv : G.obj c6 ⟶ e3)
    (CO : e3 ⟶ G.obj c7) (e₂b' : e3 ⟶ G.obj c6) (Rjgr : G.obj c7 ⟶ G.obj c2)
    (e₂0 : R3.obj d0 ⟶ G.obj (P.obj d0))
    (hcube : cubeZY = pbcG ≫ G.map cY) (nP : x1 ≫ pbcG = pbcG0 ≫ G.map ψW)
    (W : ψW ≫ cY ≫ jgι = cube₁K ≫ RXWι ≫ Hc ≫ ΨW ≫ jgHr) (hc1 : cube₁K = pbcF ≫ P.map cE)
    (hRX : RXWι = P.map jι) (h3 : cube₃K = pbc3 ≫ R3.map cE) (hι3 : Rjfg3ι = R3.map jι)
    (HP : Hc4 = e₂2 ≫ G.map Hc ≫ e₂binv) (hCO : CO = e₂b' ≫ G.map ΨW)
    (hb : e₂binv ≫ e₂b' = 𝟙 _) (hr : Rjgr = G.map jgHr) (hRjgι : Rjgι = G.map jgι)
    (n3 : R3.map (cE ≫ jι) ≫ e₂2 = e₂0 ≫ G.map (P.map (cE ≫ jι)))
    (V : pbc3 ≫ e₂0 = x0 ≫ pbcG0 ≫ G.map pbcF) :
    x0 ≫ x1 ≫ cubeZY ≫ Rjgι = cube₃K ≫ Rjfg3ι ≫ Hc4 ≫ CO ≫ Rjgr := by
  subst hcube hRjgι h3 hι3 HP hCO hr hc1 hRX
  calc x0 ≫ x1 ≫ (pbcG ≫ G.map cY) ≫ G.map jgι
      = x0 ≫ pbcG0 ≫ G.map (ψW ≫ cY ≫ jgι) := by
        simp only [G.map_comp, Category.assoc]
        rw [reassoc_of% nP]
    _ = (x0 ≫ pbcG0 ≫ G.map pbcF) ≫ G.map (P.map (cE ≫ jι)) ≫ G.map Hc ≫ G.map ΨW ≫
          G.map jgHr := by
        rw [W]
        simp only [G.map_comp, P.map_comp, Category.assoc]
    _ = _ := by
        rw [← V, Category.assoc, ← reassoc_of% n3]
        simp only [R3.map_comp, Category.assoc, reassoc_of% hb]

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

/-- Over `Z`, the composite `R(f̄ ≫ ḡ)_* ≅ Rḡ_* Rf̄_* ≅ Rḡ_* i_{Y!} Rf_!` followed by the base
change map of `Ȳ ⟶ Z̄` is the base change map of `X̄ ⟶ Z̄` followed by the isomorphism of
[Stacks, Tag 0F7J] for `f` and `g` through `X̄ ×_Z̄ Z`, read through the comparisons of
[Stacks, Tag 0F7I]. -/
theorem tower_Z (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jh.immersion).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ (overBar (jgh jh jY) jX).toBase
          (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl).hom.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (overBar (jgh jh jY) jX).immersion).obj K.obj)) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jh.immersion).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (gbar jh jY)).map
          ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K)) ≫
      (derivedLowerShriekBaseChangeCube Λ (overBar jh jY) (jg jh jY) (iW jh jY)
          (isPullback_restrictBase_overBar jh jY) pullback.condition.symm).app
        ((derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj) ≫
      (derivedLowerShriek.{u, 0} g (jg jh jY) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom.app
          ((derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj)) =
    (derivedLowerShriekBaseChangeCube Λ (jXZ jh jY jX) (jfg₃ jh jY jX) (fst₃ jh jY jX)
        (hcZ₃ jh jY jX) pullback.condition.symm).app K.obj ≫
      (derivedLowerShriek.{u, 0} (f ≫ g) (jfg₃ jh jY jX) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj) ≫
      (derivedLowerShriekHom Λ (c₃₄ jh jY jX)).app K.obj ≫
      (derivedLowerShriekCompOverIso Λ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
      (derivedLowerShriek.{u, 0} g (jg jh jY) Λ).map
        ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj) := by
  let M₁ := (etaleModuleDerivedExtensionByZero.{u, 0} Λ (overBar (jgh jh jY) jX).immersion).obj
    K.obj
  let ι := etaleModuleDerivedInverseImagePlusIdIso Λ X
  have nP := (etaleModuleDerivedBaseChange.{u, 0} Λ (gbar jh jY) (jg jh jY).toBase jh.immersion
    (iW jh jY) pullback.condition.symm).naturality
      ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K)
  simp only [Functor.comp_map] at nP
  have n3 := (etaleModuleDerivedDirectImageComp.{u, 0} Λ (pmap jh jY jX) (jg jh jY).toBase
    (snd₃ jh jY jX) (jfg₃_toBase_eq jh jY jX)).hom.naturality
      ((etaleModuleDerivedExtensionByZeroCubeIso Λ (hcZ₃ jh jY jX)).inv.app K.obj ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ (jfg₃ jh jY jX).immersion).map
          (ι.hom.app K.obj))
  simp only [Functor.comp_map] at n3
  have V := congrArg (fun t => NatTrans.app t M₁) (etaleModuleDerivedBaseChange_comp Λ
    (overBar (jgh jh jY) jX).toBase (gbar jh jY) _ rfl (pmap jh jY jX) (jg jh jY).toBase
    (snd₃ jh jY jX) (jfg₃_toBase_eq jh jY jX) (fst₃ jh jY jX) (iW jh jY) jh.immersion
    (pmap_iW jh jY jX) pullback.condition.symm pullback.condition.symm)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at V
  exact ez_chain (etaleModuleDerivedDirectImage.{u, 0} Λ (jg jh jY).toBase)
    (etaleModuleDerivedDirectImage.{u, 0} Λ (pmap jh jY jX))
    (etaleModuleDerivedDirectImage.{u, 0} Λ (snd₃ jh jY jX)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ rfl nP (tower_W Λ jh jY jX K) rfl rfl rfl rfl
    (derivedLowerShriekHom_ofFactorHom Λ _ _ _ _ _ _ _ _ _ _)
    (derivedLowerShriekCompOverIso_hom_app Λ (jg jh jY) (jXW jh jY jX) K)
    (Iso.inv_hom_id_app _ _) rfl rfl n3 V

end TowerZ

section TowerCore

open CompactificationOf CompactificationOf.Tower

/-- A diagram chase for functors `G` and `I`: given the commutations `rY`, `EZ`, `Nc`, `nε`, `rZ`
and `hid = 𝟙`, `G.map (Hc1' ≫ e₂X ≫ RΨ ≫ ΨY) ≫ εN = G.map (ΨZ ≫ I.map T) ≫ εN`. -/
lemma ozb_chain {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (I : D ⥤ C)
    {a0 a1 a2 a3 : C} {n2 n4 m1 m3 : D}
    (Hc1' : a0 ⟶ a1) (e₂X : a1 ⟶ a2) (RΨ : a2 ⟶ a3) (ΨY : a3 ⟶ I.obj n4) (ΨZ : a0 ⟶ I.obj n2)
    (T : n2 ⟶ n4) (εN : G.obj (I.obj n4) ⟶ n4) (εR : G.obj (I.obj n2) ⟶ n2)
    (cubeZY : G.obj a3 ⟶ m3) (Rjgι : m3 ⟶ n4) (cube₃K : G.obj a1 ⟶ m1) (Rjfg3ι : m1 ⟶ n2)
    (cubeOB : G.obj a0 ⟶ m1) (hid : m1 ⟶ m1)
    (rY : G.map ΨY ≫ εN = cubeZY ≫ Rjgι)
    (EZ : G.map e₂X ≫ G.map RΨ ≫ cubeZY ≫ Rjgι = cube₃K ≫ Rjfg3ι ≫ T)
    (Nc : G.map Hc1' ≫ cube₃K = cubeOB ≫ hid) (hid1 : hid = 𝟙 _)
    (nε : G.map (I.map T) ≫ εN = εR ≫ T) (rZ : G.map ΨZ ≫ εR = cubeOB ≫ Rjfg3ι) :
    G.map (Hc1' ≫ e₂X ≫ RΨ ≫ ΨY) ≫ εN = G.map (ΨZ ≫ I.map T) ≫ εN := by
  subst hid1
  simp only [G.map_comp, Category.assoc]
  rw [rY, EZ, reassoc_of% Nc, nε, reassoc_of% rZ]

/-- A diagram chase for a functor `H`: given the stated commutations and the one-sided inverse
`hi`, `COZ ≫ RhT = Hc₁₃ ≫ COX ≫ COY`. -/
lemma core_chain {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {a0 a1 a2 a3 a4 b2 : C} {d0 d2 d3 d4 : D}
    (Hc1' : a0 ⟶ a1) (e₂X : a1 ⟶ a2) (RΨ : a2 ⟶ a3) (ΨY : a3 ⟶ a4) (ΨZ : a0 ⟶ b2)
    (IT : b2 ⟶ a4) (COZ : d0 ⟶ H.obj b2) (RhT : H.obj b2 ⟶ H.obj a4) (e₂Z : d0 ⟶ H.obj a0)
    (Hc₁₃ : d0 ⟶ d2) (e₂inv : H.obj a1 ⟶ d2) (COX : d2 ⟶ d3) (e₂a : d2 ⟶ d4)
    (RghΨ : d4 ⟶ d3) (COY : d3 ⟶ H.obj a4) (e₂b : d3 ⟶ H.obj a3) (e₂c : d4 ⟶ H.obj a2)
    (e₂fgh : d2 ⟶ H.obj a1)
    (hCOZ : COZ = e₂Z ≫ H.map ΨZ) (hRhT : RhT = H.map IT)
    (Ω : Hc1' ≫ e₂X ≫ RΨ ≫ ΨY = ΨZ ≫ IT) (HP : Hc₁₃ = e₂Z ≫ H.map Hc1' ≫ e₂inv)
    (hCOX : COX = e₂a ≫ RghΨ) (hCOY : COY = e₂b ≫ H.map ΨY)
    (nat : RghΨ ≫ e₂b = e₂c ≫ H.map RΨ) (A : e₂fgh ≫ H.map e₂X = e₂a ≫ e₂c)
    (hi : e₂inv ≫ e₂fgh = 𝟙 _) :
    COZ ≫ RhT = Hc₁₃ ≫ COX ≫ COY := by
  subst hCOZ hRhT HP hCOX hCOY
  calc (e₂Z ≫ H.map ΨZ) ≫ H.map IT = e₂Z ≫ H.map (Hc1' ≫ e₂X ≫ RΨ ≫ ΨY) := by
        rw [Ω, H.map_comp, Category.assoc]
    _ = e₂Z ≫ H.map Hc1' ≫ (e₂inv ≫ e₂fgh) ≫ H.map e₂X ≫ H.map RΨ ≫ H.map ΨY := by
        rw [hi, Category.id_comp]
        simp only [H.map_comp]
    _ = _ := by
        simp only [Category.assoc]
        rw [reassoc_of% A, ← reassoc_of% nat]

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

/-- The two isomorphisms `R(f̄ ≫ ḡ)_* (X ⟶ X̄)_! ≅ i_{Z!} Rg_! Rf_!` in `D⁺(Z̄)`, through `Ȳ` and
through `X̄ ×_Z̄ Z`, agree. -/
theorem tower_Zbar (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekHom Λ (c₁₃' jh jY jX)).app K.obj ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (overBar (jgh jh jY) jX).toBase
          (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl).hom.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (overBar (jgh jh jY) jX).immersion).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (gbar jh jY)).map
          ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K) ≫
      (derivedLowerShriekRestrictBaseIso Λ jh jY).hom.app
          ⟨(derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj,
            isTorsionPlus_derivedLowerShriek_obj Λ f (jf₁ jh jY jX) K.obj K.property⟩ =
    (derivedLowerShriekRestrictBaseIso Λ jh (jXZ jh jY jX)).hom.app K ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ jh.immersion).map
        ((derivedLowerShriekHom Λ (c₃₄ jh jY jX)).app K.obj ≫
          (derivedLowerShriekCompOverIso Λ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
          (derivedLowerShriek.{u, 0} g (jg jh jY) Λ).map
            ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj)) := by
  let hB := isTorsionPlus_derivedLowerShriek_obj Λ f (jf₁ jh jY jX) K.obj K.property
  let ε := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jh.immersion
  have := isIso_derivedLowerShriekHom_app Λ (c₁₃' jh jY jX) K.obj K.property
  have : IsIso ((derivedLowerShriekHom Λ (c₁₃' jh jY jX)).app K.obj ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (overBar (jgh jh jY) jX).toBase
          (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl).hom.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (overBar (jgh jh jY) jX).immersion).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (gbar jh jY)).map
          ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K) ≫
      (derivedLowerShriekRestrictBaseIso Λ jh jY).hom.app ⟨_, hB⟩) :=
    (asIso ((derivedLowerShriekHom Λ (c₁₃' jh jY jX)).app K.obj) ≪≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (overBar (jgh jh jY) jX).toBase
          (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (overBar (jgh jh jY) jX).immersion).obj K.obj) ≪≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (gbar jh jY)).mapIso
          ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).app K) ≪≫
      (derivedLowerShriekRestrictBaseIso Λ jh jY).app ⟨_, hB⟩).isIso_hom
  refine eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_isIso Λ jh.immersion _ _ ?_
  refine (cancel_mono (ε.hom.app _)).mp ?_
  have nε := ε.hom.naturality ((derivedLowerShriekHom Λ (c₃₄ jh jY jX)).app K.obj ≫
    (derivedLowerShriekCompOverIso Λ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
    (derivedLowerShriek.{u, 0} g (jg jh jY) Λ).map
      ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj))
  simp only [Functor.comp_map, Functor.id_map] at nε
  have Nc := map_derivedLowerShriekHom_comp_cube_id Λ (c₁₃' jh jY jX) (fst₃ jh jY jX)
    (restrictBaseι jh (jXZ jh jY jX)) (hcZ₃ jh jY jX)
    (isPullback_restrictBase_overBar jh (jXZ jh jY jX)) (Category.comp_id _).symm
    pullback.condition.symm pullback.condition.symm K
  exact ozb_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jh.immersion)
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ jh.immersion) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedLowerShriekRestrictBaseIso_restrict_cube Λ jh jY ⟨_, hB⟩) (tower_Z Λ jh jY jX K)
    (Nc.trans (Category.comp_id _).symm) rfl nε
    (derivedLowerShriekRestrictBaseIso_restrict_cube Λ jh (jXZ jh jY jX) K)

/-- For the tower `X̄ ⟶ Ȳ ⟶ Z̄` the isomorphism of [Stacks, Tag 0F7J] for `f ≫ g` and `h` through
`X̄`, followed by `Rh_!` of that for `f` and `g` through `X̄ ×_Z̄ Z`, is the isomorphism for `f`
and `g ≫ h` through `X̄`, followed by that for `g` and `h` through `Ȳ`, read through the
comparisons of [Stacks, Tag 0F7I]. -/
theorem tower_core (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompOverIso Λ (f ≫ g) h jh (jXZ jh jY jX)).hom.app K ≫
      (derivedLowerShriek.{u, 0} h jh Λ).map
        ((derivedLowerShriekHom Λ (c₃₄ jh jY jX)).app K.obj ≫
          (derivedLowerShriekCompOverIso Λ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
          (derivedLowerShriek.{u, 0} g (jg jh jY) Λ).map
            ((derivedLowerShriekHom Λ (r₁₄ jh jY jX)).app K.obj)) =
    (derivedLowerShriekHom Λ (c₁₃ jh jY jX)).app K.obj ≫
      (derivedLowerShriekCompOverIso Λ f (g ≫ h) (jgh jh jY) jX).hom.app K ≫
      (derivedLowerShriekCompOverIso Λ g h jh jY).hom.app
        ⟨(derivedLowerShriek.{u, 0} f (jf₁ jh jY jX) Λ).obj K.obj,
          isTorsionPlus_derivedLowerShriek_obj Λ f (jf₁ jh jY jX) K.obj K.property⟩ := by
  let M₁ := (etaleModuleDerivedExtensionByZero.{u, 0} Λ (overBar (jgh jh jY) jX).immersion).obj
    K.obj
  have nat := (etaleModuleDerivedDirectImageComp.{u, 0} Λ jY.toBase jh.toBase
    (jY.toBase ≫ jh.toBase) rfl).hom.naturality
      ((derivedLowerShriekRestrictBaseIso Λ (jgh jh jY) jX).hom.app K)
  have A := congrArg (fun t => NatTrans.app t M₁) (etaleModuleDerivedDirectImageComp_assoc Λ
    (overBar (jgh jh jY) jX).toBase (gbar jh jY) jh.toBase
    ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl (jgh jh jY).toBase rfl
    ((jXZ jh jY jX).toBase ≫ jh.toBase) rfl rfl)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  exact core_chain (etaleModuleDerivedDirectImage.{u, 0} Λ jh.toBase) _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ (derivedLowerShriekCompOverIso_hom_app Λ jh (jXZ jh jY jX) K) rfl
    (tower_Zbar Λ jh jY jX K) (derivedLowerShriekHom_ofFactorHom Λ _ _ _ _ _ _ _ _ _ _)
    (derivedLowerShriekCompOverIso_hom_app Λ (jgh jh jY) jX K)
    (derivedLowerShriekCompOverIso_hom_app Λ jh jY _) nat A (Iso.inv_hom_id_app _ _)

end TowerCore

/-! ### [Stacks, Tag 0F7K] for the compactifications of a tower -/

section IndependenceApp

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory)

/-- A comparison of [Stacks, Tag 0F7I] into the target of a morphism of compactifications. -/
lemma derivedLowerShriekCompactificationIso_hom_app_of_hom_target
    {j k l : CompactificationOf (Over.mk f)} (ψ : k ⟶ l) :
    (derivedLowerShriekCompactificationIso f j l Λ).hom.app K =
      (derivedLowerShriekCompactificationIso f j k Λ).hom.app K ≫
        (derivedLowerShriekHomIso Λ ψ).inv.app K := by
  rw [← derivedLowerShriekCompactificationIso_trans f Λ j k l,
    ← derivedLowerShriekCompactificationIso_symm Λ f l k,
    derivedLowerShriekCompactificationIso_of_hom f Λ ψ]
  rfl

/-- Two comparisons of [Stacks, Tag 0F7I] composing to that along a morphism of
compactifications. -/
lemma derivedLowerShriekCompactificationIso_hom_app_comp_of_hom
    {j k l : CompactificationOf (Over.mk f)} (ψ : l ⟶ j) :
    (derivedLowerShriekCompactificationIso f j k Λ).hom.app K ≫
        (derivedLowerShriekCompactificationIso f k l Λ).hom.app K =
      (derivedLowerShriekHom Λ ψ).app K.obj := by
  have e := derivedLowerShriekCompactificationIso_trans f Λ j k l
  rw [derivedLowerShriekCompactificationIso_of_hom f Λ ψ] at e
  exact NatTrans.congr_app (congrArg Iso.hom e) K

/-- A comparison of [Stacks, Tag 0F7I] out of the target of a morphism of compactifications. -/
lemma derivedLowerShriekCompactificationIso_hom_app_of_hom_source
    {j k l : CompactificationOf (Over.mk f)} (ψ : k ⟶ j) :
    (derivedLowerShriekCompactificationIso f j l Λ).hom.app K =
      (derivedLowerShriekHom Λ ψ).app K.obj ≫
        (derivedLowerShriekCompactificationIso f k l Λ).hom.app K := by
  rw [← derivedLowerShriekCompactificationIso_trans f Λ j k l,
    derivedLowerShriekCompactificationIso_of_hom f Λ ψ]
  rfl

end IndependenceApp

section ThroughApp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  [QuasiCompact f] [QuasiCompact (f ≫ g)]

/-- The components of the isomorphism of [Stacks, Tag 0F7J] through an auxiliary
compactification. -/
lemma derivedLowerShriekCompIso_hom_app_eq (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f g jf jg j).hom.app K =
      (derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX)
          Λ).hom.app K ≫
        (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K ≫
        (derivedLowerShriek.{u, 0} g jg Λ).map
          ((derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX) jf
            Λ).hom.app K) := by
  rw [derivedLowerShriekCompIso_eq_compOver Λ f g jf jg j jX]
  rfl

/-- The isomorphism of [Stacks, Tag 0F7J] for the compactifications `X̄ ×_Ȳ Y` of `f` and
`X̄` of `f ≫ g` is that of `Stacks.EtaleCohomology.derivedLowerShriekCompOverIso`. -/
lemma derivedLowerShriekCompIso_restrictBase_compOver (jg : CompactificationOf (Over.mk g))
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f g (CompactificationOf.restrictBase jg jX) jg
      (CompactificationOf.compOver jg jX)).hom.app K =
      (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K := by
  rw [derivedLowerShriekCompIso_hom_app_eq Λ f g _ jg _ jX,
    derivedLowerShriekCompactificationIso_self,
    derivedLowerShriekCompactificationIso_self]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact (whisker_eq ((derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K)
    (CategoryTheory.Functor.map_id (derivedLowerShriek.{u, 0} g jg Λ) _)).trans (Category.comp_id _)

end ThroughApp

section Tower

open CompactificationOf.Tower

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z]
  [QuasiSeparatedSpace Z] [CompactSpace T] [QuasiSeparatedSpace T] [IsSeparated f]
  [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h]
  [LocallyOfFiniteType h]

/-- A diagram chase for functors `Rg` and `Rh`: given the stated factorizations and commutations,
`core` and the one-sided inverse `hh`, `CIa ≫ CIb = CIc ≫ Rh.map CId`. -/
lemma asm_chain {B C D : Type*} [Category* B] [Category* C] [Category* D] (Rh : C ⥤ D)
    (Rg : B ⥤ C) {b1 bf b4 : B} {c3 cg c4 : C} {d0 d1 d2 d3 d5 : D}
    (CIa : d0 ⟶ d3) (CIb : d3 ⟶ Rh.obj (Rg.obj bf)) (CIc : d0 ⟶ Rh.obj cg)
    (CId : cg ⟶ Rg.obj bf) (a : d0 ⟶ d1) (COX : d1 ⟶ d2) (Rghi : d2 ⟶ d3)
    (COYf : d3 ⟶ Rh.obj (Rg.obj bf)) (COY1 : d2 ⟶ Rh.obj (Rg.obj b1)) (i₁ : b1 ⟶ bf)
    (a3 : d0 ⟶ d5) (COZ : d5 ⟶ Rh.obj c3) (I₃ : c3 ⟶ cg) (I₄ : cg ⟶ c4) (COW : c4 ⟶ Rg.obj b4)
    (I4f : b4 ⟶ bf) (hinv : d1 ⟶ d5) (Hc13 : d5 ⟶ d1) (Hc34 : c3 ⟶ c4) (Hr : b4 ⟶ b1)
    (hL1 : CIa = a ≫ COX ≫ Rghi) (hL2 : CIb = COYf) (hR1 : CIc = a3 ≫ COZ ≫ Rh.map I₃)
    (hR2 : CId = I₄ ≫ COW ≫ Rg.map I4f)
    (nCO : Rghi ≫ COYf = COY1 ≫ Rh.map (Rg.map i₁)) (i1 : a3 = a ≫ hinv)
    (i2 : I₃ ≫ I₄ = Hc34) (i3 : I4f = Hr ≫ i₁)
    (core : COZ ≫ Rh.map (Hc34 ≫ COW ≫ Rg.map Hr) = Hc13 ≫ COX ≫ COY1)
    (hh : hinv ≫ Hc13 = 𝟙 _) :
    CIa ≫ CIb = CIc ≫ Rh.map CId := by
  subst CIa CIb CIc CId a3 I4f Hc34
  calc (a ≫ COX ≫ Rghi) ≫ COYf = a ≫ COX ≫ COY1 ≫ Rh.map (Rg.map i₁) := by
        simp only [Category.assoc, nCO]
    _ = a ≫ hinv ≫ (COZ ≫ Rh.map ((I₃ ≫ I₄) ≫ COW ≫ Rg.map Hr)) ≫ Rh.map (Rg.map i₁) := by
        rw [core]
        simp only [Category.assoc, reassoc_of% hh]
    _ = _ := by simp only [Rh.map_comp, Rg.map_comp, Category.assoc]

/-- For a compactification `Z̄` of `h` and a compactification `Ȳ` of `Y` over `Z̄`, with `Rg_!` and
`R(h ∘ g)_!` computed through `Ȳ ×_Z̄ Z` and `Ȳ`, the two isomorphisms
`R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` built from [Stacks, Tag 0F7J] agree. -/
theorem derivedLowerShriekCompIso_assoc_of_tower (jf : CompactificationOf (Over.mk f))
    (jfg : CompactificationOf (Over.mk (f ≫ g))) (jfgh : CompactificationOf (Over.mk (f ≫ g ≫ h)))
    (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f (g ≫ h) jf (jgh jh jY) jfgh).hom.app K ≫
        (derivedLowerShriekCompIso Λ g h (jg jh jY) jh (jgh jh jY)).hom.app
          ⟨(derivedLowerShriek.{u, 0} f jf Λ).obj K.obj,
            isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩ =
      (derivedLowerShriekCompIso Λ (f ≫ g) h jfg jh jfgh).hom.app K ≫
        (derivedLowerShriek.{u, 0} h jh Λ).map
          ((derivedLowerShriekCompIso Λ f g jf (jg jh jY) jfg).hom.app K) := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : QuasiCompact (g ≫ h) := quasiCompact_of_compactSpace _
  have : QuasiCompact h := quasiCompact_of_compactSpace h
  have : QuasiCompact (f ≫ g ≫ h) := quasiCompact_of_compactSpace _
  have : QuasiCompact ((f ≫ g) ≫ h) := quasiCompact_of_compactSpace _
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f (g ≫ h) (jgh jh jY)
  have hf := isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property
  have h1 := isTorsionPlus_derivedLowerShriek_obj Λ f (jf₁ jh jY jX) K.obj K.property
  have nCO := (derivedLowerShriekCompOverIso Λ g h jh jY).hom.naturality
    (ObjectProperty.homMk (X := ⟨_, h1⟩) (Y := ⟨_, hf⟩)
      ((derivedLowerShriekCompactificationIso f (jf₁ jh jY jX) jf Λ).hom.app K))
  have L1 := derivedLowerShriekCompIso_hom_app_eq Λ f (g ≫ h) jf (jgh jh jY) jfgh jX K
  have L2 := derivedLowerShriekCompIso_restrictBase_compOver Λ g h jh jY ⟨_, hf⟩
  have R1 := derivedLowerShriekCompIso_hom_app_eq Λ (f ≫ g) h jfg jh jfgh (jXZ jh jY jX) K
  have R2 := derivedLowerShriekCompIso_hom_app_eq Λ f g jf (jg jh jY) jfg (jXW jh jY jX) K
  exact asm_chain (derivedLowerShriek.{u, 0} h jh Λ) (derivedLowerShriek.{u, 0} g (jg jh jY) Λ)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L1 L2 R1 R2 nCO
    (derivedLowerShriekCompactificationIso_hom_app_of_hom_target Λ (f ≫ g ≫ h) K
      (c₁₃ jh jY jX))
    (derivedLowerShriekCompactificationIso_hom_app_comp_of_hom Λ (f ≫ g) K (c₃₄ jh jY jX))
    (derivedLowerShriekCompactificationIso_hom_app_of_hom_source Λ f K (r₁₄ jh jY jX))
    (tower_core Λ jh jY jX K)
    (Iso.inv_hom_id_app (derivedLowerShriekHomIso Λ (c₁₃ jh jY jX)) K)

end Tower

end Stacks.EtaleCohomology

end
