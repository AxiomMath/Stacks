module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTransfer

/-!
# Full faithfulness of `colim_F Vect(Y) ⥤ colim_F Vect(X)`

Let `p` be a prime and `f : X ⟶ Y` a morphism of schemes in characteristic `p`, with `Y`
quasi-compact and quasi-separated and `f` proper and surjective with geometrically connected
fibres. This file proves that the functor `colim_F Vect(Y) ⥤ colim_F Vect(X)` induced by pullback
along `f` (`AlgebraicGeometry.frobeniusColimitVectModelPullback`) is fully faithful: this is the
first half of Stacks Tag 0EXH, whose second half describes the essential image.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackComm_comp_pullbackComp`: the coherence between the
  commutation `b^* ⋙ f^* ≅ f^* ⋙ a^*` along `a ≫ f = f ≫ b` and the comparisons `pullbackComp`.
* `AlgebraicGeometry.homTransfer_endoConj`: read through single pullbacks
  (`AlgebraicGeometry.homTransfer`), the functor acts on morphisms by restriction along `f`.
* `AlgebraicGeometry.exists_endoRaise_eq_of_pullback_map_eq` and
  `AlgebraicGeometry.exists_endoConj_eq_endoRaise`: injectivity and surjectivity at a level, from
  `AlgebraicGeometry.exists_twistIter_eq_of_homRes_eq_of_compactSpace` and
  `AlgebraicGeometry.exists_homRes_eq_twistIter_of_qcqs`.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback_map_bijective` and
  `AlgebraicGeometry.frobeniusColimitVectModelPullback_full_faithful`: **the functor is fully
  faithful.**

## Implementation notes

The hypothesis of finite presentation in Stacks Tag 0EXH is not needed for this half.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- **Pullback along a morphism commuting with two endomorphisms, against composition.** For
`f : X ⟶ Y` with `a ≫ f = f ≫ b`, the comparison `b^* ⋙ f^* ≅ f^* ⋙ a^*` followed by the
comparisons for `f ≫ K = L` is the comparison for `f ≫ b ≫ K = a ≫ L`. -/
lemma pullbackComm_comp_pullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (hab : a ≫ f = f ≫ b) (K : Y ⟶ Z) (L : X ⟶ Z) (hL : f ≫ K = L)
    (hL' : f ≫ b ≫ K = a ≫ L) (M : Z.Modules) :
    ((pullbackComp f b).hom ≫ (pullbackCongr hab.symm).hom ≫ (pullbackComp a f).inv).app
        ((pullback K).obj M) ≫
      (pullback a).map ((pullbackComp f K).hom.app M ≫ (pullbackCongr hL).hom.app M) ≫
        (pullbackComp a L).hom.app M =
      (pullback f).map ((pullbackComp b K).hom.app M) ≫ (pullbackComp f (b ≫ K)).hom.app M ≫
        (pullbackCongr hL').hom.app M := by
  let LN : pullback K ⋙ pullback b ⋙ pullback f ⟶ pullback (a ≫ L) :=
    Functor.whiskerLeft (pullback K)
        ((pullbackComp f b).hom ≫ (pullbackCongr hab.symm).hom ≫ (pullbackComp a f).inv) ≫
      Functor.whiskerRight ((pullbackComp f K).hom ≫ (pullbackCongr hL).hom) (pullback a) ≫
        (pullbackComp a L).hom
  let RN : pullback K ⋙ pullback b ⋙ pullback f ⟶ pullback (a ≫ L) :=
    Functor.whiskerRight (pullbackComp b K).hom (pullback f) ≫ (pullbackComp f (b ≫ K)).hom ≫
      (pullbackCongr hL').hom
  let Θ : pullback (f ≫ b ≫ K) ⟶ pullback K ⋙ pullback b ⋙ pullback f :=
    (pullbackComp f (b ≫ K)).inv ≫ Functor.whiskerRight (pullbackComp b K).inv (pullback f)
  have : IsIso Θ := by
    dsimp only [Θ]
    infer_instance
  have hR : IsCanonical (Θ ≫ RN) := by
    have : Θ ≫ RN = (pullbackCongr hL').hom := by
      simp only [Θ, RN, Category.assoc]
      rw [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id, Functor.whiskerRight_id',
        Category.id_comp, Iso.inv_hom_id_assoc]
    exact this ▸ isCanonical_pullbackCongr hL'
  have hB : IsCanonical ((pullbackComp (a ≫ f) K).inv ≫
      Functor.whiskerLeft (pullback K) (pullbackComp a f).inv ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackComp f K).hom (pullback a) ≫
          (pullbackComp a (f ≫ K)).hom) := by
    refine isCanonical_of_comp_eq_id (Category.assoc a f K).symm (isCanonical_assoc a f K) ?_
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp [← Functor.whiskerLeft_comp_assoc, ← Functor.whiskerRight_comp_assoc]
  have hL₁ : IsCanonical (Θ ≫ LN) := by
    have h := isCanonical_comp (isCanonical_assoc f b K)
      (isCanonical_comp (isCanonical_whiskerLeft (isCanonical_pullbackCongr hab.symm) K)
        (isCanonical_comp hB (isCanonical_whiskerRight (isCanonical_pullbackCongr hL) a)))
    convert h using 1
    ext M'
    simp only [Θ, LN, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc, Functor.map_comp]
  simpa [LN, RN] using NatTrans.congr_app ((cancel_epi Θ).mp (hL₁.ext hR)) M

end Scheme.Modules

/-! ### The two sides of the functor in terms of single pullbacks -/

section Sides

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  (hY : IsInCharacteristic Y p)

/-- `E ≅ 𝟙^*E` for a vector bundle on `Y`. -/
def vectIsoY (E : Y.Vect) : E.obj ≅ (Scheme.Modules.pullback (𝟙 Y)).obj E.obj :=
  ((Scheme.Modules.pullbackId Y).app E.obj).symm

/-- `f^* (F_Y^j)^* ≅ (F_X^j ≫ f)^*`, the comparison for `f ≫ (𝟙_Y)_j = f_j`. -/
def frobPullbackComp (j : ℕ) :
    Scheme.Modules.pullback (frobPow p hY (𝟙 Y) j) ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback (frobPow p hY f j) :=
  Scheme.Modules.pullbackComp f _ ≪≫
    Scheme.Modules.pullbackCongr (comp_frobPow f (Category.comp_id f) j)

/-- `(f^*E) ≅ f^*E` for a vector bundle on `Y`, through `E ≅ 𝟙^*E`. -/
def vectIsoX (E : Y.Vect) :
    ((Scheme.Vect.pullback f).obj E).obj ≅ (Scheme.Modules.pullback f).obj E.obj :=
  (Scheme.Modules.pullback f).mapIso (vectIsoY E) ≪≫ (frobPullbackComp f p hY 0).app E.obj

/-- **The iterated commutation of `f^*` with the Frobenius is the canonical comparison.** -/
lemma endoIterCommIso_hom_frobIso (E : Y.Vect) : ∀ j,
    (endoIterCommIso (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) j E).hom.hom ≫
      (frobIso p hY hX f (vectIsoX f p hY E) j).hom =
    (Scheme.Modules.pullback f).map (frobIso p hY hY (𝟙 Y) (vectIsoY E) j).hom ≫
      (frobPullbackComp f p hY j).hom.app E.obj
  | 0 => Category.id_comp _
  | j + 1 => by
    have ih := endoIterCommIso_hom_frobIso E j
    let FX := frobOf p hY (frobPow p hY f j)
    let FY := frobOf p hY (frobPow p hY (𝟙 Y) j)
    have hab : FX ≫ f = f ≫ FY := absoluteFrobenius_naturality f p _ _
    let eM : Scheme.Modules.pullback FY ⋙ Scheme.Modules.pullback f ⟶
        Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback FX :=
      (Scheme.Modules.pullbackComp f FY).hom ≫ (Scheme.Modules.pullbackCongr hab.symm).hom ≫
        (Scheme.Modules.pullbackComp FX f).inv
    let g := (frobIso p hY hY (𝟙 Y) (vectIsoY E) j).hom
    let A := (((frobeniusPullback Y p hY).endoIter j).obj E).obj
    let c := (endoIterCommIso (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) j
      E).hom.hom
    let x := (frobIso p hY hX f (vectIsoX f p hY E) j).hom
    let P := (Scheme.Modules.pullbackComp FX (frobPow p hY f j)).hom.app E.obj
    let γ := (frobPullbackComp f p hY j).hom.app E.obj
    show eM.app A ≫ (Scheme.Modules.pullback FX).map c ≫ (Scheme.Modules.pullback FX).map x ≫ P =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback FY).map g ≫
        (Scheme.Modules.pullbackComp FY (frobPow p hY (𝟙 Y) j)).hom.app E.obj) ≫
      (Scheme.Modules.pullbackComp f (FY ≫ frobPow p hY (𝟙 Y) j)).hom.app E.obj ≫
        (Scheme.Modules.pullbackCongr (comp_frobPow f (Category.comp_id f) (j + 1))).hom.app E.obj
    have hn : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback FY).map g) ≫
        eM.app ((Scheme.Modules.pullback (frobPow p hY (𝟙 Y) j)).obj E.obj) =
        eM.app A ≫ (Scheme.Modules.pullback FX).map ((Scheme.Modules.pullback f).map g) :=
      eM.naturality g
    have hK := Scheme.Modules.pullbackComm_comp_pullbackComp f FX FY hab (frobPow p hY (𝟙 Y) j)
      (frobPow p hY f j) (comp_frobPow f (Category.comp_id f) j)
      (comp_frobPow f (Category.comp_id f) (j + 1)) E.obj
    calc eM.app A ≫ (Scheme.Modules.pullback FX).map c ≫ (Scheme.Modules.pullback FX).map x ≫ P
        = eM.app A ≫ (Scheme.Modules.pullback FX).map (c ≫ x) ≫ P :=
          congrArg (eM.app A ≫ ·) (Functor.map_comp_assoc _ _ _ _).symm
      _ = eM.app A ≫ (Scheme.Modules.pullback FX).map
            ((Scheme.Modules.pullback f).map g ≫ γ) ≫ P :=
          congrArg (fun t ↦ eM.app A ≫ (Scheme.Modules.pullback FX).map t ≫ P) ih
      _ = (eM.app A ≫ (Scheme.Modules.pullback FX).map ((Scheme.Modules.pullback f).map g)) ≫
            (Scheme.Modules.pullback FX).map γ ≫ P := by
          rw [Functor.map_comp, Category.assoc, Category.assoc]
      _ = (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback FY).map g) ≫
            (eM.app ((Scheme.Modules.pullback (frobPow p hY (𝟙 Y) j)).obj E.obj) ≫
              (Scheme.Modules.pullback FX).map γ ≫ P) :=
          (congrArg (· ≫ (Scheme.Modules.pullback FX).map γ ≫ P) hn.symm).trans
            (Category.assoc _ _ _)
      _ = _ := (congrArg ((Scheme.Modules.pullback f).map
            ((Scheme.Modules.pullback FY).map g) ≫ ·) hK).trans
          (Functor.map_comp_assoc _ _ _ _).symm

/-- Conjugations by two factorizations of the same isomorphisms agree. -/
lemma conj_eq_of_comp_eq {C : Type*} [Category C] {A₁ A₂ B₁ B₂ D₁ D₂ : C} (a₁ : A₁ ≅ B₁)
    (b₁ : B₁ ≅ D₁) (c₁ : A₁ ≅ D₁) (h₁ : a₁.hom ≫ b₁.hom = c₁.hom) (a₂ : A₂ ≅ B₂) (b₂ : B₂ ≅ D₂)
    (c₂ : A₂ ≅ D₂) (h₂ : a₂.hom ≫ b₂.hom = c₂.hom) (φ : A₁ ⟶ A₂) :
    b₁.inv ≫ (a₁.inv ≫ φ ≫ a₂.hom) ≫ b₂.hom = c₁.inv ≫ φ ≫ c₂.hom := by
  have e₁ : a₁ ≪≫ b₁ = c₁ := Iso.ext h₁
  have e₂ : a₂ ≪≫ b₂ = c₂ := Iso.ext h₂
  subst e₁ e₂
  simp

/-- Restriction along `f` of a transferred morphism. -/
lemma homRes_homTransfer (j : ℕ) {E G : Y.Vect}
    (φ : ((frobeniusPullback Y p hY).endoIter j).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter j).obj G) :
    homRes f (comp_frobPow f (Category.comp_id f) j)
        (homTransfer p hY hY (𝟙 Y) (vectIsoY E) (vectIsoY G) j φ) =
      ((Scheme.Modules.pullback f).mapIso (frobIso p hY hY (𝟙 Y) (vectIsoY E) j) ≪≫
          (frobPullbackComp f p hY j).app E.obj).inv ≫ (Scheme.Modules.pullback f).map φ.hom ≫
        ((Scheme.Modules.pullback f).mapIso (frobIso p hY hY (𝟙 Y) (vectIsoY G) j) ≪≫
          (frobPullbackComp f p hY j).app G.obj).hom := by
  simp only [homRes, homTransfer, frobPullbackComp, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]

/-- **The functor on morphisms, read through single pullbacks, is restriction along `f`.** -/
lemma homTransfer_endoConj (j : ℕ) {E G : Y.Vect}
    (φ : ((frobeniusPullback Y p hY).endoIter j).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter j).obj G) :
    homTransfer p hY hX f (vectIsoX f p hY E) (vectIsoX f p hY G) j
        (endoConj (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
          ((Scheme.Vect.pullback f).map φ)) =
      homRes f (comp_frobPow f (Category.comp_id f) j)
        (homTransfer p hY hY (𝟙 Y) (vectIsoY E) (vectIsoY G) j φ) := by
  refine (conj_eq_of_comp_eq
    ((ObjectProperty.ι _).mapIso
      (endoIterCommIso (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) j E))
    (frobIso p hY hX f (vectIsoX f p hY E) j)
    ((Scheme.Modules.pullback f).mapIso (frobIso p hY hY (𝟙 Y) (vectIsoY E) j) ≪≫
      (frobPullbackComp f p hY j).app E.obj) (endoIterCommIso_hom_frobIso f p hX hY E j)
    ((ObjectProperty.ι _).mapIso
      (endoIterCommIso (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) j G))
    (frobIso p hY hX f (vectIsoX f p hY G) j)
    ((Scheme.Modules.pullback f).mapIso (frobIso p hY hY (𝟙 Y) (vectIsoY G) j) ≪≫
      (frobPullbackComp f p hY j).app G.obj) (endoIterCommIso_hom_frobIso f p hX hY G j)
    ((Scheme.Modules.pullback f).map φ.hom)).trans (homRes_homTransfer f p hY j φ).symm

end Sides

/-! ### Transport along the identity is injective -/

/-- Transport along the identity, from `HomAt K A B` to `HomAt K' A B` for `𝟙 T ≫ K = K'`, is
injective. -/
lemma homRes_one_injective {Y T : Scheme.{u}} {K K' : T ⟶ Y} (h : 𝟙 T ≫ K = K') {A B : Y.Modules} :
    Function.Injective (homRes (𝟙 T) h : HomAt K A B → HomAt K' A B) := by
  intro x y hxy
  have h2 : 𝟙 T ≫ K' = K := by rw [← h, Category.id_comp, Category.id_comp]
  have := congrArg (homRes (𝟙 T) h2) hxy
  rwa [homRes_one_one, homRes_one_one, homRes_one, homRes_one] at this

/-- Restriction along `u` with `u ≫ K = K'` is restriction along `u` to `HomAt (u ≫ K) A B`
followed by transport along the identity to `HomAt K' A B`. -/
lemma homRes_eq_homRes_one_homRes {Y T T' : Scheme.{u}} (u : T' ⟶ T) {K : T ⟶ Y} {K' : T' ⟶ Y}
    (hu : u ≫ K = K') {A B : Y.Modules} (φ : HomAt K A B) :
    homRes u hu φ = homRes (𝟙 T') (by rw [Category.id_comp, hu]) (homRes u rfl φ) := by
  rw [homRes_homRes]
  exact homRes_congr (Category.id_comp u).symm _ _ φ

/-! ### Injectivity and surjectivity at a level -/

section Level

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  (hY : IsInCharacteristic Y p)

/-- **Injectivity at a level**: morphisms of vector bundles on `Y` with equal pullbacks to `X`
become equal after a Frobenius twist, for `f` surjective and `Y` quasi-compact. -/
theorem exists_endoRaise_eq_of_pullback_map_eq [CompactSpace Y] [Surjective f] (J : ℕ)
    {E G : Y.Vect} (a b : ((frobeniusPullback Y p hY).endoIter J).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter J).obj G)
    (h : (Scheme.Vect.pullback f).map a = (Scheme.Vect.pullback f).map b) :
    ∃ m, endoRaise a m = endoRaise b m := by
  have hX : IsInCharacteristic X p := isInCharacteristic_of_hom f p hY
  have hres := (homTransfer_endoConj f p hX hY J a).symm.trans
    ((congrArg (fun t ↦ homTransfer p hY hX f (vectIsoX f p hY E) (vectIsoX f p hY G) J
      (endoConj (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY) t)) h).trans
      (homTransfer_endoConj f p hX hY J b))
  have hres' : homRes f rfl (homTransfer p hY hY (𝟙 Y) (vectIsoY E) (vectIsoY G) J a) =
      homRes f rfl (homTransfer p hY hY (𝟙 Y) (vectIsoY E) (vectIsoY G) J b) :=
    homRes_one_injective _ ((homRes_eq_homRes_one_homRes f _ _).symm.trans
      (hres.trans (homRes_eq_homRes_one_homRes f _ _)))
  obtain ⟨m, hm⟩ := exists_twistIter_eq_of_homRes_eq_of_compactSpace (p := p) (hY := hY)
    (frobPow p hY (𝟙 Y) J) f
    ((hasLocalDecomp_of_isFiniteLocallyFree E.obj E.property).frobPow J)
    ((hasLocalDecomp_of_isFiniteLocallyFree G.obj G.property).frobPow J) _ _ hres'
  refine ⟨m, homTransfer_injective (hY := hY) hY (𝟙 Y) (vectIsoY E) (vectIsoY G) (J + m) ?_⟩
  exact (homTransfer_endoRaise hY (𝟙 Y) _ _ J a m).trans
    ((congrArg (homRes (𝟙 Y) _) hm).trans (homTransfer_endoRaise hY (𝟙 Y) _ _ J b m).symm)

/-- **Surjectivity at a level**: a morphism between Frobenius pullbacks of pullbacks to `X` of
vector bundles on `Y` comes from `Y` after a Frobenius twist, for `Y` quasi-compact and
quasi-separated and `f` proper and surjective with geometrically connected fibres. -/
theorem exists_endoConj_eq_endoRaise [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
    [Surjective f] [GeometricallyConnected f] (J : ℕ) {E G : Y.Vect}
    (χ : ((frobeniusPullback X p hX).endoIter J).obj ((Scheme.Vect.pullback f).obj E) ⟶
      ((frobeniusPullback X p hX).endoIter J).obj ((Scheme.Vect.pullback f).obj G)) :
    ∃ L, ∃ a : ((frobeniusPullback Y p hY).endoIter (J + L)).obj E ⟶
        ((frobeniusPullback Y p hY).endoIter (J + L)).obj G,
      endoConj (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
        ((Scheme.Vect.pullback f).map a) = endoRaise χ L := by
  let c := homTransfer p hY hX f (vectIsoX f p hY E) (vectIsoX f p hY G) J χ
  have h0 : 𝟙 X ≫ frobPow p hY f J = f ≫ frobPow p hY (𝟙 Y) J := by
    rw [Category.id_comp, comp_frobPow f (Category.comp_id f) J]
  obtain ⟨L, t, ht⟩ := exists_homRes_eq_twistIter_of_qcqs (p := p) (hY := hY)
    (frobPow p hY (𝟙 Y) J) f
    ((hasLocalDecomp_of_isFiniteLocallyFree E.obj E.property).frobPow J)
    ((hasLocalDecomp_of_isFiniteLocallyFree G.obj G.property).frobPow J) (homRes (𝟙 X) h0 c)
  have h2 : 𝟙 Y ≫ frobPow p hY (frobPow p hY (𝟙 Y) J) L = frobPow p hY (𝟙 Y) (J + L) := by
    rw [Category.id_comp, frobPow_add]
  have h3 : 𝟙 X ≫ frobPow p hY (f ≫ frobPow p hY (𝟙 Y) J) L = frobPow p hY f (J + L) := by
    rw [Category.id_comp, ← comp_frobPow f rfl L, ← comp_frobPow f (Category.comp_id f) (J + L),
      ← frobPow_add]
  obtain ⟨a, ha⟩ := homTransfer_surjective (hY := hY) hY (𝟙 Y) (vectIsoY E) (vectIsoY G) (J + L)
    (homRes (𝟙 Y) h2 t)
  refine ⟨L, a, homTransfer_injective (hY := hY) hX f (vectIsoX f p hY E) (vectIsoX f p hY G)
    (J + L) ?_⟩
  calc homTransfer p hY hX f (vectIsoX f p hY E) (vectIsoX f p hY G) (J + L)
        (endoConj (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
          ((Scheme.Vect.pullback f).map a))
      = homRes f (comp_frobPow f (Category.comp_id f) (J + L)) (homRes (𝟙 Y) h2 t) :=
        (homTransfer_endoConj f p hX hY (J + L) a).trans (congrArg _ ha)
    _ = homRes (𝟙 X) h3 (homRes f (comp_frobPow f rfl L) t) :=
        homRes_homRes_eq_of_comp (𝟙 Y) f f (𝟙 X) (by rw [Category.comp_id, Category.id_comp])
          h2 _ _ h3 t
    _ = homRes (𝟙 X) h3 (homRes (𝟙 X) (comp_frobPow (𝟙 X) h0 L) (twistIter p hY L c)) :=
        congrArg (homRes (𝟙 X) h3) (ht.trans (homRes_twistIter (𝟙 X) h0 L c).symm)
    _ = _ := (homRes_one_one _ _ _).trans
        (homTransfer_endoRaise hX f (vectIsoX f p hY E) (vectIsoX f p hY G) J χ L).symm

/-- The functor sends the morphism presented at level `k` by `a` to the one presented by the
conjugate of the pullback of `a`. -/
private lemma frobeniusColimitVectModelPullback_map_of [CompactSpace Y] (n k : ℕ) {E G : Y.Vect}
    (a : ((frobeniusPullback Y p hY).endoIter (n + k)).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter (n + k)).obj G) :
    (frobeniusColimitVectModelPullback f p hX hY).map
        (EndoColim.Hom.of (A := (⟨E, n⟩ : frobeniusColimitVectModel Y p hY)) (B := ⟨G, n⟩) k a) =
      EndoColim.Hom.of
        (A := (⟨(Scheme.Vect.pullback f).obj E, n⟩ : frobeniusColimitVectModel X p hX))
        (B := ⟨(Scheme.Vect.pullback f).obj G, n⟩) k
        (endoConj (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
          ((Scheme.Vect.pullback f).map a)) :=
  rfl

/-- Injectivity on the Hom-sets between objects at one and the same stage. -/
theorem frobeniusColimitVectModelPullback_map_injective_stage [CompactSpace Y] [Surjective f]
    (n : ℕ) (E G : Y.Vect) :
    Function.Injective (fun u : (⟨E, n⟩ : frobeniusColimitVectModel Y p hY) ⟶ ⟨G, n⟩ ↦
      (frobeniusColimitVectModelPullback f p hX hY).map u) := by
  intro u v huv
  obtain ⟨k, a, rfl⟩ := EndoColim.Hom.exists_of u
  obtain ⟨l, b, rfl⟩ := EndoColim.Hom.exists_of v
  have h0 := ((frobeniusColimitVectModelPullback_map_of f p hX hY n k a).symm.trans huv).trans
    (frobeniusColimitVectModelPullback_map_of f p hX hY n l b)
  obtain ⟨j, i, hji, hab⟩ := (EndoColim.Hom.of_eq_of_iff _ _).mp h0
  have hji' : k + j = l + i := hji
  have hk : n + k + j = n + (l + i) := by omega
  have hl : n + l + i = n + (l + i) := by omega
  let a' : ((frobeniusPullback Y p hY).endoIter (n + (l + i))).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter (n + (l + i))).obj G :=
    endoHomCast hk hk (endoRaise a j)
  let b' : ((frobeniusPullback Y p hY).endoIter (n + (l + i))).obj E ⟶
      ((frobeniusPullback Y p hY).endoIter (n + (l + i))).obj G :=
    endoHomCast hl hl (endoRaise b i)
  have hG : (Scheme.Vect.pullback f).map a' = (Scheme.Vect.pullback f).map b' :=
    endoConj_injective (G := Scheme.Vect.pullback f) (e := frobeniusVectPullbackIso f p hX hY)
      ((endoConj_map_endoHomCast _ _ _).trans
        ((congrArg (endoHomCast _ _) (endoConj_map_endoRaise a j)).trans (hab.trans
          ((congrArg (endoHomCast _ _) (endoConj_map_endoRaise b i)).symm.trans
            (endoConj_map_endoHomCast _ _ _).symm))))
  obtain ⟨m, hm⟩ := exists_endoRaise_eq_of_pullback_map_eq f p hY (n + (l + i)) a' b' hG
  have e1 : (EndoColim.Hom.of (A := (⟨E, n⟩ : frobeniusColimitVectModel Y p hY))
      (B := ⟨G, n⟩) k a) = EndoColim.Hom.of (l + i) a' :=
    EndoColim.Hom.of_eq_of a a' j 0 (by omega)
      (endoHomCast_endoHomCast hk hk _ _ (endoRaise a j)).symm
  have e2 : (EndoColim.Hom.of (A := (⟨E, n⟩ : frobeniusColimitVectModel Y p hY))
      (B := ⟨G, n⟩) (l + i) a') = EndoColim.Hom.of (l + i) b' :=
    EndoColim.Hom.of_eq_of (A := (⟨E, n⟩ : frobeniusColimitVectModel Y p hY)) (B := ⟨G, n⟩)
      a' b' m m rfl (congrArg (endoHomCast _ _) hm)
  exact e1.trans (e2.trans (EndoColim.Hom.of_raise l b i))

/-- Surjectivity on the Hom-sets between objects at one and the same stage. -/
theorem frobeniusColimitVectModelPullback_map_surjective_stage [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsProper f] [Surjective f] [GeometricallyConnected f]
    (n : ℕ) (E G : Y.Vect) :
    Function.Surjective (fun u : (⟨E, n⟩ : frobeniusColimitVectModel Y p hY) ⟶ ⟨G, n⟩ ↦
      (frobeniusColimitVectModelPullback f p hX hY).map u) := by
  intro w
  obtain ⟨k, χ, rfl⟩ := EndoColim.Hom.exists_of w
  obtain ⟨L, a, ha⟩ := exists_endoConj_eq_endoRaise f p hX hY (n + k) χ
  have hc : n + k + L = n + (k + L) := by omega
  refine ⟨EndoColim.Hom.of (k + L) (endoHomCast hc hc a),
    (frobeniusColimitVectModelPullback_map_of f p hX hY n (k + L) _).trans ?_⟩
  exact (congrArg (EndoColim.Hom.of (k + L)) ((endoConj_map_endoHomCast _ _ a).trans
    (congrArg (endoHomCast _ _) ha))).trans (EndoColim.Hom.of_raise k χ L)

/-- **The functor `colim_F Vect(Y) ⥤ colim_F Vect(X)` is bijective on all Hom-sets** for
`Y` quasi-compact and quasi-separated and `f` proper and surjective with geometrically connected
fibres. -/
theorem frobeniusColimitVectModelPullback_map_bijective [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsProper f] [Surjective f] [GeometricallyConnected f]
    (A B : frobeniusColimitVectModel Y p hY) :
    Function.Bijective (fun u : A ⟶ B ↦ (frobeniusColimitVectModelPullback f p hX hY).map u) :=
  EndoColim.bijective_desc_map _ (fun n E G ↦
    ⟨frobeniusColimitVectModelPullback_map_injective_stage f p hX hY n E G,
      frobeniusColimitVectModelPullback_map_surjective_stage f p hX hY n E G⟩) A B

/-- **Stacks Tag 0EXH, part (1).** Let `p` be a prime and `f : X ⟶ Y` a morphism of schemes in
characteristic `p`, with `Y` quasi-compact and quasi-separated and `f` proper and surjective with
geometrically connected fibres. Then the functor `colim_F Vect(Y) ⥤ colim_F Vect(X)` induced by
pullback along `f` is fully faithful. -/
theorem frobeniusColimitVectModelPullback_full_faithful [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsProper f] [Surjective f] [GeometricallyConnected f] :
    (frobeniusColimitVectModelPullback f p hX hY).Full ∧
      (frobeniusColimitVectModelPullback f p hX hY).Faithful :=
  ⟨⟨fun {A B} ↦ (frobeniusColimitVectModelPullback_map_bijective f p hX hY A B).2⟩,
    ⟨fun {A B} ↦ (frobeniusColimitVectModelPullback_map_bijective f p hX hY A B).1⟩⟩

end Level

end AlgebraicGeometry

end
