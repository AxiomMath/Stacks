module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites

/-!
# The Yoneda argument for the duality formula `a(M) ≅ R𝓗om(Lf^* D(M), a(K))`

Let `𝒳`, `𝒴` be categories with tensor bifunctors `T`, internal hom bifunctors `H` and
tensor–hom bijections `(A ⟶ H(B, Z)) ≃ (T(A, B) ⟶ Z)` natural in `A` and `B`. Let
`π : 𝒳 ⥤ 𝒴` and `p : 𝒴 ⥤ 𝒳`, let `a` be right adjoint to `π` between full subcategories
`P_𝒳`, `P_𝒴`, let `ρ : T(πF, D) ⟶ π T(F, pD)` be a projection formula map, invertible on
`P_𝒳 × P_𝒴`, and let `β : M ⟶ H(H(M, K), K)` be a natural biduality morphism. On a class `𝓜` of
objects on which `β` is invertible and the relevant objects lie in `P_𝒳`, `P_𝒴`, the chain of
bijections of [Stacks, Tag 0AU2]

`Hom(F, H(pD(M), aK)) = Hom(T(F, pD(M)), aK) = Hom(π T(F, pD(M)), K) = Hom(T(πF, D(M)), K)`
`= Hom(πF, D(D(M))) = Hom(πF, M) = Hom(F, aM)`

is natural in `F ∈ P_𝒳` and in `M ∈ 𝓜`, so Yoneda's lemma gives a natural isomorphism
`a(M) ≅ H(p D(M), a(K))`.

## Main definitions

* `CategoryTheory.DualityFormula.isoOfHomEquiv`, `natIsoOfHomEquiv`: Yoneda's lemma restricted to
  the objects with a property.
* `CategoryTheory.DualityFormula.transportedHomEquiv`: the adjunction bijection of an adjunction
  between full subcategories, read through equivalences of the ambient categories.
* `CategoryTheory.DualityFormula.dualityFormulaIso`: the natural isomorphism
  `a(M) ≅ H(p D(M), a(K))`.

## Main results

* `CategoryTheory.DualityFormula.transportedHomEquiv_eq_of_fac`: the transported bijection
  through a factorization in the target model.
* `CategoryTheory.DualityFormula.dualityFormulaIso_hom_app`,
  `CategoryTheory.DualityFormula.cX_dualityFormulaIso_hom_app`: the components of
  `dualityFormulaIso`, and their transposes.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.DualityFormula

/-! ### Yoneda's lemma on the objects with a property -/

section Yoneda

variable {C : Type*} [Category C] (P : ObjectProperty C)

/-- Two objects with property `P` with bijections `(F ⟶ A) ≃ (F ⟶ B)` for the objects `F` with
property `P`, natural in `F`, are isomorphic. -/
def isoOfHomEquiv {A B : C} (hA : P A) (hB : P B)
    (e : ∀ F, P F → ((F ⟶ A) ≃ (F ⟶ B)))
    (he : ∀ {F F'} (hF : P F) (hF' : P F') (g : F' ⟶ F) (h : F ⟶ A),
      e F' hF' (g ≫ h) = g ≫ e F hF h) :
    A ≅ B where
  hom := e A hA (𝟙 A)
  inv := (e B hB).symm (𝟙 B)
  hom_inv_id := (e A hA).injective (by rw [he hB hA, Equiv.apply_symm_apply, Category.comp_id])
  inv_hom_id := by rw [← he hA hB, Category.comp_id, Equiv.apply_symm_apply]

/-- A family of bijections `(F ⟶ Φ m) ≃ (F ⟶ Ψ m)`, for the objects `F` with property `P`,
natural in `F` and in `m`, comes from an isomorphism of functors `Φ ≅ Ψ`. -/
def natIsoOfHomEquiv {𝓜 : Type*} [Category 𝓜] (Φ Ψ : 𝓜 ⥤ C) (hΦ : ∀ m, P (Φ.obj m))
    (hΨ : ∀ m, P (Ψ.obj m)) (e : ∀ m F, P F → ((F ⟶ Φ.obj m) ≃ (F ⟶ Ψ.obj m)))
    (he : ∀ m {F F'} (hF : P F) (hF' : P F') (g : F' ⟶ F) (h : F ⟶ Φ.obj m),
      e m F' hF' (g ≫ h) = g ≫ e m F hF h)
    (he' : ∀ {m m'} (φ : m ⟶ m') F (hF : P F) (h : F ⟶ Φ.obj m),
      e m' F hF (h ≫ Φ.map φ) = e m F hF h ≫ Ψ.map φ) :
    Φ ≅ Ψ :=
  NatIso.ofComponents (fun m => isoOfHomEquiv P (hΦ m) (hΨ m) (e m) (he m)) (by
    intro m m' φ
    change Φ.map φ ≫ e m' _ (hΦ m') (𝟙 _) = e m _ (hΦ m) (𝟙 _) ≫ Ψ.map φ
    rw [← he m' (hΦ m') (hΦ m), ← he' φ _ (hΦ m), Category.comp_id, Category.id_comp])

/-- The components of `natIsoOfHomEquiv` are the images of identities. -/
theorem natIsoOfHomEquiv_hom_app {𝓜 : Type*} [Category 𝓜] (Φ Ψ : 𝓜 ⥤ C)
    (hΦ : ∀ m, P (Φ.obj m)) (hΨ : ∀ m, P (Ψ.obj m))
    (e : ∀ m F, P F → ((F ⟶ Φ.obj m) ≃ (F ⟶ Ψ.obj m)))
    (he : ∀ m {F F'} (hF : P F) (hF' : P F') (g : F' ⟶ F) (h : F ⟶ Φ.obj m),
      e m F' hF' (g ≫ h) = g ≫ e m F hF h)
    (he' : ∀ {m m'} (φ : m ⟶ m') F (hF : P F) (h : F ⟶ Φ.obj m),
      e m' F hF (h ≫ Φ.map φ) = e m F hF h ≫ Ψ.map φ) (m : 𝓜) :
    (natIsoOfHomEquiv P Φ Ψ hΦ hΨ e he he').hom.app m = e m _ (hΦ m) (𝟙 _) :=
  rfl

end Yoneda

/-! ### Composition with invertible morphisms -/

section Comp

variable {C : Type*} [Category C]

/-- Precomposition with an isomorphism `i : X ⟶ Y`, as a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. -/
@[simps]
def precompEquiv {X Y Z : C} (i : X ⟶ Y) [IsIso i] : (Y ⟶ Z) ≃ (X ⟶ Z) where
  toFun h := i ≫ h
  invFun h := inv i ≫ h
  left_inv h := by simp
  right_inv h := by simp

/-- Postcomposition with an isomorphism `i : Y ⟶ Z`, as a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`. -/
@[simps]
def postcompEquiv {X Y Z : C} (i : Y ⟶ Z) [IsIso i] : (X ⟶ Y) ≃ (X ⟶ Z) where
  toFun h := h ≫ i
  invFun h := h ≫ inv i
  left_inv h := by simp
  right_inv h := by simp

end Comp

/-! ### A projection formula map read through isomorphisms of tensor bifunctors -/

section Conjugate

variable {𝒳 𝒴 : Type*} [Category 𝒳] [Category 𝒴] {TX TX' : 𝒳 ⥤ 𝒳 ⥤ 𝒳}
  {TY TY' : 𝒴 ⥤ 𝒴 ⥤ 𝒴} (eX : TX' ≅ TX) (eY : TY' ≅ TY) (π : 𝒳 ⥤ 𝒴) (p : 𝒴 ⥤ 𝒳)
  (ρ' : ∀ F D, (TY'.obj (π.obj F)).obj D ⟶ π.obj ((TX'.obj F).obj (p.obj D)))

/-- A map `T'(π F, D) ⟶ π T'(F, p D)` read through isomorphisms `T' ≅ T` of tensor bifunctors
on both sides. -/
def conjugateProjection (F : 𝒳) (D : 𝒴) :
    (TY.obj (π.obj F)).obj D ⟶ π.obj ((TX.obj F).obj (p.obj D)) :=
  (eY.inv.app (π.obj F)).app D ≫ ρ' F D ≫ π.map ((eX.hom.app F).app (p.obj D))

/-- If `ρ'` is natural in `F`, then so is `conjugateProjection`. -/
theorem conjugateProjection_natural_left
    (hρ' : ∀ {F F' : 𝒳} (g : F' ⟶ F) (D : 𝒴),
      (TY'.map (π.map g)).app D ≫ ρ' F D = ρ' F' D ≫ π.map ((TX'.map g).app (p.obj D)))
    {F F' : 𝒳} (g : F' ⟶ F) (D : 𝒴) :
    (TY.map (π.map g)).app D ≫ conjugateProjection eX eY π p ρ' F D =
      conjugateProjection eX eY π p ρ' F' D ≫ π.map ((TX.map g).app (p.obj D)) := by
  have h1 := congrArg (fun φ => NatTrans.app φ D) (eY.inv.naturality (π.map g))
  have h2 := congrArg (fun φ => NatTrans.app φ (p.obj D)) (eX.hom.naturality g)
  simp only [NatTrans.comp_app] at h1 h2
  simp only [conjugateProjection, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% (hρ' g D), ← π.map_comp, ← π.map_comp, h2]

/-- If `ρ'` is natural in `D`, then so is `conjugateProjection`. -/
theorem conjugateProjection_natural_right
    (hρ' : ∀ (F : 𝒳) {D D' : 𝒴} (d : D ⟶ D'),
      (TY'.obj (π.obj F)).map d ≫ ρ' F D' = ρ' F D ≫ π.map ((TX'.obj F).map (p.map d)))
    (F : 𝒳) {D D' : 𝒴} (d : D ⟶ D') :
    (TY.obj (π.obj F)).map d ≫ conjugateProjection eX eY π p ρ' F D' =
      conjugateProjection eX eY π p ρ' F D ≫ π.map ((TX.obj F).map (p.map d)) := by
  simp only [conjugateProjection, Category.assoc]
  rw [reassoc_of% ((eY.inv.app (π.obj F)).naturality d), reassoc_of% (hρ' F d), ← π.map_comp,
    ← π.map_comp, (eX.hom.app F).naturality (p.map d)]

/-- `conjugateProjection` is invertible at `(F, D)` whenever `ρ' F D` is. -/
theorem isIso_conjugateProjection (F : 𝒳) (D : 𝒴) (h : IsIso (ρ' F D)) :
    IsIso (conjugateProjection eX eY π p ρ' F D) := by
  unfold conjugateProjection
  infer_instance

end Conjugate

/-! ### An adjunction between full subcategories read through equivalences -/

section Transport

variable {𝒳 𝒴 𝒳' 𝒴' : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒳'] [Category 𝒴']
  (EX : 𝒳 ≌ 𝒳') (EY : 𝒴 ≌ 𝒴') (π : 𝒳 ⥤ 𝒴) (π' : 𝒳' ⥤ 𝒴')
  (eπ : π ⋙ EY.functor ≅ EX.functor ⋙ π') (PX' : ObjectProperty 𝒳') (PY' : ObjectProperty 𝒴')
  (πQ : PX'.FullSubcategory ⥤ PY'.FullSubcategory) (eQ : πQ ⋙ PY'.ι ≅ PX'.ι ⋙ π')
  (a' : PY'.FullSubcategory ⥤ PX'.FullSubcategory) (adj : πQ ⊣ a')

/-- The property of objects of `𝒴` whose image under `EY` has property `PY'`. -/
abbrev transportedProperty : ObjectProperty 𝒴 := fun M => PY' (EY.functor.obj M)

/-- The right adjoint `a'`, read on `𝒴` and `𝒳` through the equivalences. -/
def transportedRightAdjoint : (transportedProperty EY PY').FullSubcategory ⥤ 𝒳 :=
  PY'.lift ((transportedProperty EY PY').ι ⋙ EY.functor) (fun M => M.property) ⋙ a' ⋙
    PX'.ι ⋙ EX.inverse

/-- The adjunction bijection of `πQ ⊣ a'`, read on `𝒳` and `𝒴` through the equivalences:
`(π F ⟶ M) ≃ (F ⟶ a M)` for `F` and `M` whose images have the properties. -/
def transportedHomEquiv (M : (transportedProperty EY PY').FullSubcategory) (F : 𝒳)
    (hF : PX' (EX.functor.obj F)) :
    (π.obj F ⟶ M.obj) ≃ (F ⟶ (transportedRightAdjoint EX EY PX' PY' a').obj M) :=
  EY.fullyFaithfulFunctor.homEquiv.trans
    ((precompEquiv (eπ.inv.app F)).trans
      ((precompEquiv (eQ.hom.app ⟨EX.functor.obj F, hF⟩)).trans
        ((PY'.fullyFaithfulι.homEquiv (X := πQ.obj ⟨EX.functor.obj F, hF⟩)
            (Y := ⟨EY.functor.obj M.obj, M.property⟩)).symm.trans
          ((adj.homEquiv _ _).trans
            (PX'.fullyFaithfulι.homEquiv.trans (EX.toAdjunction.homEquiv _ _))))))

/-- `transportedHomEquiv` sends `h : π F ⟶ M` to the transpose under `EX` of the
`πQ ⊣ a'`-transpose of `eQ ≫ eπ⁻¹ ≫ EY h`. -/
theorem transportedHomEquiv_apply (M : (transportedProperty EY PY').FullSubcategory) (F : 𝒳)
    (hF : PX' (EX.functor.obj F)) (h : π.obj F ⟶ M.obj) :
    transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M F hF h =
      EX.toAdjunction.homEquiv F _
        (adj.homEquiv ⟨EX.functor.obj F, hF⟩ ⟨EY.functor.obj M.obj, M.property⟩
          (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F, hF⟩ ≫ eπ.inv.app F ≫
            EY.functor.map h))).hom :=
  rfl

variable {EX EY π π' eπ PX' PY' πQ eQ a' adj}

/-- `transportedHomEquiv` is natural in `F`: precomposition with `π g` corresponds to
precomposition with `g`. -/
theorem transportedHomEquiv_naturality_left (M : (transportedProperty EY PY').FullSubcategory)
    {F F' : 𝒳} (hF : PX' (EX.functor.obj F)) (hF' : PX' (EX.functor.obj F')) (g : F' ⟶ F)
    (h : π.obj F ⟶ M.obj) :
    transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M F' hF' (π.map g ≫ h) =
      g ≫ transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M F hF h := by
  let gQ : (⟨EX.functor.obj F', hF'⟩ : PX'.FullSubcategory) ⟶ ⟨EX.functor.obj F, hF⟩ :=
    ObjectProperty.homMk (EX.functor.map g)
  have h1 : eπ.inv.app F' ≫ EY.functor.map (π.map g) = π'.map (EX.functor.map g) ≫ eπ.inv.app F :=
    (eπ.inv.naturality g).symm
  have h2 : eQ.hom.app ⟨EX.functor.obj F', hF'⟩ ≫ π'.map (EX.functor.map g) =
      (πQ.map gQ).hom ≫ eQ.hom.app ⟨EX.functor.obj F, hF⟩ :=
    (eQ.hom.naturality gQ).symm
  have e1 : (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F', hF'⟩ ≫ eπ.inv.app F' ≫
        EY.functor.map (π.map g ≫ h)) :
          πQ.obj ⟨EX.functor.obj F', hF'⟩ ⟶ ⟨EY.functor.obj M.obj, M.property⟩) =
      πQ.map gQ ≫ (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F, hF⟩ ≫ eπ.inv.app F ≫
        EY.functor.map h) :
          πQ.obj ⟨EX.functor.obj F, hF⟩ ⟶ ⟨EY.functor.obj M.obj, M.property⟩) := by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, Functor.map_comp, reassoc_of% h1, reassoc_of% h2]
  rw [transportedHomEquiv_apply, transportedHomEquiv_apply, e1,
    Adjunction.homEquiv_naturality_left, ObjectProperty.FullSubcategory.comp_hom]
  exact EX.toAdjunction.homEquiv_naturality_left _ _

/-- `transportedHomEquiv` is natural in `M`: postcomposition with `φ` corresponds to
postcomposition with `transportedRightAdjoint` applied to `φ`. -/
theorem transportedHomEquiv_naturality_right
    {M M' : (transportedProperty EY PY').FullSubcategory}
    (φ : M ⟶ M') (F : 𝒳) (hF : PX' (EX.functor.obj F)) (h : π.obj F ⟶ M.obj) :
    transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M' F hF (h ≫ φ.hom) =
      transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M F hF h ≫
        (transportedRightAdjoint EX EY PX' PY' a').map φ := by
  let φQ : (⟨EY.functor.obj M.obj, M.property⟩ : PY'.FullSubcategory) ⟶
      ⟨EY.functor.obj M'.obj, M'.property⟩ := ObjectProperty.homMk (EY.functor.map φ.hom)
  have e1 : (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F, hF⟩ ≫ eπ.inv.app F ≫
        EY.functor.map (h ≫ φ.hom)) :
          πQ.obj ⟨EX.functor.obj F, hF⟩ ⟶ ⟨EY.functor.obj M'.obj, M'.property⟩) =
      (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F, hF⟩ ≫ eπ.inv.app F ≫
        EY.functor.map h) :
          πQ.obj ⟨EX.functor.obj F, hF⟩ ⟶ ⟨EY.functor.obj M.obj, M.property⟩) ≫ φQ := by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, ObjectProperty.homMk_hom, Functor.map_comp, Category.assoc,
      Category.assoc]
  rw [transportedHomEquiv_apply, transportedHomEquiv_apply, e1,
    Adjunction.homEquiv_naturality_right, ObjectProperty.FullSubcategory.comp_hom]
  exact EX.toAdjunction.homEquiv_naturality_right _ _

/-- **The transported adjunction bijection through a factorization.** If the image of
`h : π F ⟶ M`, read in `PY'`, factors as `πQ` of `x : EX F ⟶ Q` followed by `y : πQ Q ⟶ EY M`,
then the corresponding morphism `F ⟶ a M` is the transpose under `EX` of `x` followed by the
`πQ ⊣ a'`-transpose of `y`. -/
theorem transportedHomEquiv_eq_of_fac (M : (transportedProperty EY PY').FullSubcategory) (F : 𝒳)
    (hF : PX' (EX.functor.obj F)) (h : π.obj F ⟶ M.obj) (Q : PX'.FullSubcategory)
    (x : (⟨EX.functor.obj F, hF⟩ : PX'.FullSubcategory) ⟶ Q)
    (y : πQ.obj Q ⟶ ⟨EY.functor.obj M.obj, M.property⟩)
    (hxy : (ObjectProperty.homMk (eQ.hom.app ⟨EX.functor.obj F, hF⟩ ≫ eπ.inv.app F ≫
        EY.functor.map h) : πQ.obj ⟨EX.functor.obj F, hF⟩ ⟶ ⟨EY.functor.obj M.obj, M.property⟩) =
      πQ.map x ≫ y) :
    transportedHomEquiv EX EY π π' eπ PX' PY' πQ eQ a' adj M F hF h =
      EX.toAdjunction.homEquiv F _ (x.hom ≫ (adj.homEquiv Q _ y).hom) := by
  rw [transportedHomEquiv_apply, hxy, Adjunction.homEquiv_naturality_left,
    ObjectProperty.FullSubcategory.comp_hom]

end Transport

/-! ### The duality formula -/

section Formula

variable {𝒳 𝒴 : Type*} [Category 𝒳] [Category 𝒴]
  (TX : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (HX : 𝒳ᵒᵖ ⥤ 𝒳 ⥤ 𝒳)
  (cX : ∀ A B Z : 𝒳, (A ⟶ (HX.obj (op B)).obj Z) ≃ ((TX.obj A).obj B ⟶ Z))
  (TY : 𝒴 ⥤ 𝒴 ⥤ 𝒴) (HY : 𝒴ᵒᵖ ⥤ 𝒴 ⥤ 𝒴)
  (cY : ∀ A B Z : 𝒴, (A ⟶ (HY.obj (op B)).obj Z) ≃ ((TY.obj A).obj B ⟶ Z))
  (π : 𝒳 ⥤ 𝒴) (p : 𝒴 ⥤ 𝒳) (PX : ObjectProperty 𝒳) (PY : ObjectProperty 𝒴)
  (a : PY.FullSubcategory ⥤ 𝒳)
  (α : ∀ (M : PY.FullSubcategory) (F : 𝒳), PX F → ((π.obj F ⟶ M.obj) ≃ (F ⟶ a.obj M)))
  (ρ : ∀ (F : 𝒳) (D : 𝒴), (TY.obj (π.obj F)).obj D ⟶ π.obj ((TX.obj F).obj (p.obj D)))
  (K : PY.FullSubcategory)
  (β : ∀ M : 𝒴, M ⟶ (HY.obj (op ((HY.obj (op M)).obj K.obj))).obj K.obj)
  (𝓜 : ObjectProperty 𝒴) (h𝓜 : 𝓜 ≤ PY)
  (hρ : ∀ F D, PX F → PY D → IsIso (ρ F D)) (hβ : ∀ M, 𝓜 M → IsIso (β M))
  (hD : ∀ M, 𝓜 M → PY ((HY.obj (op M)).obj K.obj))
  (hT : ∀ M F, 𝓜 M → PX F → PX ((TX.obj F).obj (p.obj ((HY.obj (op M)).obj K.obj))))

/-- The chain of bijections `Hom(F, H(pD(M), aK)) ≃ Hom(F, aM)` of [Stacks, Tag 0AU2]. -/
def dualityHomEquiv (M : 𝒴) (hM : 𝓜 M) (F : 𝒳) (hF : PX F) :
    (F ⟶ (HX.obj (op (p.obj ((HY.obj (op M)).obj K.obj)))).obj (a.obj K)) ≃
      (F ⟶ a.obj ⟨M, h𝓜 _ hM⟩) :=
  haveI := hρ F _ hF (hD M hM)
  haveI := hβ M hM
  (cX F _ (a.obj K)).trans ((α K _ (hT M F hM hF)).symm.trans
    ((precompEquiv (ρ F ((HY.obj (op M)).obj K.obj))).trans
      ((cY (π.obj F) ((HY.obj (op M)).obj K.obj) K.obj).symm.trans
        ((postcompEquiv (inv (β M))).trans (α ⟨M, h𝓜 _ hM⟩ F hF)))))

/-- `dualityHomEquiv` sends `h` to the image under `α_M` of the `cY`-transpose of
`ρ ≫ α_K⁻¹(cX h)` followed by `β_M⁻¹`. -/
theorem dualityHomEquiv_apply (M : 𝒴) (hM : 𝓜 M) (F : 𝒳) (hF : PX F)
    (h : F ⟶ (HX.obj (op (p.obj ((HY.obj (op M)).obj K.obj)))).obj (a.obj K)) :
    haveI := hβ M hM
    dualityHomEquiv TX HX cX TY HY cY π p PX PY a α ρ K β 𝓜 h𝓜 hρ hβ hD hT M hM F hF h =
      α ⟨M, h𝓜 _ hM⟩ F hF ((cY (π.obj F) ((HY.obj (op M)).obj K.obj) K.obj).symm
        (ρ F ((HY.obj (op M)).obj K.obj) ≫ (α K _ (hT M F hM hF)).symm (cX F _ (a.obj K) h)) ≫
          inv (β M)) :=
  rfl

variable {TX HX cX TY HY cY π p PX PY a α ρ K β 𝓜 h𝓜 hρ hβ hD hT}

/-- **The inverse of the chain of bijections, read through `α_K` and `cX`**: for
`h : F ⟶ a(M)`, the morphism `F ⟶ H(pD(M), aK)` it comes from corresponds under `cX` and `α_K`
to `ρ⁻¹` followed by the `cY`-transpose of `α_M⁻¹(h) ≫ β_M`. -/
theorem dualityHomEquiv_symm_apply (M : 𝒴) (hM : 𝓜 M) (F : 𝒳) (hF : PX F)
    (h : F ⟶ a.obj ⟨M, h𝓜 _ hM⟩) :
    haveI := hρ F _ hF (hD M hM)
    (α K _ (hT M F hM hF)).symm (cX F _ (a.obj K)
        ((dualityHomEquiv TX HX cX TY HY cY π p PX PY a α ρ K β 𝓜 h𝓜 hρ hβ hD hT M hM F
          hF).symm h)) =
      inv (ρ F ((HY.obj (op M)).obj K.obj)) ≫
        cY (π.obj F) ((HY.obj (op M)).obj K.obj) K.obj ((α ⟨M, h𝓜 _ hM⟩ F hF).symm h ≫ β M) := by
  have := hρ F _ hF (hD M hM)
  have := hβ M hM
  simp only [dualityHomEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, precompEquiv_symm_apply, postcompEquiv_symm_apply, IsIso.inv_inv,
    Equiv.symm_symm]

/-- An equation `e₁ (f x) = g (e₂ x)` gives `e₁⁻¹ (g y) = f (e₂⁻¹ y)`. -/
private theorem symm_apply_of_apply {A B A' B' : Sort*} (e₁ : A ≃ B) (e₂ : A' ≃ B')
    {f : A' → A} {g : B' → B} (h : ∀ x, e₁ (f x) = g (e₂ x)) (y : B') :
    e₁.symm (g y) = f (e₂.symm y) := by
  apply e₁.injective
  rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]

/-- **The duality formula of [Stacks, Tag 0AU2], abstractly**: under the hypotheses of the
section, `a(M) ≅ H(p D(M), a(K))` naturally in `M ∈ 𝓜`, where `D = H(-, K)`. -/
def dualityFormulaIso
    (hcX₁ : ∀ {A A' : 𝒳} (B Z : 𝒳) (k : A' ⟶ A) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A' B Z (k ≫ θ) = (TX.map k).app B ≫ cX A B Z θ)
    (hcX₂ : ∀ (A : 𝒳) {B B' : 𝒳} (Z : 𝒳) (l : B' ⟶ B) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A B' Z (θ ≫ (HX.map l.op).app Z) = (TX.obj A).map l ≫ cX A B Z θ)
    (hcY₁ : ∀ {A A' : 𝒴} (B Z : 𝒴) (k : A' ⟶ A) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A' B Z (k ≫ θ) = (TY.map k).app B ≫ cY A B Z θ)
    (hcY₂ : ∀ (A : 𝒴) {B B' : 𝒴} (Z : 𝒴) (l : B' ⟶ B) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A B' Z (θ ≫ (HY.map l.op).app Z) = (TY.obj A).map l ≫ cY A B Z θ)
    (hα₁ : ∀ (M : PY.FullSubcategory) {F F' : 𝒳} (hF : PX F) (hF' : PX F') (g : F' ⟶ F)
      (h : π.obj F ⟶ M.obj), α M F' hF' (π.map g ≫ h) = g ≫ α M F hF h)
    (hα₂ : ∀ {M M' : PY.FullSubcategory} (φ : M ⟶ M') (F : 𝒳) (hF : PX F)
      (h : π.obj F ⟶ M.obj), α M' F hF (h ≫ φ.hom) = α M F hF h ≫ a.map φ)
    (hρ₁ : ∀ {F F' : 𝒳} (g : F' ⟶ F) (D : 𝒴),
      (TY.map (π.map g)).app D ≫ ρ F D = ρ F' D ≫ π.map ((TX.map g).app (p.obj D)))
    (hρ₂ : ∀ (F : 𝒳) {D D' : 𝒴} (d : D ⟶ D'),
      (TY.obj (π.obj F)).map d ≫ ρ F D' = ρ F D ≫ π.map ((TX.obj F).map (p.map d)))
    (hβnat : ∀ {M M' : 𝒴} (φ : M ⟶ M'),
      φ ≫ β M' = β M ≫ (HY.map ((HY.map φ.op).app K.obj).op).app K.obj)
    (ha : ∀ M, PX (a.obj M))
    (hN : ∀ M, 𝓜 M → PX ((HX.obj (op (p.obj ((HY.obj (op M)).obj K.obj)))).obj (a.obj K))) :
    ObjectProperty.ιOfLE h𝓜 ⋙ a ≅
      𝓜.ι ⋙ (HY.flip.obj K.obj).rightOp ⋙ p.op ⋙ HX.flip.obj (a.obj K) :=
  (natIsoOfHomEquiv PX (𝓜.ι ⋙ (HY.flip.obj K.obj).rightOp ⋙ p.op ⋙ HX.flip.obj (a.obj K))
    (ObjectProperty.ιOfLE h𝓜 ⋙ a) (fun M => hN M.obj M.property) (fun M => ha _)
    (fun M F hF => dualityHomEquiv TX HX cX TY HY cY π p PX PY a α ρ K β 𝓜 h𝓜 hρ hβ hD hT
      M.obj M.property F hF)
    (by
      intro M F F' hF hF' g h
      have := hρ F _ hF (hD M.obj M.property)
      have := hρ F' _ hF' (hD M.obj M.property)
      have := hβ M.obj M.property
      dsimp only [Functor.comp_obj]
      rw [dualityHomEquiv_apply, dualityHomEquiv_apply, hcX₁,
        symm_apply_of_apply (α K _ (hT M.obj F' M.property hF')) (α K _ (hT M.obj F M.property hF))
          (fun x => hα₁ K (hT M.obj F M.property hF) (hT M.obj F' M.property hF')
            ((TX.map g).app _) x),
        reassoc_of% (hρ₁ g _).symm,
        symm_apply_of_apply (cY (π.obj F') _ K.obj) (cY (π.obj F) _ K.obj)
          (fun x => hcY₁ _ K.obj (π.map g) x), Category.assoc]
      exact hα₁ _ hF hF' g _)
    (by
      intro M M' φ F hF h
      have := hρ F _ hF (hD M.obj M.property)
      have := hρ F _ hF (hD M'.obj M'.property)
      have := hβ M.obj M.property
      have := hβ M'.obj M'.property
      have hβ' : (HY.map ((HY.map φ.hom.op).app K.obj).op).app K.obj ≫ inv (β M'.obj) =
          inv (β M.obj) ≫ φ.hom := by
        rw [IsIso.eq_inv_comp, ← Category.assoc, ← hβnat, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [dualityHomEquiv_apply, dualityHomEquiv_apply]
      dsimp only [Functor.flip_obj_map, Functor.op_map, Functor.rightOp_map, Quiver.Hom.unop_op,
        ObjectProperty.ι_map]
      rw [hcX₂,
        symm_apply_of_apply (α K _ (hT M'.obj F M'.property hF)) (α K _ (hT M.obj F M.property hF))
          (fun x => hα₁ K (hT M.obj F M.property hF) (hT M'.obj F M'.property hF)
            ((TX.obj F).map (p.map ((HY.map φ.hom.op).app K.obj))) x),
        reassoc_of% (hρ₂ F ((HY.map φ.hom.op).app K.obj)).symm,
        symm_apply_of_apply (cY (π.obj F) _ K.obj) (cY (π.obj F) _ K.obj)
          (fun x => (hcY₂ (π.obj F) K.obj ((HY.map φ.hom.op).app K.obj) x)),
        Category.assoc, hβ', ← Category.assoc]
      exact hα₂ ((ObjectProperty.ιOfLE h𝓜).map φ) F hF _)).symm

/-- The components of `dualityFormulaIso` are the images of identities under the inverse of the
chain of bijections. -/
theorem dualityFormulaIso_hom_app
    (hcX₁ : ∀ {A A' : 𝒳} (B Z : 𝒳) (k : A' ⟶ A) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A' B Z (k ≫ θ) = (TX.map k).app B ≫ cX A B Z θ)
    (hcX₂ : ∀ (A : 𝒳) {B B' : 𝒳} (Z : 𝒳) (l : B' ⟶ B) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A B' Z (θ ≫ (HX.map l.op).app Z) = (TX.obj A).map l ≫ cX A B Z θ)
    (hcY₁ : ∀ {A A' : 𝒴} (B Z : 𝒴) (k : A' ⟶ A) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A' B Z (k ≫ θ) = (TY.map k).app B ≫ cY A B Z θ)
    (hcY₂ : ∀ (A : 𝒴) {B B' : 𝒴} (Z : 𝒴) (l : B' ⟶ B) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A B' Z (θ ≫ (HY.map l.op).app Z) = (TY.obj A).map l ≫ cY A B Z θ)
    (hα₁ : ∀ (M : PY.FullSubcategory) {F F' : 𝒳} (hF : PX F) (hF' : PX F') (g : F' ⟶ F)
      (h : π.obj F ⟶ M.obj), α M F' hF' (π.map g ≫ h) = g ≫ α M F hF h)
    (hα₂ : ∀ {M M' : PY.FullSubcategory} (φ : M ⟶ M') (F : 𝒳) (hF : PX F)
      (h : π.obj F ⟶ M.obj), α M' F hF (h ≫ φ.hom) = α M F hF h ≫ a.map φ)
    (hρ₁ : ∀ {F F' : 𝒳} (g : F' ⟶ F) (D : 𝒴),
      (TY.map (π.map g)).app D ≫ ρ F D = ρ F' D ≫ π.map ((TX.map g).app (p.obj D)))
    (hρ₂ : ∀ (F : 𝒳) {D D' : 𝒴} (d : D ⟶ D'),
      (TY.obj (π.obj F)).map d ≫ ρ F D' = ρ F D ≫ π.map ((TX.obj F).map (p.map d)))
    (hβnat : ∀ {M M' : 𝒴} (φ : M ⟶ M'),
      φ ≫ β M' = β M ≫ (HY.map ((HY.map φ.op).app K.obj).op).app K.obj)
    (ha : ∀ M, PX (a.obj M))
    (hN : ∀ M, 𝓜 M → PX ((HX.obj (op (p.obj ((HY.obj (op M)).obj K.obj)))).obj (a.obj K)))
    (M : 𝓜.FullSubcategory) :
    (dualityFormulaIso (TX := TX) (HX := HX) (cX := cX) (TY := TY) (HY := HY) (cY := cY) (π := π)
        (p := p) (PX := PX) (PY := PY) (a := a) (α := α) (ρ := ρ) (K := K) (β := β) (𝓜 := 𝓜)
        (h𝓜 := h𝓜) (hρ := hρ) (hβ := hβ) (hD := hD) (hT := hT) hcX₁ hcX₂ hcY₁ hcY₂ hα₁ hα₂ hρ₁
        hρ₂ hβnat ha hN).hom.app M =
      (dualityHomEquiv TX HX cX TY HY cY π p PX PY a α ρ K β 𝓜 h𝓜 hρ hβ hD hT M.obj M.property
        _ (ha _)).symm (𝟙 _) :=
  rfl

/-- **The transpose of a component of `dualityFormulaIso`**: under `cX` and the bijection `α` at
`K`, the component at `M` is the inverse of `ρ` followed by the `cY`-transpose of the counit
`α⁻¹(𝟙)` followed by `β`. -/
theorem cX_dualityFormulaIso_hom_app
    (hcX₁ : ∀ {A A' : 𝒳} (B Z : 𝒳) (k : A' ⟶ A) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A' B Z (k ≫ θ) = (TX.map k).app B ≫ cX A B Z θ)
    (hcX₂ : ∀ (A : 𝒳) {B B' : 𝒳} (Z : 𝒳) (l : B' ⟶ B) (θ : A ⟶ (HX.obj (op B)).obj Z),
      cX A B' Z (θ ≫ (HX.map l.op).app Z) = (TX.obj A).map l ≫ cX A B Z θ)
    (hcY₁ : ∀ {A A' : 𝒴} (B Z : 𝒴) (k : A' ⟶ A) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A' B Z (k ≫ θ) = (TY.map k).app B ≫ cY A B Z θ)
    (hcY₂ : ∀ (A : 𝒴) {B B' : 𝒴} (Z : 𝒴) (l : B' ⟶ B) (θ : A ⟶ (HY.obj (op B)).obj Z),
      cY A B' Z (θ ≫ (HY.map l.op).app Z) = (TY.obj A).map l ≫ cY A B Z θ)
    (hα₁ : ∀ (M : PY.FullSubcategory) {F F' : 𝒳} (hF : PX F) (hF' : PX F') (g : F' ⟶ F)
      (h : π.obj F ⟶ M.obj), α M F' hF' (π.map g ≫ h) = g ≫ α M F hF h)
    (hα₂ : ∀ {M M' : PY.FullSubcategory} (φ : M ⟶ M') (F : 𝒳) (hF : PX F)
      (h : π.obj F ⟶ M.obj), α M' F hF (h ≫ φ.hom) = α M F hF h ≫ a.map φ)
    (hρ₁ : ∀ {F F' : 𝒳} (g : F' ⟶ F) (D : 𝒴),
      (TY.map (π.map g)).app D ≫ ρ F D = ρ F' D ≫ π.map ((TX.map g).app (p.obj D)))
    (hρ₂ : ∀ (F : 𝒳) {D D' : 𝒴} (d : D ⟶ D'),
      (TY.obj (π.obj F)).map d ≫ ρ F D' = ρ F D ≫ π.map ((TX.obj F).map (p.map d)))
    (hβnat : ∀ {M M' : 𝒴} (φ : M ⟶ M'),
      φ ≫ β M' = β M ≫ (HY.map ((HY.map φ.op).app K.obj).op).app K.obj)
    (ha : ∀ M, PX (a.obj M))
    (hN : ∀ M, 𝓜 M → PX ((HX.obj (op (p.obj ((HY.obj (op M)).obj K.obj)))).obj (a.obj K)))
    (M : 𝓜.FullSubcategory) :
    haveI := hρ (a.obj ⟨M.obj, h𝓜 _ M.property⟩) _ (ha _) (hD M.obj M.property)
    cX (a.obj ⟨M.obj, h𝓜 _ M.property⟩) (p.obj ((HY.obj (op M.obj)).obj K.obj)) (a.obj K)
      ((dualityFormulaIso (TX := TX) (HX := HX) (cX := cX) (TY := TY) (HY := HY) (cY := cY) (π := π)
        (p := p) (PX := PX) (PY := PY) (a := a) (α := α) (ρ := ρ) (K := K) (β := β) (𝓜 := 𝓜)
        (h𝓜 := h𝓜) (hρ := hρ) (hβ := hβ) (hD := hD) (hT := hT) hcX₁ hcX₂ hcY₁ hcY₂ hα₁ hα₂ hρ₁
        hρ₂ hβnat ha hN).hom.app M) =
      α K _ (hT M.obj _ M.property (ha _))
        (inv (ρ (a.obj ⟨M.obj, h𝓜 _ M.property⟩) ((HY.obj (op M.obj)).obj K.obj)) ≫
          cY (π.obj (a.obj ⟨M.obj, h𝓜 _ M.property⟩)) ((HY.obj (op M.obj)).obj K.obj) K.obj
            ((α ⟨M.obj, h𝓜 _ M.property⟩ _ (ha _)).symm (𝟙 _) ≫ β M.obj)) := by
  rw [dualityFormulaIso_hom_app]
  exact (Equiv.symm_apply_eq _).1 (dualityHomEquiv_symm_apply M.obj M.property _ (ha _) (𝟙 _))

end Formula

end CategoryTheory.DualityFormula

end
