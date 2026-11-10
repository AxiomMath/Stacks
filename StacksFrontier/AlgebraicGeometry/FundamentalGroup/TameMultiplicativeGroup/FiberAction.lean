module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ClassificationCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.TowerAction

/-!
# The action of `Ẑ^{(q)} ⋊ Ẑ` on the fibres of tame covers of `𝐆_m`

By the classification, the ring map `ψ_y : Γ(Y) → Ω` of a point `y` of the fibre of a tame cover
`Y` at the geometric generic point takes values in the Kummer tower, so `γ ∈ Γ` acts on it by
`ψ_y ↦ τ_γ ∘ ψ_y`. This is a natural action on the fibre functor, hence a homomorphism
`Γ → π₁ᵗ(𝐆_{m,k}, η̄)`.

Every point of a fibre is the image of the base point of a layer `K_m` of the tower under a map of
covers `K_m → Y`, so an automorphism of the fibre functor is determined by its values at these
base points.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.fiberAct`: the action on a fibre.
* `AlgebraicGeometry.TameMultiplicativeGroup.tameAut`: the induced automorphism of the fibre
  functor.
* `AlgebraicGeometry.TameMultiplicativeGroup.basePoint`: the base point of the layer `K_m`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.exists_map_basePoint`: every point of a fibre is the
  image of a base point under a map of covers.
* `AlgebraicGeometry.TameMultiplicativeGroup.eq_of_forall_basePoint`: an element of `π₁ᵗ` is
  determined by its values at the base points.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {k : Type u} [Field k]

/-- The ring map `Γ(Y) → Ω` of a point of the fibre. -/
abbrev fiberRingHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) :
    Γ(Y.obj.left, ⊤) →+* Omega k :=
  (pointRingHom y.1).hom

/-- A point of a fibre is determined by its ring map `Γ(Y) → Ω`. -/
theorem fiber_ext {Y : TameCover k} {y y' : (tameFiberFunctor k).obj Y}
    (h : fiberRingHom y = fiberRingHom y') : y = y' :=
  Subtype.ext (pointRingHom_injective (CommRingCat.hom_ext h))

/-- The point of the fibre with a given ring map over the base map. -/
def fiberPoint {Y : TameCover k} (χ : Γ(Y.obj.left, ⊤) →+* Omega k)
    (hχ : χ.comp (strHom Y.obj).hom = baseHom k) : (tameFiberFunctor k).obj Y :=
  (⟨pointOfRingHom (CommRingCat.ofHom χ), (comp_hom_eq_iff _).mpr (by
    rw [pointRingHom_pointOfRingHom]
    ext z
    exact RingHom.congr_fun hχ z)⟩ : finiteEtaleFiber (genericGeometricPoint k) Y.obj)

/-- The ring map of `fiberPoint χ hχ` is `χ`. -/
theorem fiberRingHom_fiberPoint {Y : TameCover k} (χ : Γ(Y.obj.left, ⊤) →+* Omega k)
    (hχ : χ.comp (strHom Y.obj).hom = baseHom k) : fiberRingHom (fiberPoint χ hχ) = χ := by
  change (pointRingHom (pointOfRingHom (CommRingCat.ofHom χ))).hom = χ
  rw [pointRingHom_pointOfRingHom]
  rfl

/-- The ring map of a point of the fibre lies over the base map `baseHom k`. -/
theorem fiberRingHom_comp_strHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) :
    (fiberRingHom y).comp (strHom Y.obj).hom = baseHom k :=
  pointRingHom_comp_strHom y.1 y.2

/-- The ring map of the image of `y` under a map of covers `g` is that of `y` composed with `g` on
global sections. -/
theorem fiberRingHom_map {Y Y' : TameCover k} (g : Y ⟶ Y') (y : (tameFiberFunctor k).obj Y) :
    fiberRingHom ((tameFiberFunctor k).map g y) = (fiberRingHom y).comp g.hom.left.appTop.hom := by
  change (pointRingHom (y.1 ≫ g.hom.left)).hom = _
  rw [pointRingHom_comp]
  rfl

variable [Fintype k]

/-- The ring map of a point of the fibre takes values in the Kummer tower. -/
theorem isTowerValued_fiberRingHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) :
    IsTowerValued (fiberRingHom y) :=
  exists_forall_mem_range_towerPoint_of_fiber Y y

/-- **The action of `γ ∈ Γ` on a fibre**, `ψ_y ↦ τ_γ ∘ ψ_y`. -/
def fiberAct (γ : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) : (tameFiberFunctor k).obj Y :=
  fiberPoint (towerAct γ (fiberRingHom y) (isTowerValued_fiberRingHom y))
    (towerAct_comp_eq_baseHom _ _ _ _ (fiberRingHom_comp_strHom y))

/-- The ring map of `fiberAct γ Y y` is `τ_γ ∘ ψ_y`. -/
theorem fiberRingHom_fiberAct (γ : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) :
    fiberRingHom (fiberAct γ Y y) = towerAct γ (fiberRingHom y) (isTowerValued_fiberRingHom y) :=
  fiberRingHom_fiberPoint _ _

/-- The action on a fibre is compatible with multiplication in `Γ`. -/
theorem fiberAct_mul (γ γ' : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) : fiberAct (γ * γ') Y y = fiberAct γ Y (fiberAct γ' Y y) :=
  fiber_ext (by
    rw [fiberRingHom_fiberAct, fiberRingHom_fiberAct, towerAct_mul]
    exact towerAct_eq_of_eq _ _ _ (fiberRingHom_fiberAct γ' Y y).symm)

/-- The identity of `Γ` acts trivially on a fibre. -/
theorem fiberAct_one (Y : TameCover k) (y : (tameFiberFunctor k).obj Y) : fiberAct 1 Y y = y :=
  fiber_ext (by rw [fiberRingHom_fiberAct, towerAct_one])

/-- The action on fibres commutes with the maps induced by maps of covers. -/
theorem fiberAct_map (γ : Gamma (inverseCharacter (Fintype.card k))) {Y Y' : TameCover k}
    (g : Y ⟶ Y') (y : (tameFiberFunctor k).obj Y) :
    (tameFiberFunctor k).map g (fiberAct γ Y y) = fiberAct γ Y' ((tameFiberFunctor k).map g y) := by
  have h₂ : IsTowerValued ((fiberRingHom y).comp g.hom.left.appTop.hom) :=
    ⟨(isTowerValued_fiberRingHom y).choose,
      fun c ↦ (isTowerValued_fiberRingHom y).choose_spec _⟩
  refine fiber_ext ?_
  calc fiberRingHom ((tameFiberFunctor k).map g (fiberAct γ Y y))
      = (fiberRingHom (fiberAct γ Y y)).comp g.hom.left.appTop.hom := fiberRingHom_map g _
    _ = (towerAct γ (fiberRingHom y) (isTowerValued_fiberRingHom y)).comp
          g.hom.left.appTop.hom := by rw [fiberRingHom_fiberAct]
    _ = towerAct γ ((fiberRingHom y).comp g.hom.left.appTop.hom) h₂ :=
          (towerAct_comp γ _ _ _ h₂).symm
    _ = towerAct γ (fiberRingHom ((tameFiberFunctor k).map g y))
          (isTowerValued_fiberRingHom _) :=
          towerAct_eq_of_eq _ _ _ (fiberRingHom_map g y).symm
    _ = fiberRingHom (fiberAct γ Y' ((tameFiberFunctor k).map g y)) :=
          (fiberRingHom_fiberAct _ _ _).symm

/-- The action of `γ` on a fibre, as a permutation. -/
def fiberEquiv (γ : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k) :
    (tameFiberFunctor k).obj Y ≃ (tameFiberFunctor k).obj Y where
  toFun := fiberAct γ Y
  invFun := fiberAct γ⁻¹ Y
  left_inv y := by rw [← fiberAct_mul, inv_mul_cancel, fiberAct_one]
  right_inv y := by rw [← fiberAct_mul, mul_inv_cancel, fiberAct_one]

/-- **The automorphism of the fibre functor of `γ ∈ Γ`.** -/
def tameAut (γ : Gamma (inverseCharacter (Fintype.card k))) : tameFundamentalGroup k :=
  Aut.of <| NatIso.ofComponents (fun Y ↦ (fiberEquiv γ Y).toIso) (fun g ↦ by
    ext y
    exact (fiberAct_map γ g y).symm)

/-- The value of an element of `π₁ᵗ` at a point of a fibre. -/
abbrev autApply (σ : tameFundamentalGroup k) (Y : TameCover k) (y : (tameFiberFunctor k).obj Y) :
    (tameFiberFunctor k).obj Y :=
  (σ : Aut (tameFiberFunctor k)).asIso.hom.app Y y

/-- The value of `tameAut γ` at a point of a fibre is `fiberAct γ`. -/
theorem autApply_tameAut (γ : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) : autApply (tameAut γ) Y y = fiberAct γ Y y := rfl

omit [Fintype k] in
/-- Two elements of `π₁ᵗ` agreeing at every point of every fibre are equal. -/
theorem tameFundamentalGroup_ext {σ τ : tameFundamentalGroup k}
    (h : ∀ Y y, autApply σ Y y = autApply τ Y y) : σ = τ :=
  Aut.ext (Iso.ext (NatTrans.ext (funext fun Y ↦ by
    ext y
    exact h Y y)))

omit [Fintype k] in
/-- The value of a product `σ * τ` at a point is that of `σ` at the value of `τ`. -/
theorem autApply_mul (σ τ : tameFundamentalGroup k) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) : autApply (σ * τ) Y y = autApply σ Y (autApply τ Y y) :=
  rfl

omit [Fintype k] in
/-- The value of an element of `π₁ᵗ` commutes with the maps induced by maps of covers. -/
theorem autApply_map (σ : tameFundamentalGroup k) {Y Y' : TameCover k} (g : Y ⟶ Y')
    (y : (tameFiberFunctor k).obj Y) :
    autApply σ Y' ((tameFiberFunctor k).map g y) = (tameFiberFunctor k).map g (autApply σ Y y) :=
  NatTrans.naturality_apply (σ : Aut (tameFiberFunctor k)).asIso.hom g y

/-- **`γ ↦ (y ↦ τ_γ ∘ y)` is a homomorphism `Γ → π₁ᵗ(𝐆_{m,k}, η̄)`.** -/
def tameAutHom : Gamma (inverseCharacter (Fintype.card k)) →* tameFundamentalGroup k where
  toFun := tameAut
  map_one' := tameFundamentalGroup_ext fiberAct_one
  map_mul' γ γ' := tameFundamentalGroup_ext (fiberAct_mul γ γ')

/-- The value of `tameAutHom γ` at a point of a fibre is `fiberAct γ`. -/
theorem autApply_tameAutHom (γ : Gamma (inverseCharacter (Fintype.card k))) (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) : autApply (tameAutHom γ) Y y = fiberAct γ Y y := rfl

/-! ### Base points of the layers -/

variable (k) in
/-- **The base point of the layer `K_m`**, the point `Spec k₀^{(m)} : Spec Ω ⟶ K_m`. -/
def basePoint (m : ℕ) : (tameFiberFunctor k).obj (towerCover k m) :=
  (⟨Spec.map (CommRingCat.ofHom (towerPoint k m)), by
    change Spec.map (CommRingCat.ofHom (towerPoint k m)) ≫
      Spec.map (CommRingCat.ofHom (kummerMap k (towerField k m) (towerN k m))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, towerPoint_comp_kummerMap, specMap_baseHom]⟩ :
    finiteEtaleFiber (genericGeometricPoint k) (towerCover k m).obj)

/-- The map `Γ(K_m) → Ω` of the base point of `K_m` is `Γ(Spec R) ≅ R` followed by
`towerPoint k m`. -/
theorem pointRingHom_basePoint (m : ℕ) :
    pointRingHom (basePoint k m).1 =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (towerPoint k m) := by
  apply Spec.map_injective
  rw [specMap_pointRingHom]
  change Spec.map (CommRingCat.ofHom (towerPoint k m)) ≫
    (Spec (CommRingCat.of (Ring (towerField k m)))).isoSpec.hom = _
  rw [Scheme.isoSpec_Spec_hom]
  exact (Spec.map_comp _ _).symm

/-- The ring map of the base point of `K_m` is `towerPoint k m ∘ (Γ(Spec R) ≅ R)`. -/
theorem fiberRingHom_basePoint (m : ℕ) :
    fiberRingHom (basePoint k m) = (towerPoint k m).comp (Scheme.ΓSpecIso _).hom.hom := by
  rw [fiberRingHom, pointRingHom_basePoint]
  rfl

/-- The structure map of the layer `K_m` on global sections is the Kummer map followed by
`R ≅ Γ(Spec R)`. -/
theorem strHom_towerCover (m : ℕ) :
    strHom (towerCover k m).obj =
      CommRingCat.ofHom (kummerMap k (towerField k m) (towerN k m)) ≫ (Scheme.ΓSpecIso _).inv := by
  rw [Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The ring map `Γ(Y) → 𝔽_{m!}[X]_X` of a point with values in the `m`-th layer. -/
def factorRingHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    Γ(Y.obj.left, ⊤) →+* Ring (towerField k m) :=
  (rangeEquiv k m).symm.toRingHom.comp ((fiberRingHom y).codRestrict _ hm)

/-- Composing `factorRingHom y m hm` with `towerPoint k m` recovers the ring map of `y`. -/
theorem towerPoint_factorRingHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    (towerPoint k m).comp (factorRingHom y m hm) = fiberRingHom y := by
  ext
  exact towerPoint_rangeEquiv_symm k m _

/-- `factorRingHom y m hm` lies over the Kummer map of the `m`-th layer. -/
theorem factorRingHom_comp_strHom {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    (factorRingHom y m hm).comp (strHom Y.obj).hom = kummerMap k (towerField k m) (towerN k m) := by
  ext z
  apply towerPoint_injective k m
  have h1 := RingHom.congr_fun (towerPoint_factorRingHom y m hm) ((strHom Y.obj).hom z)
  have h2 := RingHom.congr_fun (fiberRingHom_comp_strHom y) z
  simp only [RingHom.comp_apply] at h1 h2 ⊢
  rw [h1, h2, towerPoint_kummerMap]

/-- The map of global sections `Γ(Y) → Γ(K_m)` of a point with values in the `m`-th layer. -/
def factorTheta {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    Γ(Y.obj.left, ⊤) ⟶ Γ((towerCover k m).obj.left, ⊤) :=
  CommRingCat.ofHom (factorRingHom y m hm) ≫ (Scheme.ΓSpecIso _).inv

/-- `factorTheta y m hm` is `factorRingHom y m hm` followed by `R ≅ Γ(Spec R)`. -/
theorem factorTheta_apply {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) (c : Γ(Y.obj.left, ⊤)) :
    (factorTheta y m hm).hom c =
      (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom (factorRingHom y m hm c) :=
  rfl

/-- `factorTheta y m hm` is compatible with the structure maps of `Y` and of `K_m`. -/
theorem strHom_comp_factorTheta {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    strHom Y.obj ≫ factorTheta y m hm = strHom (towerCover k m).obj := by
  have h1 : strHom Y.obj ≫ CommRingCat.ofHom (factorRingHom y m hm) =
      CommRingCat.ofHom (kummerMap k (towerField k m) (towerN k m)) := by
    ext z
    exact RingHom.congr_fun (factorRingHom_comp_strHom y m hm) z
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Scheme.ΓSpecIso _).inv) h1).trans (strHom_towerCover m).symm)

/-- **The map of covers `K_m → Y`** sending the base point to a point with values in the `m`-th
layer. -/
def factorMap {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) : towerCover k m ⟶ Y :=
  ObjectProperty.homMk (homOfRingHom (factorTheta y m hm) (strHom_comp_factorTheta y m hm))

/-- The map of covers `factorMap y m hm` sends the base point of `K_m` to `y`. -/
theorem map_factorMap_basePoint {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) (m : ℕ)
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range) :
    (tameFiberFunctor k).map (factorMap y m hm) (basePoint k m) = y := by
  refine fiber_ext (RingHom.ext fun c ↦ ?_)
  have h1 : fiberRingHom ((tameFiberFunctor k).map (factorMap y m hm) (basePoint k m)) =
      (fiberRingHom (basePoint k m)).comp (factorTheta y m hm).hom := by
    change (pointRingHom ((basePoint k m).1 ≫
      (homOfRingHom (factorTheta y m hm) (strHom_comp_factorTheta y m hm)).left)).hom = _
    rw [pointRingHom_homOfRingHom]
    rfl
  rw [h1, RingHom.comp_apply, fiberRingHom_basePoint]
  refine (congrArg ((towerPoint k m).comp
    (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).hom.hom)
      (factorTheta_apply y m hm c)).trans ?_
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom
        (factorRingHom y m hm c)) = factorRingHom y m hm c :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).inv_hom_id _
  exact (congrArg (towerPoint k m) hinv).trans
    (RingHom.congr_fun (towerPoint_factorRingHom y m hm) c)

/-- **Every point of a fibre comes from a base point of the tower.** -/
theorem exists_map_basePoint {Y : TameCover k} (y : (tameFiberFunctor k).obj Y) :
    ∃ m, ∃ g : towerCover k m ⟶ Y, (tameFiberFunctor k).map g (basePoint k m) = y := by
  obtain ⟨m, hm⟩ := isTowerValued_fiberRingHom y
  exact ⟨m, factorMap y m hm, map_factorMap_basePoint y m hm⟩

/-- **An element of `π₁ᵗ` is determined by its values at the base points of the tower.** -/
theorem eq_of_forall_basePoint {σ τ : tameFundamentalGroup k}
    (h : ∀ m, autApply σ _ (basePoint k m) = autApply τ _ (basePoint k m)) : σ = τ := by
  refine tameFundamentalGroup_ext fun Y y ↦ ?_
  obtain ⟨m, g, rfl⟩ := exists_map_basePoint y
  rw [autApply_map, autApply_map, h m]

/-- Agreement at the base point of `K_{m+1}` implies agreement at that of `K_m`. -/
theorem autApply_basePoint_of_succ {σ τ : tameFundamentalGroup k} (m : ℕ)
    (h : autApply σ _ (basePoint k (m + 1)) = autApply τ _ (basePoint k (m + 1))) :
    autApply σ _ (basePoint k m) = autApply τ _ (basePoint k m) := by
  have hm : ∀ c, fiberRingHom (basePoint k m) c ∈ (towerPoint k (m + 1)).range := fun c ↦
    range_towerPoint_le k m (by rw [fiberRingHom_basePoint]; exact ⟨_, rfl⟩)
  rw [← map_factorMap_basePoint (basePoint k m) (m + 1) hm, autApply_map, autApply_map, h]

end AlgebraicGeometry.TameMultiplicativeGroup

end
