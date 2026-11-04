/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.BaseChange.Graph
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatQuotientPullbackMono
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullbackComp
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectCornerSquare

/-!
# Base change of shtukas

Let `k` be a finite field with `q = p ^ f` elements, `X` a separated scheme over `k` and
`g : S' ⟶ S` a morphism of schemes over `k`. Pulling back along `id_X × g : X ×_k S' ⟶ X ×_k S`
carries a shtuka of rank `r` over `S` to a shtuka of rank `r` over `S'`:

* `E ↦ (id × g)^* E` and `E' ↦ (id × g)^* E'` stay locally free of rank `r`;
* `j ↦ (id × g)^* j` stays injective: `coker j = Γ_{∞,*} L` is flat over `S` (Stacks Tag 0FLM),
  so `Tor_1` against it vanishes, and its cokernel is `(id × g)^* Γ_{∞,*} L ≅ Γ_{∞ ∘ g,*} g^* L`
  (affine base change, Stacks Tag 02KG);
* `t : τ_S^* E ⟶ E'` is transported along `τ_{S'}^* (id × g)^* ≅ (id × g)^* τ_S^*`, which comes
  from `τ_{S'} ≫ (id × g) = (id × g) ≫ τ_S`, and the same argument applies to it;
* the legs become `∞ ∘ g` and `0 ∘ g`.

## Main definitions

* `Stacks.Drinfeld.Shtuka.frobeniusTwistBaseChangeIso`: `τ_{S'}^* (id × g)^* ≅ (id × g)^* τ_S^*`.
* `Stacks.Drinfeld.Shtuka.baseChange`: the shtuka `(id × g)^* 𝓔` over `S'`.
* `Stacks.Drinfeld.Shtuka.baseChangeMap`, `Stacks.Drinfeld.Shtuka.baseChangeFunctor`: base change
  is functorial in morphisms of shtukas.
* `Stacks.Drinfeld.Shtuka.baseChangeIdIso`, `Stacks.Drinfeld.Shtuka.baseChangeCompIso` and their
  functor versions `Stacks.Drinfeld.Shtuka.baseChangeFunctorId`,
  `Stacks.Drinfeld.Shtuka.baseChangeFunctorComp`: `baseChange (𝟙 S) ≅ 𝟭` and
  `baseChange (g' ≫ g) ≅ baseChange g ⋙ baseChange g'`, built from the unit and composition
  comparisons of pullback of modules along `id_X × 𝟙 = 𝟙` and
  `id_X × (g' ≫ g) = (id_X × g') ≫ (id_X × g)`.

## Main results

* `Stacks.Drinfeld.Shtuka.mono_pullback_productMap_map`: `(id × g)^*` keeps a monomorphism whose
  cokernel is a graph line bundle injective.
* `Stacks.Drinfeld.Shtuka.isGraphLineBundle_cokernel_pullback_productMap`: the cokernel of the
  pulled-back map is the graph line bundle of the leg `x ∘ g`.
* `Stacks.Drinfeld.Shtuka.modulesPullbackSquareIso_hom_app_comp_pullbackId` and
  `Stacks.Drinfeld.Shtuka.modulesPullbackSquareIso_hom_app_comp_pullbackComp`: the comparison
  `AlgebraicGeometry.modulesPullbackSquareIso` of a square `τ' ≫ P = P ≫ τ` is compatible with
  the unit comparison when `P = 𝟙` and with the composition comparison when `P = P₁ ≫ P₂`
  (from `AlgebraicGeometry.modulesPullbackSquareIso_paste`); these are what make the unit and
  composition comparisons morphisms of shtukas.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Drinfeld

namespace Shtuka

/-! ### Coherence of the square comparisons of pullback -/

section Coherence

variable {Y₀ Y₁ Y₂ Y₃ : Scheme.{u}}

/-- The comparison of the transposed square is the inverse comparison. -/
theorem modulesPullbackSquareIso_symm {a : Y₃ ⟶ Y₁} {b : Y₁ ⟶ Y₀} {c : Y₃ ⟶ Y₂} {d : Y₂ ⟶ Y₀}
    (h : a ≫ b = c ≫ d) :
    modulesPullbackSquareIso h.symm = (modulesPullbackSquareIso h).symm :=
  Iso.ext (by
    ext E
    simp [modulesPullbackSquareIso, Scheme.Modules.pullbackCongr])

/-- The comparison of a commuting square whose horizontal edges are equal to the identity is the
unit comparison: for `P = 𝟙` and `P ≫ τ = τ ≫ P`, transporting along the square and then
identifying `P^*` with the identity agrees with identifying `P^*` with the identity first. The
morphism `P` is kept a variable subject to `P = 𝟙` so that the lemma applies to `id_X × 𝟙_S`. -/
theorem modulesPullbackSquareIso_inv_app_comp_pullbackId {P τ : Y₀ ⟶ Y₀} (hP : P = 𝟙 Y₀)
    (w : P ≫ τ = τ ≫ P) (E : Y₀.Modules) :
    (modulesPullbackSquareIso w).inv.app E ≫
        (Scheme.Modules.pullbackCongr hP ≪≫ Scheme.Modules.pullbackId Y₀).hom.app
          ((Scheme.Modules.pullback τ).obj E) =
      (Scheme.Modules.pullback τ).map
        ((Scheme.Modules.pullbackCongr hP ≪≫ Scheme.Modules.pullbackId Y₀).hom.app E) := by
  subst hP
  rw [← cancel_epi ((modulesPullbackSquareIso w).hom.app E), Iso.hom_inv_id_app_assoc,
    modulesPullbackSquareIso_id_hom_app τ w E]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_trans, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The comparison of a horizontally pasted square, inverted: for `P₃ = P₁ ≫ P₂` and three
commuting squares `Pᵢ ≫ τ = τ ≫ Pᵢ`, transporting along the outer square and then splitting
`P₃^*` agrees with splitting `P₃^*` first and transporting along the two inner squares. The
morphism `P₃` is kept a variable subject to `P₃ = P₁ ≫ P₂`. -/
theorem modulesPullbackSquareIso_inv_app_comp_pullbackComp {P₁ : Y₂ ⟶ Y₁} {P₂ : Y₁ ⟶ Y₀}
    {P₃ : Y₂ ⟶ Y₀} (hP : P₃ = P₁ ≫ P₂) {τ₀ : Y₀ ⟶ Y₀} {τ₁ : Y₁ ⟶ Y₁} {τ₂ : Y₂ ⟶ Y₂}
    (w₁ : P₁ ≫ τ₁ = τ₂ ≫ P₁) (w₂ : P₂ ≫ τ₀ = τ₁ ≫ P₂) (w₃ : P₃ ≫ τ₀ = τ₂ ≫ P₃)
    (E : Y₀.Modules) :
    (modulesPullbackSquareIso w₃).inv.app E ≫
        (Scheme.Modules.pullbackCongr hP ≪≫ (Scheme.Modules.pullbackComp P₁ P₂).symm).hom.app
          ((Scheme.Modules.pullback τ₀).obj E) =
      (Scheme.Modules.pullback τ₂).map
          ((Scheme.Modules.pullbackCongr hP ≪≫ (Scheme.Modules.pullbackComp P₁ P₂).symm).hom.app
            E) ≫
        (modulesPullbackSquareIso w₁).inv.app ((Scheme.Modules.pullback P₂).obj E) ≫
          (Scheme.Modules.pullback P₁).map ((modulesPullbackSquareIso w₂).inv.app E) := by
  subst hP
  have H := congrArg (fun e => e.inv.app E)
    (modulesPullbackSquareIso_paste P₁ P₂ τ₂ τ₁ τ₀ P₁ P₂ w₁ w₂ w₃)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] at H
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_trans, Iso.symm_hom,
    Functor.comp_obj] using H

/-- `modulesPullbackSquareIso_inv_app_comp_pullbackId` for the square `τ ≫ P = P ≫ τ`. -/
theorem modulesPullbackSquareIso_hom_app_comp_pullbackId {P τ : Y₀ ⟶ Y₀} (hP : P = 𝟙 Y₀)
    (w : τ ≫ P = P ≫ τ) (E : Y₀.Modules) :
    (modulesPullbackSquareIso w).hom.app E ≫
        (Scheme.Modules.pullbackCongr hP ≪≫ Scheme.Modules.pullbackId Y₀).hom.app
          ((Scheme.Modules.pullback τ).obj E) =
      (Scheme.Modules.pullback τ).map
        ((Scheme.Modules.pullbackCongr hP ≪≫ Scheme.Modules.pullbackId Y₀).hom.app E) := by
  rw [modulesPullbackSquareIso_symm w.symm, Iso.symm_hom]
  exact modulesPullbackSquareIso_inv_app_comp_pullbackId hP w.symm E

/-- `modulesPullbackSquareIso_inv_app_comp_pullbackComp` for the squares `τ ≫ P = P ≫ τ`. -/
theorem modulesPullbackSquareIso_hom_app_comp_pullbackComp {P₁ : Y₂ ⟶ Y₁} {P₂ : Y₁ ⟶ Y₀}
    {P₃ : Y₂ ⟶ Y₀} (hP : P₃ = P₁ ≫ P₂) {τ₀ : Y₀ ⟶ Y₀} {τ₁ : Y₁ ⟶ Y₁} {τ₂ : Y₂ ⟶ Y₂}
    (w₁ : τ₂ ≫ P₁ = P₁ ≫ τ₁) (w₂ : τ₁ ≫ P₂ = P₂ ≫ τ₀) (w₃ : τ₂ ≫ P₃ = P₃ ≫ τ₀)
    (E : Y₀.Modules) :
    (modulesPullbackSquareIso w₃).hom.app E ≫
        (Scheme.Modules.pullbackCongr hP ≪≫ (Scheme.Modules.pullbackComp P₁ P₂).symm).hom.app
          ((Scheme.Modules.pullback τ₀).obj E) =
      (Scheme.Modules.pullback τ₂).map
          ((Scheme.Modules.pullbackCongr hP ≪≫ (Scheme.Modules.pullbackComp P₁ P₂).symm).hom.app
            E) ≫
        (modulesPullbackSquareIso w₁).hom.app ((Scheme.Modules.pullback P₂).obj E) ≫
          (Scheme.Modules.pullback P₁).map ((modulesPullbackSquareIso w₂).hom.app E) := by
  rw [modulesPullbackSquareIso_symm w₃.symm, modulesPullbackSquareIso_symm w₁.symm,
    modulesPullbackSquareIso_symm w₂.symm, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom]
  exact modulesPullbackSquareIso_inv_app_comp_pullbackComp hP w₁.symm w₂.symm w₃.symm E

end Coherence

section Graph

variable {k : Type u} [Field k] [Fintype k] {X S S' : Over (Spec (.of k))}

/-- **Pulling back a modification along `id × g` keeps it injective.** If `j : E ⟶ E'` is a
monomorphism of `𝒪_{X ×_k S}`-modules whose cokernel is the direct image of an invertible
`𝒪_S`-module along the graph of `x : S ⟶ X`, then `(id × g)^* j` is a monomorphism: the cokernel
is flat over `S`, so `Tor_1^{𝒪_S}(coker j, 𝒪_{S'})` vanishes. -/
theorem mono_pullback_productMap_map [IsSeparated X.hom] {E E' : (product X S).Modules}
    (j : E ⟶ E') [Mono j] {x : S ⟶ X} (hj : IsGraphLineBundle (cokernel j) x) (g : S' ⟶ S) :
    Mono ((Scheme.Modules.pullback (productMap g)).map j) := by
  have hT : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j) }
  exact Scheme.Modules.mono_pullback_map_of_shortExact_of_isFlatOver
    (isPullback_productMap g) hT hj.isFlatOver

/-- **The cokernel of a pulled-back modification is a graph line bundle.** If the cokernel of
`j` is the graph line bundle of `x`, the cokernel of `(id × g)^* j` is the graph line bundle of
`x ∘ g`: pullback is right exact, and `(id × g)^* Γ_{x,*} L ≅ Γ_{x ∘ g,*} g^* L`. -/
theorem isGraphLineBundle_cokernel_pullback_productMap [IsSeparated X.hom]
    {E E' : (product X S).Modules} (j : E ⟶ E') {x : S ⟶ X}
    (hj : IsGraphLineBundle (cokernel j) x) (g : S' ⟶ S) :
    IsGraphLineBundle (cokernel ((Scheme.Modules.pullback (productMap g)).map j)) (g ≫ x) :=
  (hj.pullback_productMap g).of_iso (PreservesCokernel.iso _ j)

omit [Fintype k] in
variable (X) in
/-- `id_X × 𝟙_S = 𝟙`. -/
theorem productMap_id : productMap (X := X) (𝟙 S) = 𝟙 (product X S) := by
  apply pullback.hom_ext <;> simp

omit [Fintype k] in
variable (X) in
/-- `id_X × (g' ≫ g) = (id_X × g') ≫ (id_X × g)`. -/
theorem productMap_comp {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S') (g : S' ⟶ S) :
    productMap (X := X) (g' ≫ g) = productMap g' ≫ productMap g := by
  apply pullback.hom_ext <;> simp [Over.comp_left]

end Graph

variable {k : Type u} [Field k] [Fintype k] {p f : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ f} {X S S' : Over (Spec (.of k))} {r : ℕ}

variable (p f hcard X) in
/-- **`τ` commutes with base change, on modules.** The isomorphism
`τ_{S'}^* (id × g)^* ≅ (id × g)^* τ_S^*` of functors from modules on `X ×_k S` to modules on
`X ×_k S'`: the comparison `AlgebraicGeometry.modulesPullbackSquareIso` of the commuting square
`τ_{S'} ≫ (id × g) = (id × g) ≫ τ_S`. -/
def frobeniusTwistBaseChangeIso (g : S' ⟶ S) :
    Scheme.Modules.pullback (productMap g) ⋙
        Scheme.Modules.pullback (frobeniusTwist p f hcard X S') ≅
      Scheme.Modules.pullback (frobeniusTwist p f hcard X S) ⋙
        Scheme.Modules.pullback (productMap g) :=
  modulesPullbackSquareIso (frobeniusTwist_comp_productMap p f hcard g)

variable [IsSeparated X.hom]

/-- **Base change of a shtuka** along `g : S' ⟶ S`: the shtuka `(id_X × g)^* 𝓔` over `S'`, with
`E` and `E'` pulled back along `id_X × g`, `j` pulled back, `t` pulled back and transported along
`τ_{S'}^* (id × g)^* ≅ (id × g)^* τ_S^*`, and legs `∞ ∘ g`, `0 ∘ g`. -/
def baseChange (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) : Shtuka p f hcard X S' r :=
  have := 𝓔.mono_j
  have := 𝓔.mono_t
  have := mono_pullback_productMap_map 𝓔.t 𝓔.isGraphLineBundle_cokernel_t g
  { E := (Scheme.Modules.pullback (productMap g)).obj 𝓔.E
    E' := (Scheme.Modules.pullback (productMap g)).obj 𝓔.E'
    isFiniteLocallyFreeOfRank_E :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.pullback_scheme _ _ r 𝓔.isFiniteLocallyFreeOfRank_E
    isFiniteLocallyFreeOfRank_E' :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.pullback_scheme _ _ r
        𝓔.isFiniteLocallyFreeOfRank_E'
    j := (Scheme.Modules.pullback (productMap g)).map 𝓔.j
    t := (frobeniusTwistBaseChangeIso p f hcard X g).hom.app 𝓔.E ≫
      (Scheme.Modules.pullback (productMap g)).map 𝓔.t
    mono_j := mono_pullback_productMap_map 𝓔.j 𝓔.isGraphLineBundle_cokernel_j g
    mono_t := mono_comp _ _
    pole := g ≫ 𝓔.pole
    zero := g ≫ 𝓔.zero
    isGraphLineBundle_cokernel_j :=
      isGraphLineBundle_cokernel_pullback_productMap 𝓔.j 𝓔.isGraphLineBundle_cokernel_j g
    isGraphLineBundle_cokernel_t :=
      (isGraphLineBundle_cokernel_pullback_productMap 𝓔.t 𝓔.isGraphLineBundle_cokernel_t g).of_iso
        (cokernelEpiComp _ _).symm }

/-- The first bundle of `baseChange g 𝓔` is the pullback of `𝓔.E` along `id_X × g`. -/
@[simp] theorem baseChange_E (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).E = (Scheme.Modules.pullback (productMap g)).obj 𝓔.E := rfl

/-- The second bundle of `baseChange g 𝓔` is the pullback of `𝓔.E'` along `id_X × g`. -/
@[simp] theorem baseChange_E' (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).E' = (Scheme.Modules.pullback (productMap g)).obj 𝓔.E' := rfl

/-- The map `j` of `baseChange g 𝓔` is the pullback of `𝓔.j` along `id_X × g`. -/
@[simp] theorem baseChange_j (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).j = (Scheme.Modules.pullback (productMap g)).map 𝓔.j := rfl

/-- The map `t` of `baseChange g 𝓔` is the pullback of `𝓔.t` along `id_X × g`, precomposed
with the comparison `τ_{S'}^* (id × g)^* ≅ (id × g)^* τ_S^*`. -/
@[simp] theorem baseChange_t (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).t = (frobeniusTwistBaseChangeIso p f hcard X g).hom.app 𝓔.E ≫
      (Scheme.Modules.pullback (productMap g)).map 𝓔.t := rfl

/-- The pole of `baseChange g 𝓔` is `g ≫ 𝓔.pole`. -/
@[simp] theorem baseChange_pole (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).pole = g ≫ 𝓔.pole := rfl

/-- The zero of `baseChange g 𝓔` is `g ≫ 𝓔.zero`. -/
@[simp] theorem baseChange_zero (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChange g 𝓔).zero = g ≫ 𝓔.zero := rfl

/-- **Base change of a morphism of shtukas**: the pullbacks along `id_X × g` of its two
components. -/
def baseChangeMap (g : S' ⟶ S) {𝓔 𝓕 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) :
    baseChange g 𝓔 ⟶ baseChange g 𝓕 where
  hom := (Scheme.Modules.pullback (productMap g)).map α.hom
  hom' := (Scheme.Modules.pullback (productMap g)).map α.hom'
  pole_eq := by rw [baseChange_pole, baseChange_pole, α.pole_eq]
  zero_eq := by rw [baseChange_zero, baseChange_zero, α.zero_eq]
  j_comp := by
    dsimp only [baseChange_j, baseChange_E, baseChange_E']
    rw [← Functor.map_comp, ← Functor.map_comp, α.j_comp]
  t_comp := by
    have h := (frobeniusTwistBaseChangeIso p f hcard X g).hom.naturality α.hom
    dsimp only [Functor.comp_obj, Functor.comp_map] at h
    dsimp only [baseChange_t, baseChange_E, baseChange_E']
    rw [Category.assoc, ← Functor.map_comp, α.t_comp,
      Functor.map_comp, ← Category.assoc, ← Category.assoc, h, Category.assoc]

/-- The first component of `baseChangeMap g α` is the pullback of `α.hom` along `id_X × g`. -/
@[simp] theorem baseChangeMap_hom (g : S' ⟶ S) {𝓔 𝓕 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) :
    (baseChangeMap g α).hom = (Scheme.Modules.pullback (productMap g)).map α.hom := rfl

/-- The second component of `baseChangeMap g α` is the pullback of `α.hom'` along
`id_X × g`. -/
@[simp] theorem baseChangeMap_hom' (g : S' ⟶ S) {𝓔 𝓕 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) :
    (baseChangeMap g α).hom' = (Scheme.Modules.pullback (productMap g)).map α.hom' := rfl

variable (p f hcard X r) in
/-- **Base change of shtukas is a functor** `Sht(S) ⥤ Sht(S')`. -/
@[simps]
def baseChangeFunctor (g : S' ⟶ S) : Shtuka p f hcard X S r ⥤ Shtuka p f hcard X S' r where
  obj := baseChange g
  map := baseChangeMap g
  map_id 𝓔 := hom_ext (by simp) (by simp)
  map_comp α β := hom_ext (by simp) (by simp)

/-! ### Pseudofunctoriality -/

/-- **Unfolding the modification `t` of a base change, against a morphism of shtukas.** The
compatibility of a pair `(a, b)` with `t` for `baseChange g 𝓔` is its compatibility with the
transported modification `τ_{S'}^* (id × g)^* E ≅ (id × g)^* τ_S^* E ⟶ (id × g)^* E'`. -/
theorem baseChange_t_comp_of_eq {g : S' ⟶ S} {𝓔 : Shtuka p f hcard X S r}
    {𝓕 : Shtuka p f hcard X S' r} (a : (baseChange g 𝓔).E ⟶ 𝓕.E)
    (b : (baseChange g 𝓔).E' ⟶ 𝓕.E')
    (h : (frobeniusTwistBaseChangeIso p f hcard X g).hom.app 𝓔.E ≫
        (Scheme.Modules.pullback (productMap g)).map 𝓔.t ≫ b =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S')).map a ≫ 𝓕.t) :
    (baseChange g 𝓔).t ≫ b =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S')).map a ≫ 𝓕.t :=
  (Category.assoc _ _ _).trans h

/-- **Unfolding the modifications `t` of a base change and of an iterated base change**, against
a pair of maps between them. -/
theorem baseChange_t_comp_baseChange_of_eq {S'' : Over (Spec (.of k))} {g₃ : S'' ⟶ S}
    {g' : S'' ⟶ S'} {g : S' ⟶ S} {𝓔 : Shtuka p f hcard X S r}
    (a : (baseChange g₃ 𝓔).E ⟶ (baseChange g' (baseChange g 𝓔)).E)
    (b : (baseChange g₃ 𝓔).E' ⟶ (baseChange g' (baseChange g 𝓔)).E')
    (h : (frobeniusTwistBaseChangeIso p f hcard X g₃).hom.app 𝓔.E ≫
        (Scheme.Modules.pullback (productMap g₃)).map 𝓔.t ≫ b =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S'')).map a ≫
        (frobeniusTwistBaseChangeIso p f hcard X g').hom.app
          ((Scheme.Modules.pullback (productMap g)).obj 𝓔.E) ≫
          (Scheme.Modules.pullback (productMap g')).map
            ((frobeniusTwistBaseChangeIso p f hcard X g).hom.app 𝓔.E ≫
              (Scheme.Modules.pullback (productMap g)).map 𝓔.t)) :
    (baseChange g₃ 𝓔).t ≫ b =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S'')).map a ≫
        (baseChange g' (baseChange g 𝓔)).t :=
  (Category.assoc _ _ _).trans h

omit [IsSeparated X.hom] in
/-- The compatibility with `t` of the unit comparison `baseChange (𝟙 S) 𝓔 ⟶ 𝓔`, unfolded. -/
theorem frobeniusTwistBaseChangeIso_id_comp (𝓔 : Shtuka p f hcard X S r) :
    (frobeniusTwistBaseChangeIso p f hcard X (𝟙 S)).hom.app 𝓔.E ≫
        (Scheme.Modules.pullback (productMap (𝟙 S))).map 𝓔.t ≫
          (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
            Scheme.Modules.pullbackId _).hom.app 𝓔.E' =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S)).map
        ((Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
          Scheme.Modules.pullbackId _).hom.app 𝓔.E) ≫ 𝓔.t := by
  have h := (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
    Scheme.Modules.pullbackId _).hom.naturality 𝓔.t
  dsimp only [Functor.id_map, Functor.id_obj] at h
  rw [h, ← Category.assoc]
  exact congrArg (· ≫ 𝓔.t)
    (modulesPullbackSquareIso_hom_app_comp_pullbackId (productMap_id X) _ 𝓔.E)

omit [IsSeparated X.hom] in
/-- The compatibility with `t` of the composition comparison
`baseChange (g' ≫ g) 𝓔 ⟶ baseChange g' (baseChange g 𝓔)`, unfolded. -/
theorem frobeniusTwistBaseChangeIso_comp_comp {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S')
    (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (frobeniusTwistBaseChangeIso p f hcard X (g' ≫ g)).hom.app 𝓔.E ≫
        (Scheme.Modules.pullback (productMap (g' ≫ g))).map 𝓔.t ≫
          (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
            (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E' =
      (Scheme.Modules.pullback (frobeniusTwist p f hcard X S'')).map
          ((Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
            (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E) ≫
        (frobeniusTwistBaseChangeIso p f hcard X g').hom.app
          ((Scheme.Modules.pullback (productMap g)).obj 𝓔.E) ≫
          (Scheme.Modules.pullback (productMap g')).map
            ((frobeniusTwistBaseChangeIso p f hcard X g).hom.app 𝓔.E ≫
              (Scheme.Modules.pullback (productMap g)).map 𝓔.t) := by
  have h := (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm).hom.naturality 𝓔.t
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  rw [h, ← Category.assoc, Functor.map_comp]
  have hc := modulesPullbackSquareIso_hom_app_comp_pullbackComp (productMap_comp X g' g)
    (frobeniusTwist_comp_productMap p f hcard g') (frobeniusTwist_comp_productMap p f hcard g)
    (frobeniusTwist_comp_productMap p f hcard (g' ≫ g)) 𝓔.E
  dsimp only [frobeniusTwistBaseChangeIso]
  rw [hc]
  simp only [Category.assoc]

/-- The unit comparison `baseChange (𝟙 S) 𝓔 ⟶ 𝓔`: pullback along `id_X × 𝟙_S = 𝟙` on both
components. -/
def baseChangeIdHom (𝓔 : Shtuka p f hcard X S r) : baseChange (𝟙 S) 𝓔 ⟶ 𝓔 where
  hom := (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
    Scheme.Modules.pullbackId _).hom.app 𝓔.E
  hom' := (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
    Scheme.Modules.pullbackId _).hom.app 𝓔.E'
  pole_eq := Category.id_comp _
  zero_eq := Category.id_comp _
  j_comp := (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
    Scheme.Modules.pullbackId _).hom.naturality 𝓔.j
  t_comp := baseChange_t_comp_of_eq _ _ (frobeniusTwistBaseChangeIso_id_comp 𝓔)

/-- The composition comparison `baseChange (g' ≫ g) 𝓔 ⟶ baseChange g' (baseChange g 𝓔)`:
pullback along `id_X × (g' ≫ g) = (id_X × g') ≫ (id_X × g)` on both components. -/
def baseChangeCompHom {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S') (g : S' ⟶ S)
    (𝓔 : Shtuka p f hcard X S r) : baseChange (g' ≫ g) 𝓔 ⟶ baseChange g' (baseChange g 𝓔) where
  hom := (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E
  hom' := (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E'
  pole_eq := Category.assoc _ _ _
  zero_eq := Category.assoc _ _ _
  j_comp := (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm).hom.naturality 𝓔.j
  t_comp := baseChange_t_comp_baseChange_of_eq _ _ (frobeniusTwistBaseChangeIso_comp_comp g' g 𝓔)

/-- The unit comparison `baseChangeIdHom 𝓔` is an isomorphism. -/
instance (𝓔 : Shtuka p f hcard X S r) : IsIso (baseChangeIdHom 𝓔) := by
  have : IsIso (baseChangeIdHom 𝓔).hom := inferInstanceAs (IsIso
    ((Scheme.Modules.pullbackCongr (productMap_id X) ≪≫ Scheme.Modules.pullbackId _).hom.app
      𝓔.E))
  have : IsIso (baseChangeIdHom 𝓔).hom' := inferInstanceAs (IsIso
    ((Scheme.Modules.pullbackCongr (productMap_id X) ≪≫ Scheme.Modules.pullbackId _).hom.app
      𝓔.E'))
  exact isIso_of_isIso _

/-- The composition comparison `baseChangeCompHom g' g 𝓔` is an isomorphism. -/
instance {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S') (g : S' ⟶ S)
    (𝓔 : Shtuka p f hcard X S r) : IsIso (baseChangeCompHom g' g 𝓔) := by
  have : IsIso (baseChangeCompHom g' g 𝓔).hom := inferInstanceAs (IsIso
    ((Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
      (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E))
  have : IsIso (baseChangeCompHom g' g 𝓔).hom' := inferInstanceAs (IsIso
    ((Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
      (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E'))
  exact isIso_of_isIso _

/-- **Base change along the identity is the identity**: `baseChange (𝟙 S) 𝓔 ≅ 𝓔`. -/
def baseChangeIdIso (𝓔 : Shtuka p f hcard X S r) : baseChange (𝟙 S) 𝓔 ≅ 𝓔 :=
  asIso (baseChangeIdHom 𝓔)

/-- **Base change along a composite is the iterated base change**:
`baseChange (g' ≫ g) 𝓔 ≅ baseChange g' (baseChange g 𝓔)`. -/
def baseChangeCompIso {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S') (g : S' ⟶ S)
    (𝓔 : Shtuka p f hcard X S r) : baseChange (g' ≫ g) 𝓔 ≅ baseChange g' (baseChange g 𝓔) :=
  asIso (baseChangeCompHom g' g 𝓔)

/-- The first component of `(baseChangeIdIso 𝓔).hom` is the canonical isomorphism
`(id_X × 𝟙_S)^* 𝓔.E ≅ 𝓔.E`. -/
@[simp] theorem baseChangeIdIso_hom_hom (𝓔 : Shtuka p f hcard X S r) :
    (baseChangeIdIso 𝓔).hom.hom = (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
      Scheme.Modules.pullbackId _).hom.app 𝓔.E := rfl

/-- The second component of `(baseChangeIdIso 𝓔).hom` is the canonical isomorphism
`(id_X × 𝟙_S)^* 𝓔.E' ≅ 𝓔.E'`. -/
@[simp] theorem baseChangeIdIso_hom_hom' (𝓔 : Shtuka p f hcard X S r) :
    (baseChangeIdIso 𝓔).hom.hom' = (Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
      Scheme.Modules.pullbackId _).hom.app 𝓔.E' := rfl

/-- The first component of `(baseChangeCompIso g' g 𝓔).hom` is the canonical isomorphism
`(id_X × (g' ≫ g))^* 𝓔.E ≅ (id_X × g')^* (id_X × g)^* 𝓔.E`. -/
@[simp] theorem baseChangeCompIso_hom_hom {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S')
    (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChangeCompIso g' g 𝓔).hom.hom =
      (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
        (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E := rfl

/-- The second component of `(baseChangeCompIso g' g 𝓔).hom` is the canonical isomorphism
`(id_X × (g' ≫ g))^* 𝓔.E' ≅ (id_X × g')^* (id_X × g)^* 𝓔.E'`. -/
@[simp] theorem baseChangeCompIso_hom_hom' {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S')
    (g : S' ⟶ S) (𝓔 : Shtuka p f hcard X S r) :
    (baseChangeCompIso g' g 𝓔).hom.hom' =
      (Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
        (Scheme.Modules.pullbackComp _ _).symm).hom.app 𝓔.E' := rfl

variable (p f hcard X S r) in
/-- **Pseudofunctoriality of base change, unit.** `baseChangeFunctor (𝟙 S) ≅ 𝟭`. -/
def baseChangeFunctorId : baseChangeFunctor p f hcard X r (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents baseChangeIdIso fun α => hom_ext
    ((Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
      Scheme.Modules.pullbackId _).hom.naturality α.hom)
    ((Scheme.Modules.pullbackCongr (productMap_id X) ≪≫
      Scheme.Modules.pullbackId _).hom.naturality α.hom')

variable (p f hcard X r) in
/-- **Pseudofunctoriality of base change, composition.**
`baseChangeFunctor (g' ≫ g) ≅ baseChangeFunctor g ⋙ baseChangeFunctor g'`. -/
def baseChangeFunctorComp {S'' : Over (Spec (.of k))} (g' : S'' ⟶ S') (g : S' ⟶ S) :
    baseChangeFunctor p f hcard X r (g' ≫ g) ≅
      baseChangeFunctor p f hcard X r g ⋙ baseChangeFunctor p f hcard X r g' :=
  NatIso.ofComponents (baseChangeCompIso g' g) fun α => hom_ext
    ((Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
      (Scheme.Modules.pullbackComp _ _).symm).hom.naturality α.hom)
    ((Scheme.Modules.pullbackCongr (productMap_comp X g' g) ≪≫
      (Scheme.Modules.pullbackComp _ _).symm).hom.naturality α.hom')

end Shtuka

end Stacks.Drinfeld
