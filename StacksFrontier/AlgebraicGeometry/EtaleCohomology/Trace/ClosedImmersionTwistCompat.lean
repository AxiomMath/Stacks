module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqPasting
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqPasting

/-!
# The base change map along a closed immersion and the Frobenius twists

For a closed immersion `i : Z ⟶ Y` of schemes over a finite field `k` with base change
`i_k̄ : Z_k̄ ⟶ Y_k̄`, the base change map `β : (i_* M)|_{Y_k̄} ⟶ (i_k̄)_*(M|_{Z_k̄})` is an
isomorphism and carries the canonical Frobenius twist of `(i_* M)|_{Y_k̄}` to `(i_k̄)_*` of the
twist of `M|_{Z_k̄}`.  This is the input of the closed immersion invariance of the canonical
Frobenius trace in Step 2 of the proof of [Stacks, Tag 03UG].

The proof is mate calculus: an abstract unit formula for a base change map
(`Stacks.CategoryTheory.BaseChange.unit_comp_map_map`), an abstract compatibility of base change
with twists (`Stacks.CategoryTheory.BaseChange.baseChange_comp_twist_eq`), and two scheme-level
inputs, the coherence of the direct-image comparisons around the cube
(`Stacks.EtaleCohomology.directImageComp_cube_coherence`, a section-level chase into iterated
base changes) and the compatibility of the Frobenius descent isomorphism of [Stacks, Tag 03SR]
with direct images.

## Main results

* `Stacks.EtaleCohomology.unit_comp_map_etaleModuleBaseChange`
* `Stacks.EtaleCohomology.etaleModuleBaseChange_comp_twist`
* `Stacks.EtaleCohomology.geometricFrobeniusPushforwardIso_hom_app_directImage`
* `Stacks.EtaleCohomology.etaleModuleBaseChange_comp_frobeniusBaseChangeTwist`
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.CategoryTheory.BaseChange

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} (adjg : Lg ⊣ Rg) {Li : A ⥤ B} {Ri : B ⥤ A} (adji : Li ⊣ Ri)
  {Li' : A' ⥤ B'} {Ri' : B' ⥤ A'} (adji' : Li' ⊣ Ri') {Lg' : B ⥤ B'} {Rg' : B' ⥤ B}
  (adjg' : Lg' ⊣ Rg') {Lc : A ⥤ B'} {Rc : B' ⥤ A} (adjc : Lc ⊣ Rc)
  (eg : Lg ⋙ Li' ≅ Lc) (ef : Li ⋙ Lg' ≅ Lc) (e₁ : Ri' ⋙ Rg ≅ Rc) (e₂ : Rg' ⋙ Ri ≅ Rc)

/-- **The unit formula for the base change map.**  When the two comparisons of left adjoints
around the square are conjugate to comparisons `e₁`, `e₂` of the right adjoints, the base change
map `Lg Ri ⟶ Ri' Lg'` followed through the unit of `Lg ⊣ Rg` is `Ri` of the unit of `Lg' ⊣ Rg'`
followed by the comparison `Ri Rg' ≅ Rc ≅ Rg Ri'`. -/
theorem unit_comp_map_map
    (hg : conjugateEquiv adjc (adjg.comp adji') eg.hom = e₁.inv)
    (hf : conjugateEquiv adjc (adji.comp adjg') ef.hom = e₂.inv) (M : B) :
    adjg.unit.app (Ri.obj M) ≫ Rg.map (map adji adji' eg ef M) =
      Ri.map (adjg'.unit.app M) ≫ e₂.hom.app (Lg'.obj M) ≫ e₁.inv.app (Lg'.obj M) := by
  apply ((adjg.comp adji').homEquiv _ _).symm.injective
  have h₁ := Stacks.EtaleCohomology.conjugateEquiv_homEquiv_symm adjc (adjg.comp adji') eg.hom
    (Ri.map (adjg'.unit.app M) ≫ e₂.hom.app (Lg'.obj M))
  have h₂ := Stacks.EtaleCohomology.conjugateEquiv_homEquiv_symm adjc (adji.comp adjg') ef.hom
    (Ri.map (adjg'.unit.app M) ≫ e₂.hom.app (Lg'.obj M))
  rw [hg] at h₁
  rw [hf] at h₂
  dsimp only [Functor.id_obj] at h₁ h₂
  have h₃ : (adjc.homEquiv (Ri.obj M) (Lg'.obj M)).symm
      (Ri.map (adjg'.unit.app M) ≫ e₂.hom.app (Lg'.obj M)) =
        ef.inv.app (Ri.obj M) ≫ Lg'.map (adji.counit.app M) := by
    rw [← cancel_epi (ef.hom.app (Ri.obj M)), h₂, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, Category.assoc, Iso.hom_inv_id_app]
    simp [Adjunction.comp_homEquiv, Adjunction.homEquiv_counit]
  simp only [Category.assoc] at h₁
  refine Eq.trans ?_ h₁
  rw [h₃, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  dsimp only [Functor.id_obj]
  rw [← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  exact homEquiv_symm_map adji adji' eg ef M

/-- The comparison of left adjoints produced by `leftAdjointUniq` against a transported
adjunction is conjugate to the transporting isomorphism. -/
alias conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv :=
  Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv

section TwistCompat

variable {CY : Type*} {CY' : Type*} {CZ : Type*} {CZ' : Type*}
  [Category* CY] [Category* CY'] [Category* CZ] [Category* CZ']
  {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY} (adjg : Lg ⊣ Rg) {Lg' : CZ ⥤ CZ'} {Rg' : CZ' ⥤ CZ}
  (adjg' : Lg' ⊣ Rg') {Ri : CZ ⥤ CY} {Ri' : CZ' ⥤ CY'} {Ra : CY' ⥤ CY'} {Rb : CY ⥤ CY}
  {Ra' : CZ' ⥤ CZ'} {Rb' : CZ ⥤ CZ}
  (ψ : 𝟭 CY ⟶ Rb) (ψ' : 𝟭 CZ ⟶ Rb') (compsY : Rg ⋙ Rb ⟶ Ra ⋙ Rg)
  (compsZ : Rg' ⋙ Rb' ⟶ Ra' ⋙ Rg') (c : Rg' ⋙ Ri ⟶ Ri' ⋙ Rg) (d : Rb' ⋙ Ri ⟶ Ri ⋙ Rb)
  (ρ : Ra' ⋙ Ri' ⟶ Ri' ⋙ Ra) (β : Ri ⋙ Lg ⟶ Lg' ⋙ Ri') (tw : Lg ⟶ Lg ⋙ Ra)
  (tw' : Lg' ⟶ Lg' ⋙ Ra')

/-- **Base change maps intertwine base change twists**, abstractly.  Let `tw : Lg ⟶ Lg ⋙ Ra`
and `tw' : Lg' ⟶ Lg' ⋙ Ra'` be adjoint to `ψ ≫ Rb(unit) ≫ compsY` and
`ψ' ≫ Rb'(unit) ≫ compsZ`, and let `β : Ri ⋙ Lg ⟶ Lg' ⋙ Ri'` satisfy the unit formula through
`c`.  If `ψ` restricts to `ψ'` through `d` and the comparisons `compsY`, `compsZ`, `c`, `d`, `ρ`
are coherent, then `β` followed by `Ri'(tw')` and `ρ` is `tw` followed by `Ra(β)`. -/
theorem baseChange_comp_twist_eq
    (htw : ∀ L, adjg.unit.app L ≫ Rg.map (tw.app L) =
      ψ.app L ≫ Rb.map (adjg.unit.app L) ≫ compsY.app (Lg.obj L))
    (htw' : ∀ L, adjg'.unit.app L ≫ Rg'.map (tw'.app L) =
      ψ'.app L ≫ Rb'.map (adjg'.unit.app L) ≫ compsZ.app (Lg'.obj L))
    (hU : ∀ M, adjg.unit.app (Ri.obj M) ≫ Rg.map (β.app M) =
      Ri.map (adjg'.unit.app M) ≫ c.app (Lg'.obj M))
    (hψ : ∀ M, ψ.app (Ri.obj M) = Ri.map (ψ'.app M) ≫ d.app M)
    (hcoh : ∀ N, Ri.map (compsZ.app N) ≫ c.app (Ra'.obj N) ≫ Rg.map (ρ.app N) =
      d.app (Rg'.obj N) ≫ Rb.map (c.app N) ≫ compsY.app (Ri'.obj N)) (M : CZ) :
    β.app M ≫ Ri'.map (tw'.app M) ≫ ρ.app (Lg'.obj M) =
      tw.app (Ri.obj M) ≫ Ra.map (β.app M) := by
  apply (adjg.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hc := c.naturality (tw'.app M)
  have hY := compsY.naturality (β.app M)
  have hd := d.naturality (adjg'.unit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hc hY hd
  rw [← Category.assoc (adjg.unit.app _), hU, ← Category.assoc (adjg.unit.app _), htw,
    Category.assoc, ← Category.assoc (c.app _), ← hc, Category.assoc, ← Category.assoc,
    ← Functor.map_comp, htw' M]
  rw [Category.assoc, Category.assoc, ← hY, ← Category.assoc (Rb.map _), ← Functor.map_comp, hU,
    hψ M]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hd, hcoh]

end TwistCompat

end Stacks.CategoryTheory.BaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- The comparison `(f ≫ g)^{-1} ≅ g^{-1} ⋙ f^{-1}` of inverse images of sheaves of modules is
conjugate to the composition isomorphism of the direct images. -/
theorem conjugateEquiv_etaleModuleInverseImageCompIso_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
        ((etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
        (etaleModuleInverseImageCompIso.{u, r} Λ f g).inv =
      (etaleModuleDirectImageComp.{u, r} Λ f g (f ≫ g) rfl).inv := by
  refine (Stacks.CategoryTheory.BaseChange.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv
    _ _ _).trans ?_
  rfl

/-- `Stacks.EtaleCohomology.conjugateEquiv_etaleModuleInverseImageCompIso_inv` with the
composite named. -/
theorem conjugateEquiv_etaleModuleInverseImageCompIso_inv' {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (h : fg = f ≫ g) :
    conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ fg)
        ((etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
        ((etaleModuleInverseImageCompIso.{u, r} Λ f g).inv ≫
          eqToHom (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) h.symm)) =
      (etaleModuleDirectImageComp.{u, r} Λ f g fg h).inv := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact conjugateEquiv_etaleModuleInverseImageCompIso_inv Λ f g

section BaseChangeUnit

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)
  (w : i' ≫ g = g' ≫ i)

/-- **The unit formula for the base change map of a square.**  The base change map
`β : g^{-1} i_* ⟶ i'_* g'^{-1}` followed through the unit of `g^{-1} ⊣ g_*` is `i_*` of the unit
of `g'^{-1} ⊣ g'_*` followed by the comparison `i_* g'_* ≅ (g' ≫ i)_* = (i' ≫ g)_* ≅ g_* i'_*`. -/
theorem unit_comp_map_etaleModuleBaseChange (M : EtaleModules.{u, r} Λ Z) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app ((etaleModuleDirectImage.{u, r} Λ i).obj M) ≫
        (etaleModuleDirectImage.{u, r} Λ g).map ((etaleModuleBaseChange Λ i i' g g' w).app M) =
      (etaleModuleDirectImage.{u, r} Λ i).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app M) ≫
        (etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) w).hom.app
          ((etaleModuleInverseImage.{u, r} Λ g').obj M) ≫
        (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.app
          ((etaleModuleInverseImage.{u, r} Λ g').obj M) :=
  Stacks.CategoryTheory.BaseChange.unit_comp_map_map (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleModuleInverseImageAdj.{u, r} Λ i) (etaleModuleInverseImageAdj.{u, r} Λ i')
    (etaleModuleInverseImageAdj.{u, r} Λ g') (etaleModuleInverseImageAdj.{u, r} Λ (i' ≫ g))
    (etaleModuleInverseImageCompIso.{u, r} Λ i' g).symm
    (etaleModuleBaseChangeComparison Λ i i' g g' w)
    (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl)
    (etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) w)
    (conjugateEquiv_etaleModuleInverseImageCompIso_inv Λ i' g)
    (conjugateEquiv_etaleModuleInverseImageCompIso_inv' Λ g' i (i' ≫ g) w) M

end BaseChangeUnit

section Coherence

variable (Λ : Type r) [Ring Λ]

private lemma assocChain₃ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ : D} {p q : O₀ ⟶ O₁}
    {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {c : O₃ ⟶ O₄} (h : p ≫ a ≫ b ≫ c = q ≫ a ≫ b ≫ c) :
    ((p ≫ a) ≫ b) ≫ c = ((q ≫ a) ≫ b) ≫ c := by
  simpa only [Category.assoc] using h

private lemma sndChain₃ {D : Type*} [Category* D] {O₀ O₀' O₁ O₂ O₃ O₄ O₅ : D} {p q : O₀ ⟶ O₁}
    {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {c : O₃ ⟶ O₄} {s : O₂ ⟶ O₅} {f : O₅ ⟶ O₄} {t : O₀ ⟶ O₀'}
    {g : O₀' ⟶ O₅} (hcond : b ≫ c = s ≫ f) (hp : p ≫ a ≫ s = t ≫ g) (hq : q ≫ a ≫ s = t ≫ g) :
    ((p ≫ a) ≫ b) ≫ c = ((q ≫ a) ≫ b) ≫ c := by
  simp only [Category.assoc, hcond, reassoc_of% hp, reassoc_of% hq]

/-- A morphism into a three-fold iterated base change is determined by its composite first
projection onto the original object. -/
lemma smallEtaleBaseChange_hom_ext₃ {A B C D : Scheme.{u}} (f₁ : A ⟶ B) (f₂ : B ⟶ C) (f₃ : C ⟶ D)
    {T : A.Etale} {W : D.Etale}
    {p q : T ⟶ (smallEtaleBaseChange f₁).obj
      ((smallEtaleBaseChange f₂).obj ((smallEtaleBaseChange f₃).obj W))}
    (h : p.left ≫ pullback.fst _ f₁ ≫ pullback.fst _ f₂ ≫ pullback.fst W.hom f₃ =
      q.left ≫ pullback.fst _ f₁ ≫ pullback.fst _ f₂ ≫ pullback.fst W.hom f₃) : p = q :=
  smallEtaleBaseChange_hom_ext f₁ (pullback.hom_ext (pullback.hom_ext (assocChain₃ h)
    (sndChain₃ (pullback.condition (f := ((smallEtaleBaseChange f₃).obj W).hom) (g := f₂))
      (smallEtaleBaseChange_fst_snd f₁ f₂ p) (smallEtaleBaseChange_fst_snd f₁ f₂ q)))
    ((smallEtaleBaseChange_fst_snd f₁ f₂ p).trans (smallEtaleBaseChange_fst_snd f₁ f₂ q).symm))


private lemma opChain₆ {C D : Type*} [Category* C] [Category* D] (G : Cᵒᵖ ⥤ D)
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ P₁ P₂ P₃ P₄ P₅ : C} {x₁ : O₁ ⟶ O₀} {x₂ : O₂ ⟶ O₁} {x₃ : O₃ ⟶ O₂}
    {x₄ : O₄ ⟶ O₃} {x₅ : O₅ ⟶ O₄} {x₆ : O₆ ⟶ O₅} {y₁ : P₁ ⟶ O₀} {y₂ : P₂ ⟶ P₁} {y₃ : P₃ ⟶ P₂}
    {y₄ : P₄ ⟶ P₃} {y₅ : P₅ ⟶ P₄} {y₆ : O₆ ⟶ P₅}
    (h : x₆ ≫ x₅ ≫ x₄ ≫ x₃ ≫ x₂ ≫ x₁ = y₆ ≫ y₅ ≫ y₄ ≫ y₃ ≫ y₂ ≫ y₁) :
    (G.map x₁.op ≫ G.map x₂.op) ≫ (G.map x₃.op ≫ G.map x₄.op) ≫ G.map x₅.op ≫ G.map x₆.op =
      (G.map y₁.op ≫ G.map y₂.op) ≫ (G.map y₃.op ≫ G.map y₄.op) ≫ G.map y₅.op ≫
        G.map y₆.op := by
  simp only [← Functor.map_comp, ← op_comp, Category.assoc, h]

private lemma projChain₆ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ V : D}
    {l₁ : O₁ ⟶ O₀} {l₂ : O₂ ⟶ O₁} {l₃ : O₃ ⟶ O₂} {l₄ : O₄ ⟶ O₃} {l₅ : O₅ ⟶ O₄} {l₆ : O₆ ⟶ O₅}
    {φ₀ : O₀ ⟶ V} {φ₁ : O₁ ⟶ V} {φ₂ : O₂ ⟶ V} {φ₃ : O₃ ⟶ V} {φ₄ : O₄ ⟶ V} {φ₅ : O₅ ⟶ V}
    {φ₆ : O₆ ⟶ V} (h₁ : l₁ ≫ φ₀ = φ₁) (h₂ : l₂ ≫ φ₁ = φ₂) (h₃ : l₃ ≫ φ₂ = φ₃)
    (h₄ : l₄ ≫ φ₃ = φ₄) (h₅ : l₅ ≫ φ₄ = φ₅) (h₆ : l₆ ≫ φ₅ = φ₆) :
    (l₆ ≫ l₅ ≫ l₄ ≫ l₃ ≫ l₂ ≫ l₁) ≫ φ₀ = φ₆ := by
  simp only [Category.assoc, h₁, h₂, h₃, h₄, h₅, h₆]

/-- A step of a projection chase: `x ≫ f₁ ≫ f₂ = f₃` followed by `f₄`. -/
lemma stepHom {D : Type*} [Category* D] {A B C E F : D} {x : A ⟶ B} {f₁ : B ⟶ C}
    {f₂ : C ⟶ E} {f₃ : A ⟶ E} (f₄ : E ⟶ F) (h : x ≫ f₁ ≫ f₂ = f₃) :
    x ≫ f₁ ≫ f₂ ≫ f₄ = f₃ ≫ f₄ := by
  rw [← h]; simp only [Category.assoc]

/-- A step of a projection chase: `x ≫ f₁ = f₂ ≫ f₃` followed by `f₄`. -/
lemma stepInv {D : Type*} [Category* D] {A B C E F : D} {x : A ⟶ B} {f₁ : B ⟶ E}
    {f₂ : A ⟶ C} {f₃ : C ⟶ E} (f₄ : E ⟶ F) (h : x ≫ f₁ = f₂ ≫ f₃) :
    x ≫ f₁ ≫ f₄ = f₂ ≫ f₃ ≫ f₄ := by
  rw [← Category.assoc, h, Category.assoc]

/-- A step of a projection chase through a base-changed morphism `m`, composite form. -/
lemma stepMapHom {D : Type*} [Category* D] {A B C C' E F : D} {x : A ⟶ B} {f₁ : B ⟶ C}
    {f₂ : A ⟶ C'} {m : C' ⟶ C} {n₁ : C ⟶ E} {n₂ : E ⟶ F} {n₃ : C' ⟶ F}
    (hx : x ≫ f₁ = f₂ ≫ m) (hm : m ≫ n₁ ≫ n₂ = n₃) : x ≫ f₁ ≫ n₁ ≫ n₂ = f₂ ≫ n₃ := by
  rw [← Category.assoc, hx, Category.assoc, hm]

/-- A step of a projection chase through a base-changed morphism `m`, factored form. -/
lemma stepMapInv {D : Type*} [Category* D] {A B C C' F G : D} {x : A ⟶ B}
    {f₁ : B ⟶ C} {f₂ : A ⟶ C'} {m : C' ⟶ C} {n₁ : C ⟶ F} {n₂ : C' ⟶ G} {n₃ : G ⟶ F}
    (hx : x ≫ f₁ = f₂ ≫ m) (hm : m ≫ n₁ = n₂ ≫ n₃) : x ≫ f₁ ≫ n₁ = f₂ ≫ n₂ ≫ n₃ := by
  rw [← Category.assoc, hx, Category.assoc, hm]

/-- Sections of the direct image of a morphism of sheaves of modules. -/
lemma directImage_map_hom_app {X Y : Scheme.{u}} (h : X ⟶ Y)
    {F G : EtaleModules.{u, r} Λ X} (x : F ⟶ G) (U : (Y.Etale)ᵒᵖ) :
    ((etaleModuleDirectImage.{u, r} Λ h).map x).hom.app U =
      x.hom.app (op ((smallEtaleBaseChange h).obj U.unop)) := rfl

/-- Restriction maps of the direct image of a sheaf of modules. -/
lemma directImage_obj_map {X Y : Scheme.{u}} (h : X ⟶ Y) (F : EtaleModules.{u, r} Λ X)
    {U V : (Y.Etale)ᵒᵖ} (m : U ⟶ V) :
    ((etaleModuleDirectImage.{u, r} Λ h).obj F).obj.map m =
      F.obj.map (op ((smallEtaleBaseChange h).map m.unop)) := rfl

variable {Z Z' Y Y' : Scheme.{u}} (i : Z ⟶ Y) (i' : Z' ⟶ Y') (g : Y' ⟶ Y) (g' : Z' ⟶ Z)
  (a : Y' ⟶ Y') (b : Y ⟶ Y) (a' : Z' ⟶ Z') (b' : Z ⟶ Z) (w : a ≫ g = g ≫ b)
  (w' : a' ≫ g' = g' ≫ b') (hi : i' ≫ g = g' ≫ i) (ha : a' ≫ i' = i' ≫ a) (hb : b' ≫ i = i ≫ b)

/-- **Coherence of the comparisons of direct images around the cube** formed by the two base
change squares and the twist squares. -/
theorem directImageComp_cube_coherence (N : EtaleModules.{u, r} Λ Z') :
    (etaleModuleDirectImage.{u, r} Λ i).map
        ((etaleModuleDirectImageComp.{u, r} Λ g' b' (a' ≫ g') w').hom.app N ≫
          (etaleModuleDirectImageComp.{u, r} Λ a' g' (a' ≫ g') rfl).inv.app N) ≫
      ((etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom.app
          ((etaleModuleDirectImage.{u, r} Λ a').obj N) ≫
        (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.app
          ((etaleModuleDirectImage.{u, r} Λ a').obj N)) ≫
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((directImageTwistTransfer Λ i' a' a ha).app N) =
    (directImageTwistTransfer Λ i b' b hb).app ((etaleModuleDirectImage.{u, r} Λ g').obj N) ≫
      (etaleModuleDirectImage.{u, r} Λ b).map
        ((etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom.app N ≫
          (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.app N) ≫
      ((etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom.app
          ((etaleModuleDirectImage.{u, r} Λ i').obj N) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv.app
          ((etaleModuleDirectImage.{u, r} Λ i').obj N)) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  simp only [directImageTwistTransfer, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.map_comp, directImage_map_hom_app, etaleModuleDirectImageComp_hom_app_hom_app,
    etaleModuleDirectImageComp_inv_app_hom_app, directImage_obj_map]
  refine opChain₆ N.obj (smallEtaleBaseChange_hom_ext₃ g' b' i ?_)
  exact Eq.trans
    (projChain₆ (stepHom _ (smallEtaleBaseChangeComp'_fst_fst g' b' (a' ≫ g') w' _))
      (stepInv _ (smallEtaleBaseChangeComp'_inv_fst a' g' (a' ≫ g') rfl _))
      (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst g' i (i' ≫ g) hi _))
      (stepMapInv (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_inv_fst i' g (i' ≫ g) rfl _))
      (stepHom _ (smallEtaleBaseChangeComp'_fst_fst a' i' (a' ≫ i') rfl _))
      (stepInv _ (smallEtaleBaseChangeComp'_inv_fst i' a (a' ≫ i') ha _)))
    (projChain₆ (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst b' i (b' ≫ i) rfl _))
      (stepMapInv (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_inv_fst i b (b' ≫ i) hb _))
      (stepHom _ (smallEtaleBaseChangeComp'_fst_fst g' i (i' ≫ g) hi _))
      (stepInv _ (smallEtaleBaseChangeComp'_inv_fst i' g (i' ≫ g) rfl _))
      (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst g b (a ≫ g) w _))
      (stepMapInv (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_inv_fst a g (a ≫ g) rfl _))).symm

end Coherence

section TwistCompat

variable {Z Z' Y Y' : Scheme.{u}} (i : Z ⟶ Y) (i' : Z' ⟶ Y') (g : Y' ⟶ Y) (g' : Z' ⟶ Z)
  (a : Y' ⟶ Y') (b : Y ⟶ Y) (a' : Z' ⟶ Z') (b' : Z ⟶ Z) (w : a ≫ g = g ≫ b)
  (w' : a' ≫ g' = g' ≫ b') (hi : i' ≫ g = g' ≫ i) (ha : a' ≫ i' = i' ≫ a) (hb : b' ≫ i = i ≫ b)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)
  (ψ' : 𝟭 (EtaleModules.{u, r} Λ Z) ⟶ etaleModuleDirectImage.{u, r} Λ b')

/-- The base change twist followed through the unit is the transformation it is adjoint to. -/
lemma unit_comp_etaleModuleBaseChangeTwist (L : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ).app L) =
      ψ.app L ≫ (etaleModuleDirectImage.{u, r} Λ b).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L) ≫
        ((etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv).app
          ((etaleModuleInverseImage.{u, r} Λ g).obj L) := by
  refine (Adjunction.homEquiv_unit _ _ _ _).symm.trans ?_
  rw [etaleModuleBaseChangeTwist_app, Equiv.apply_symm_apply]
  simp [etaleModuleBaseChangeTwistAdj]

/-- **The base change map along a closed immersion intertwines the base change twists.**  For
a cube formed by base change squares `i' ≫ g = g' ≫ i`, twist squares `a ≫ g = g ≫ b`,
`a' ≫ g' = g' ≫ b'` and compatibilities `a' ≫ i' = i' ≫ a`, `b' ≫ i = i ≫ b`, and transformations
`ψ : 𝟭 ⟶ b_*`, `ψ' : 𝟭 ⟶ b'_*` with `ψ` at `i_* M` equal to `i_* ψ'` followed by the
comparison `b'_* i_* ⟶ i_* b_*`, the base change map `β : g^{-1} i_* ⟶ i'_* g'^{-1}` carries the
twist of `g^{-1} i_* M` to `i'_*` of the twist of `g'^{-1} M` followed by the comparison
`i'_* a'_* ⟶ a_* i'_*`. -/
theorem etaleModuleBaseChange_comp_twist
    (hψ : ∀ M : EtaleModules.{u, r} Λ Z, ψ.app ((etaleModuleDirectImage.{u, r} Λ i).obj M) =
      (etaleModuleDirectImage.{u, r} Λ i).map (ψ'.app M) ≫
        (directImageTwistTransfer Λ i b' b hb).app M)
    (M : EtaleModules.{u, r} Λ Z) :
    (etaleModuleBaseChange Λ i i' g g' hi).app M ≫
        (etaleModuleDirectImage.{u, r} Λ i').map
          ((etaleModuleBaseChangeTwist.{u, r} Λ g' a' b' w' ψ').app M) ≫
        (directImageTwistTransfer Λ i' a' a ha).app ((etaleModuleInverseImage.{u, r} Λ g').obj M) =
      (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ).app
          ((etaleModuleDirectImage.{u, r} Λ i).obj M) ≫
        (etaleModuleDirectImage.{u, r} Λ a).map ((etaleModuleBaseChange Λ i i' g g' hi).app M) :=
  Stacks.CategoryTheory.BaseChange.baseChange_comp_twist_eq
    (etaleModuleInverseImageAdj.{u, r} Λ g) (etaleModuleInverseImageAdj.{u, r} Λ g') ψ ψ'
    ((etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom ≫
      (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv)
    ((etaleModuleDirectImageComp.{u, r} Λ g' b' (a' ≫ g') w').hom ≫
      (etaleModuleDirectImageComp.{u, r} Λ a' g' (a' ≫ g') rfl).inv)
    ((etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom ≫
      (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv)
    (directImageTwistTransfer Λ i b' b hb) (directImageTwistTransfer Λ i' a' a ha)
    (etaleModuleBaseChange Λ i i' g g' hi) (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ)
    (etaleModuleBaseChangeTwist.{u, r} Λ g' a' b' w' ψ')
    (unit_comp_etaleModuleBaseChangeTwist Λ g a b w ψ)
    (unit_comp_etaleModuleBaseChangeTwist Λ g' a' b' w' ψ')
    (unit_comp_map_etaleModuleBaseChange Λ i i' g g' hi) hψ
    (directImageComp_cube_coherence Λ i i' g g' a b a' b' w w' hi ha hb) M

end TwistCompat

section Frobenius

open Stacks.Frobenius

variable {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) (p q : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The geometric Frobenius commutes with morphisms over `k`. -/
lemma geometricFrobenius_left_comp (i : Z ⟶ Y) :
    (geometricFrobenius Z p q hcard).left ≫ i.left =
      i.left ≫ (geometricFrobenius Y p q hcard).left :=
  absoluteFrobeniusPow_naturality i.left p _ _ q

private lemma frobeniusPushChase {D : Type*} [Category* D] {A B C F G : D} {l : A ⟶ B}
    {h : B ⟶ C} {f₁ : C ⟶ B} {f₂ : B ⟶ F} {FV : B ⟶ B} {FW : F ⟶ F} {f₃ : A ⟶ G} {gi : G ⟶ F}
    {gh : F ⟶ G} {f₄ : G ⟶ F} (hγZ : h ≫ f₁ = FV) (hnat : FV ≫ f₂ = f₂ ≫ FW)
    (hmap : l ≫ f₂ = f₃ ≫ gi) (hγY : gh ≫ f₄ = FW) (hinv : gi ≫ gh = 𝟙 G) :
    l ≫ h ≫ f₁ ≫ f₂ = f₃ ≫ f₄ := by
  rw [← Category.assoc h, hγZ, hnat, ← Category.assoc, hmap, Category.assoc, ← hγY,
    ← Category.assoc gi, hinv, Category.id_comp]

private lemma compChase {D : Type*} [Category* D] {A B B' C F G : D} {u : A ⟶ B'} {v : B' ⟶ C}
    {f₁ : C ⟶ B} {f₂ : B ⟶ F} {f : B' ⟶ F} {f₃ : A ⟶ G} {f₄ : G ⟶ F}
    (hv : v ≫ f₁ ≫ f₂ = f) (hu : u ≫ f = f₃ ≫ f₄) : u ≫ v ≫ f₁ ≫ f₂ = f₃ ≫ f₄ := by
  rw [hv, hu]

private lemma pairChase {D : Type*} [Category* D] {A B B' C E : D} {l : A ⟶ B} {h : B ⟶ C}
    {u : A ⟶ B'} {v : B' ⟶ C} {r : C ⟶ E} {X : A ⟶ E} (hL : l ≫ h ≫ r = X)
    (hR : u ≫ v ≫ r = X) : (l ≫ h) ≫ r = (u ≫ v) ≫ r := by
  rw [Category.assoc, Category.assoc, hL, hR]

private lemma assocChain₂ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ : D} {p q : O₀ ⟶ O₁}
    {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} (h : p ≫ a ≫ b = q ≫ a ≫ b) : (p ≫ a) ≫ b = (q ≫ a) ≫ b := by
  simpa only [Category.assoc] using h

/-- A morphism into a twice iterated base change is determined by its composite first
projection onto the original object. -/
lemma smallEtaleBaseChange_hom_ext₂ {A B C : Scheme.{u}} (f₁ : A ⟶ B) (f₂ : B ⟶ C)
    {T : A.Etale} {W : C.Etale}
    {p q : T ⟶ (smallEtaleBaseChange f₁).obj ((smallEtaleBaseChange f₂).obj W)}
    (h : p.left ≫ pullback.fst _ f₁ ≫ pullback.fst W.hom f₂ =
      q.left ≫ pullback.fst _ f₁ ≫ pullback.fst W.hom f₂) : p = q :=
  smallEtaleBaseChange_hom_ext f₁ (pullback.hom_ext (assocChain₂ h)
    ((smallEtaleBaseChange_fst_snd f₁ f₂ p).trans (smallEtaleBaseChange_fst_snd f₁ f₂ q).symm))

private lemma opChain₃ {C D : Type*} [Category* C] [Category* D] (G : Cᵒᵖ ⥤ D)
    {O₀ O₁ O₂ O₃ : C} {x : O₃ ⟶ O₀} {y₁ : O₁ ⟶ O₀} {y₂ : O₂ ⟶ O₁} {y₃ : O₃ ⟶ O₂}
    (h : x = y₃ ≫ y₂ ≫ y₁) : G.map x.op = G.map y₁.op ≫ G.map y₂.op ≫ G.map y₃.op := by
  simp only [← Functor.map_comp, ← op_comp, Category.assoc, h]

/-- **The Frobenius descent isomorphism commutes with direct images**: for a morphism
`i : Z ⟶ Y` over `k` and a sheaf of modules `M` on `Z_étale`, the isomorphism
`i_* M ≅ (π_Y)_* i_* M` of [Stacks, Tag 03SR] is `i_*` of the one of `M` followed by the
comparison `i_* (π_Z)_* ⟶ (π_Y)_* i_*`. -/
@[sga "4½ Rapport 1.3" "special case"]
theorem geometricFrobeniusPushforwardIso_hom_app_directImage (M : EtaleModules.{u, r} Λ Z.left) :
    (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom.app
        ((etaleModuleDirectImage.{u, r} Λ i.left).obj M) =
      (etaleModuleDirectImage.{u, r} Λ i.left).map
          ((geometricFrobeniusPushforwardIso Z p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom.app M) ≫
        (directImageTwistTransfer Λ i.left (geometricFrobenius Z p q hcard).left
          (geometricFrobenius Y p q hcard).left
          (geometricFrobenius_left_comp p q hcard i)).app M := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  simp only [directImageTwistTransfer, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    directImage_map_hom_app, etaleModuleDirectImageComp_hom_app_hom_app,
    etaleModuleDirectImageComp_inv_app_hom_app, geometricFrobeniusPushforwardIso_hom_app_hom_app]
  refine opChain₃ M.obj ((cancel_mono ((geometricFrobeniusEtaleSiteIso Z p q hcard).hom.app
    ((smallEtaleBaseChange i.left).obj W.unop))).1 ?_)
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine smallEtaleBaseChange_hom_ext₂ _ i.left ?_
  have hop : ((NatTrans.op (geometricFrobeniusEtaleSiteIso Y p q hcard).symm.hom).app W).unop =
      (geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W.unop := rfl
  rw [hop]
  have hinv : ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W.unop).left ≫
      ((geometricFrobeniusEtaleSiteIso Y p q hcard).hom.app W.unop).left = 𝟙 _ :=
    congrArg (fun m => m.left) ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv_hom_id_app W.unop)
  have hmap := smallEtaleBaseChange_map_left_fst i.left
    ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W.unop)
  have hγZ := geometricFrobeniusEtaleSiteIso_hom_app_left_fst Z p q hcard
    ((smallEtaleBaseChange i.left).obj W.unop)
  have hγY := geometricFrobeniusEtaleSiteIso_hom_app_left_fst Y p q hcard W.unop
  have hnat := absoluteFrobeniusPow_naturality (pullback.fst W.unop.hom i.left) p
    (isInCharacteristic_of_hom ((smallEtaleBaseChange i.left).obj W.unop).hom p
      (Stacks.Frobenius.isInCharacteristic_of_over Z))
    (isInCharacteristic_of_hom W.unop.hom p (Stacks.Frobenius.isInCharacteristic_of_over Y)) q
  have hL := frobeniusPushChase hγZ hnat hmap hγY hinv
  have hR := (compChase
      (smallEtaleBaseChangeComp'_fst_fst (geometricFrobenius Z p q hcard).left i.left
        ((geometricFrobenius Z p q hcard).left ≫ i.left) rfl W.unop)
      (smallEtaleBaseChangeComp'_inv_fst i.left (geometricFrobenius Y p q hcard).left
        ((geometricFrobenius Z p q hcard).left ≫ i.left)
        (geometricFrobenius_left_comp p q hcard i) W.unop))
  exact pairChase hL hR

variable (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change `i_k̄ : Z_k̄ ⟶ Y_k̄` of a morphism `i : Z ⟶ Y` of schemes over `k`. -/
abbrev fieldBaseChangeMap : fieldBaseChange Z kbar ⟶ fieldBaseChange Y kbar :=
  pullback.map Z.hom (specAlgebraMap k kbar) Y.hom (specAlgebraMap k kbar) i.left (𝟙 _) (𝟙 _)
    (by simp) (by simp)

omit [Fintype k] in
/-- `i_k̄` lies over `i`. -/
lemma fieldBaseChangeMap_comp_fst :
    fieldBaseChangeMap i kbar ≫ fieldBaseChangeProj Y kbar = fieldBaseChangeProj Z kbar ≫ i.left :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
/-- `i_k̄` lies over `Spec k̄`. -/
lemma fieldBaseChangeMap_comp_snd :
    fieldBaseChangeMap i kbar ≫ pullback.snd Y.hom (specAlgebraMap k kbar) =
      pullback.snd Z.hom (specAlgebraMap k kbar) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `i_k̄` intertwines the base changes of the geometric Frobenius. -/
lemma geometricFrobeniusBaseChange_comp_fieldBaseChangeMap :
    geometricFrobeniusBaseChange Z kbar p q hcard ≫ fieldBaseChangeMap i kbar =
      fieldBaseChangeMap i kbar ≫ geometricFrobeniusBaseChange Y kbar p q hcard := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      geometricFrobeniusBaseChange_comp_fst_assoc, geometricFrobeniusBaseChange_comp_fst,
      geometricFrobenius_left_comp p q hcard i]
  · simp only [Category.assoc]
    rw [fieldBaseChangeMap_comp_snd, geometricFrobeniusBaseChange_comp_snd,
      geometricFrobeniusBaseChange_comp_snd, fieldBaseChangeMap_comp_snd]

/-- **The base change map intertwines the canonical Frobenius twists.**  For `i : Z ⟶ Y` over
`k` and a sheaf of modules `M` on `Z_étale`, the base change map
`β : (i_* M)|_{Y_k̄} ⟶ (i_k̄)_* (M|_{Z_k̄})` carries the canonical twist of `(i_* M)|_{Y_k̄}` to
`(i_k̄)_*` of the canonical twist of `M|_{Z_k̄}` followed by the comparison
`(i_k̄)_* π̄_{Z,*} ⟶ π̄_{Y,*} (i_k̄)_*`. -/
theorem etaleModuleBaseChange_comp_frobeniusBaseChangeTwist (M : EtaleModules.{u, r} Λ Z.left) :
    (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
        (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)).app M ≫
      (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)).map
        ((frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard).app M) ≫
      (directImageTwistTransfer Λ (fieldBaseChangeMap i kbar)
        (geometricFrobeniusBaseChange Z kbar p q hcard)
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).app
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar)).obj M) =
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app
        ((etaleModuleDirectImage.{u, r} Λ i.left).obj M) ≫
      (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        ((etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
          (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)).app M) :=
  etaleModuleBaseChange_comp_twist Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
    (fieldBaseChangeProj Z kbar) (geometricFrobeniusBaseChange Y kbar p q hcard)
    (geometricFrobenius Y p q hcard).left (geometricFrobeniusBaseChange Z kbar p q hcard)
    (geometricFrobenius Z p q hcard).left (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_fst Z kbar p q hcard) (fieldBaseChangeMap_comp_fst i kbar)
    (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
    (geometricFrobenius_left_comp p q hcard i)
    (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom
    (geometricFrobeniusPushforwardIso Z p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom
    (geometricFrobeniusPushforwardIso_hom_app_directImage Λ i p q hcard) M

omit [Fintype k] in
/-- The base change of a closed immersion over `k` to `k̄` is a closed immersion. -/
lemma isClosedImmersion_fieldBaseChangeMap [IsClosedImmersion i.left] :
    IsClosedImmersion (fieldBaseChangeMap i kbar) :=
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion i.left))
    (inferInstanceAs (IsClosedImmersion (𝟙 _))) (Over.w i).symm (Category.id_comp _).symm

omit [Fintype k] in
/-- The image of `i_k̄` is the inverse image of the image of `i`. -/
lemma range_fieldBaseChangeMap :
    Set.range (fieldBaseChangeMap i kbar) = fieldBaseChangeProj Y kbar ⁻¹' Set.range i.left := by
  rw [Scheme.Pullback.range_map]
  simp

omit [Fintype k] in
/-- **The base change map along a closed immersion over `k` is an isomorphism.** -/
theorem isIso_etaleModuleBaseChange_fieldBaseChangeMap [IsClosedImmersion i.left]
    (M : EtaleModules.{u, r} Λ Z.left) :
    IsIso ((etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)).app M) := by
  have := isClosedImmersion_fieldBaseChangeMap i kbar
  let U : Y.left.Opens :=
    ⟨(Set.range i.left)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U' : (fieldBaseChange Y kbar).Opens := fieldBaseChangeProj Y kbar ⁻¹ᵁ U
  refine isIso_etaleModuleBaseChange_of_isClosedImmersion Λ i.left (fieldBaseChangeMap i kbar)
    (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)
    U.ι U'.ι ?_ ?_ (fieldBaseChangeProj Y kbar ∣_ U) (morphismRestrict_ι _ _).symm M
  · exact U.range_ι
  · rw [U'.range_ι, range_fieldBaseChangeMap]
    rfl


end Frobenius

end Stacks.EtaleCohomology

end
