module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCoverComparison

/-!
# Characters are determined by their torsors after a cover of the base

Let `χ₁, χ₂` be characters of an open subgroup `V ⊆ π₁(X, x)` with torsor covers `T₁, T₂` over
the cover `Y` with fibre `π₁ ⧸ V`, and let `g : Z ⟶ Y` be a finite étale cover with a point `e`
of its fibre at `x` over the base coset. A morphism `T₁ ×_Y Z ⟶ T₂ ×_Y Z` over `Z` commuting with
the translations forces `χ₁ v = χ₂ v` for every `v ∈ V` fixing `e`: the points `(t, e)` of the
fibre of `T₁ ×_Y Z` over the base coset are moved by `v` exactly as `t` is, through `χ₁`, and the
morphism carries them to points of `T₂ ×_Y Z` moved through `χ₂`.

## Main results

* `Stacks.LAdic.eq_of_inducedTorsor_fiber`: the comparison of characters on the base fibre.
* `AlgebraicGeometry.CharacterTorsorData.eq_of_hom_baseChange`: the rigidity statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LAdic

variable {Γ : Type*} [Group Γ] {V : Subgroup Γ} {A : Type*} [AddCommGroup A]

/-- **Comparison of characters on the base fibre.** A map `a ↦ Φ a` from `A` to the induced
torsor of `χ₂`, compatible with translation, landing over the base coset at `0`, and sending
`χ₁ v` to `v • Φ 0`, forces `χ₁ v = χ₂ v`. -/
theorem eq_of_inducedTorsor_fiber {χ₁ χ₂ : V → A} {hadd₂ : ∀ a b, χ₂ (a * b) = χ₂ a + χ₂ b}
    (Φ : A → InducedTorsor V χ₂ hadd₂)
    (ht : ∀ a b, Φ (a + b) = InducedTorsor.translate b (Φ a))
    (hp : InducedTorsor.proj (Φ 0) = QuotientGroup.mk 1) (v : V)
    (hv : Φ (χ₁ v) = (v : Γ) • Φ 0) : χ₁ v = χ₂ v := by
  obtain ⟨a', ha'⟩ := InducedTorsor.exists_mk_one_of_proj _ hp
  have h1 : Φ (χ₁ v) = InducedTorsor.mk 1 (a' + χ₁ v) := by
    rw [← zero_add (χ₁ v), ht, ← ha', InducedTorsor.translate_mk, zero_add]
  rw [h1, ← ha', InducedTorsor.smul_mk_one] at hv
  exact add_left_cancel (InducedTorsor.mk_one_injective _ _ hv)

end Stacks.LAdic

namespace AlgebraicGeometry

open Stacks.LAdic Stacks.Kummer

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X}

/-- The fibre functor's map along a morphism of finite étale covers commutes with the action of
`π₁(X, x)` on fibres. -/
theorem finiteEtaleFiberFunctor_map_smul {Y Z : FiniteEtaleOver X} (f : Y ⟶ Z)
    (σ : EtaleFundamentalGroup X x) (y : (finiteEtaleFiberFunctor x).obj Y) :
    (finiteEtaleFiberFunctor x).map f (σ • y) = σ • (finiteEtaleFiberFunctor x).map f y :=
  (NatTrans.naturality_apply σ.hom f y).symm

omit [ConnectedSpace X] in
/-- The image of a fibre point `y` under the fibre functor's map along `f` is `y` composed with
`f.left`. -/
theorem finiteEtaleFiberFunctor_map_val {Y Z : FiniteEtaleOver X} (f : Y ⟶ Z)
    (y : (finiteEtaleFiberFunctor x).obj Y) :
    ((finiteEtaleFiberFunctor x).map f y).1 = y.1 ≫ f.left := rfl

/-- A finite étale cover of a finite étale cover, as a finite étale cover of the base. -/
abbrev FiniteEtaleOver.overComp {Y : FiniteEtaleOver X} {Z : Scheme.{u}} (g : Z ⟶ Y.left)
    (hg : finiteEtale g) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (g ≫ Y.hom) (MorphismProperty.comp_mem _ _ _ hg Y.prop)

variable {n : ℕ} {V : Subgroup (EtaleFundamentalGroup X x)}
  {Y : FiniteEtaleOver X} {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}

namespace CharacterTorsorData

variable {χ : V → ZMod n} {hadd : ∀ a b, χ (a * b) = χ a + χ b}
  (D : CharacterTorsorData x χ hadd Y eY)

/-- The translations of the base change of the torsor cover along `g : Z ⟶ Y`. -/
abbrev τZ {Z : Scheme.{u}} (g : Z ⟶ Y.left) (a : ZMod n) :
    pullback D.q.left g ⟶ pullback D.q.left g :=
  baseChangeTranslation D.q.left g (fun a => (D.τ a).left) (translation_left_comp D.q D.τ D.τ_q) a

/-- Each translation of the torsor cover lies over `X`. -/
theorem τ_left_comp_hom (a : ZMod n) : (D.τ a).left ≫ D.T.hom = D.T.hom :=
  MorphismProperty.Over.w (D.τ a)

/-- The base change of the torsor cover to `Z`, as a finite étale cover of `X`. -/
abbrev baseChangeX {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (pullback.snd D.q.left g ≫ g ≫ Y.hom)
    (MorphismProperty.comp_mem _ _ _
      (MorphismProperty.pullback_snd _ _ (finiteEtale_left_of_hom D.q))
      (MorphismProperty.comp_mem _ _ _ hg Y.prop))

/-- The first projection of the base change along `g`, followed by the structure map of the torsor
cover, equals the second projection followed by `g` and the structure map of `Y`. -/
theorem fst_comp_hom {Z : Scheme.{u}} (g : Z ⟶ Y.left) :
    pullback.fst D.q.left g ≫ D.T.hom = pullback.snd D.q.left g ≫ g ≫ Y.hom := by
  rw [← MorphismProperty.Over.w D.q, ← Category.assoc, pullback.condition, Category.assoc]

/-- The projection of the base change to the torsor cover. -/
abbrev baseChangeFst {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g) :
    D.baseChangeX g hg ⟶ D.T :=
  MorphismProperty.Over.homMk (pullback.fst D.q.left g) (D.fst_comp_hom g)

/-- The projection of the base change to `Z`. -/
abbrev baseChangeSnd {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g) :
    D.baseChangeX g hg ⟶ FiniteEtaleOver.overComp g hg :=
  MorphismProperty.Over.homMk (pullback.snd D.q.left g) rfl

/-- The point `(t, e)` of the fibre of the base change. -/
def basePoint {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g)
    (t : (finiteEtaleFiberFunctor x).obj D.T) (e : x.source ⟶ Z)
    (h : t.1 ≫ D.q.left = e ≫ g) : (finiteEtaleFiberFunctor x).obj (D.baseChangeX g hg) :=
  ⟨pullback.lift t.1 e h, by
    change pullback.lift t.1 e h ≫ pullback.snd D.q.left g ≫ g ≫ Y.hom = x.hom
    rw [pullback.lift_snd_assoc, ← reassoc_of% h, MorphismProperty.Over.w D.q]
    exact t.2⟩

/-- A fibre point of the torsor cover lying over the base coset maps under `q` to the point of the
fibre of `Y` corresponding to the base coset. -/
theorem q_basePoint_val (t : (finiteEtaleFiberFunctor x).obj D.T)
    (ht : InducedTorsor.proj (D.eT t) = QuotientGroup.mk 1) :
    t.1 ≫ D.q.left = (eY.symm (QuotientGroup.mk 1)).1 := by
  have : (finiteEtaleFiberFunctor x).map D.q t = eY.symm (QuotientGroup.mk 1) := by
    apply eY.injective
    rw [D.q_apply, ht, Equiv.apply_symm_apply]
  exact congrArg Subtype.val this

/-- The fibre point over the base coset with coordinate `a`. -/
def fiberPoint (a : ZMod n) : (finiteEtaleFiberFunctor x).obj D.T :=
  D.eT.symm (InducedTorsor.mk 1 a)

/-- The fibre point with coordinate `a` maps under `q` to the point of the fibre of `Y`
corresponding to the base coset. -/
theorem fiberPoint_q (a : ZMod n) :
    (D.fiberPoint a).1 ≫ D.q.left = (eY.symm (QuotientGroup.mk 1)).1 :=
  D.q_basePoint_val _ (by rw [fiberPoint, Equiv.apply_symm_apply, InducedTorsor.proj_mk])

/-- The translation by `b` sends the fibre point with coordinate `a` to the one with coordinate
`a + b`. -/
theorem map_τ_fiberPoint (a b : ZMod n) :
    (finiteEtaleFiberFunctor x).map (D.τ b) (D.fiberPoint a) = D.fiberPoint (a + b) := by
  apply D.eT.injective
  rw [D.τ_apply, fiberPoint, fiberPoint, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    InducedTorsor.translate_mk]

/-- The translations of the base change, as endomorphisms of `baseChangeX` over `X`. -/
abbrev τX {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g) (a : ZMod n) :
    D.baseChangeX g hg ⟶ D.baseChangeX g hg :=
  MorphismProperty.Over.homMk (D.τZ g a) (by
    change _ ≫ pullback.snd D.q.left g ≫ g ≫ Y.hom = pullback.snd D.q.left g ≫ g ≫ Y.hom
    rw [baseChangeTranslation_snd_assoc])

/-- The translations of the base change lie over the translations of the torsor cover. -/
theorem τX_comp_baseChangeFst {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g)
    (a : ZMod n) : D.τX g hg a ≫ D.baseChangeFst g hg = D.baseChangeFst g hg ≫ D.τ a := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  exact baseChangeTranslation_fst _ _ _ _ a

/-- The translation by `b` of the base change sends the point `(t_a, e)` to `(t_{a + b}, e)`. -/
theorem map_τX_basePoint {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g)
    (e : x.source ⟶ Z) (he : e ≫ g = (eY.symm (QuotientGroup.mk 1)).1) (a b : ZMod n) :
    D.basePoint g hg (D.fiberPoint (a + b)) e ((D.fiberPoint_q _).trans he.symm) =
      (finiteEtaleFiberFunctor x).map (D.τX g hg b)
        (D.basePoint g hg (D.fiberPoint a) e ((D.fiberPoint_q _).trans he.symm)) := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · show pullback.lift _ _ _ ≫ pullback.fst _ _ =
      (pullback.lift _ _ _ ≫ D.τZ g b) ≫ pullback.fst _ _
    rw [Category.assoc, baseChangeTranslation_fst, pullback.lift_fst, pullback.lift_fst_assoc,
      ← D.map_τ_fiberPoint a b]
    rfl
  · show pullback.lift _ _ _ ≫ pullback.snd _ _ =
      (pullback.lift _ _ _ ≫ D.τZ g b) ≫ pullback.snd _ _
    rw [Category.assoc, baseChangeTranslation_snd, pullback.lift_snd, pullback.lift_snd]

/-- An element `v ∈ V` moves the fibre point with coordinate `0` to the one with coordinate
`χ v`. -/
theorem fiberPoint_smul (v : V) :
    D.fiberPoint (χ v) = (v : EtaleFundamentalGroup X x) • D.fiberPoint 0 := by
  apply D.eT.injective
  rw [D.eT_smul, fiberPoint, fiberPoint, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    InducedTorsor.smul_mk_one, zero_add]

end CharacterTorsorData

/-- A point of `Z` over the base coset, as a point of the fibre of `Z` at `x`. -/
def exPoint {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g) (e : x.source ⟶ Z)
    (he : e ≫ g = (eY.symm (QuotientGroup.mk 1)).1) :
    (finiteEtaleFiberFunctor x).obj (FiniteEtaleOver.overComp g hg) :=
  ⟨e, by
    change e ≫ g ≫ Y.hom = x.hom
    rw [reassoc_of% he]
    exact (eY.symm (QuotientGroup.mk 1)).2⟩

namespace CharacterTorsorData

variable {χ : V → ZMod n} {hadd : ∀ a b, χ (a * b) = χ a + χ b}
  (D : CharacterTorsorData x χ hadd Y eY)

/-- If `v ∈ V` fixes `e`, it moves the point `(t_0, e)` of the base change to `(t_{χ v}, e)`. -/
theorem basePoint_fiberPoint_smul {Z : Scheme.{u}} (g : Z ⟶ Y.left) (hg : finiteEtale g)
    (e : x.source ⟶ Z) (he : e ≫ g = (eY.symm (QuotientGroup.mk 1)).1) (v : V)
    (hv : (v : EtaleFundamentalGroup X x) • exPoint g hg e he = exPoint g hg e he) :
    D.basePoint g hg (D.fiberPoint (χ v)) e ((D.fiberPoint_q _).trans he.symm) =
      (v : EtaleFundamentalGroup X x) •
        D.basePoint g hg (D.fiberPoint 0) e ((D.fiberPoint_q _).trans he.symm) := by
  set w := D.basePoint g hg (D.fiberPoint 0) e ((D.fiberPoint_q _).trans he.symm)
  have h1 : (finiteEtaleFiberFunctor x).map (D.baseChangeFst g hg)
      ((v : EtaleFundamentalGroup X x) • w) = D.fiberPoint (χ v) := by
    rw [finiteEtaleFiberFunctor_map_smul, D.fiberPoint_smul v]
    exact congrArg _ (Subtype.ext (pullback.lift_fst _ _ _))
  have h2 : (finiteEtaleFiberFunctor x).map (D.baseChangeSnd g hg)
      ((v : EtaleFundamentalGroup X x) • w) = exPoint g hg e he := by
    rw [finiteEtaleFiberFunctor_map_smul]
    exact (congrArg _ (Subtype.ext (pullback.lift_snd _ _ _))).trans hv
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · exact (pullback.lift_fst _ _ _).trans (congrArg Subtype.val h1).symm
  · exact (pullback.lift_snd _ _ _).trans (congrArg Subtype.val h2).symm

end CharacterTorsorData

open CharacterTorsorData

variable {χ₁ χ₂ : V → ZMod n} {hadd₁ : ∀ a b, χ₁ (a * b) = χ₁ a + χ₁ b}
  {hadd₂ : ∀ a b, χ₂ (a * b) = χ₂ a + χ₂ b}

/-- **Rigidity of character torsors.** If `ψ : T₁ ×_Y Z ⟶ T₂ ×_Y Z` is a morphism over `Z`
commuting with the translations, `g : Z ⟶ Y` is finite étale and `e` is a point of the fibre of
`Z` over the base coset fixed by `v ∈ V`, then `χ₁ v = χ₂ v`. -/
theorem CharacterTorsorData.eq_of_hom_baseChange (D₁ : CharacterTorsorData x χ₁ hadd₁ Y eY)
    (D₂ : CharacterTorsorData x χ₂ hadd₂ Y eY) {Z : Scheme.{u}} (g : Z ⟶ Y.left)
    (hg : finiteEtale g) (ψ : pullback D₁.q.left g ⟶ pullback D₂.q.left g)
    (hΨsnd : ψ ≫ pullback.snd D₂.q.left g = pullback.snd D₁.q.left g)
    (hψ : ∀ a, D₁.τZ g a ≫ ψ = ψ ≫ D₂.τZ g a)
    (e : x.source ⟶ Z) (he : e ≫ g = (eY.symm (QuotientGroup.mk 1)).1) (v : V)
    (hv : (v : EtaleFundamentalGroup X x) • exPoint g hg e he = exPoint g hg e he) :
    χ₁ v = χ₂ v := by
  let Ψ : D₁.baseChangeX g hg ⟶ D₂.baseChangeX g hg :=
    MorphismProperty.Over.homMk ψ (by
      show ψ ≫ pullback.snd D₂.q.left g ≫ g ≫ Y.hom = pullback.snd D₁.q.left g ≫ g ≫ Y.hom
      rw [reassoc_of% hΨsnd])
  have hΨτ : ∀ a, D₁.τX g hg a ≫ Ψ = Ψ ≫ D₂.τX g hg a := fun a => by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    exact hψ a
  -- the comparison map on the base fibre
  let Φ : ZMod n → InducedTorsor V χ₂ hadd₂ := fun a =>
    D₂.eT ((finiteEtaleFiberFunctor x).map (Ψ ≫ D₂.baseChangeFst g hg)
      (D₁.basePoint g hg (D₁.fiberPoint a) e ((D₁.fiberPoint_q _).trans he.symm)))
  refine eq_of_inducedTorsor_fiber Φ (fun a b => ?_) ?_ v ?_
  · have hmor : D₁.τX g hg b ≫ Ψ ≫ D₂.baseChangeFst g hg =
        (Ψ ≫ D₂.baseChangeFst g hg) ≫ D₂.τ b := by
      rw [← Category.assoc, hΨτ, Category.assoc, D₂.τX_comp_baseChangeFst, Category.assoc]
    show D₂.eT _ = _
    rw [D₁.map_τX_basePoint g hg e he a b, ← Functor.map_comp_apply, hmor,
      Functor.map_comp_apply, D₂.τ_apply]
  · show InducedTorsor.proj (D₂.eT _) = _
    rw [← D₂.q_apply]
    have : (finiteEtaleFiberFunctor x).map D₂.q ((finiteEtaleFiberFunctor x).map
        (Ψ ≫ D₂.baseChangeFst g hg)
          (D₁.basePoint g hg (D₁.fiberPoint 0) e ((D₁.fiberPoint_q _).trans he.symm))) =
        eY.symm (QuotientGroup.mk 1) := by
      refine Subtype.ext ?_
      show ((pullback.lift _ _ _ ≫ ψ) ≫ pullback.fst _ _) ≫ D₂.q.left = _
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hΨsnd,
        pullback.lift_snd_assoc, he]
    rw [this, Equiv.apply_symm_apply]
  · show D₂.eT _ = _
    rw [D₁.basePoint_fiberPoint_smul g hg e he v hv, finiteEtaleFiberFunctor_map_smul,
      D₂.eT_smul]

end AlgebraicGeometry
