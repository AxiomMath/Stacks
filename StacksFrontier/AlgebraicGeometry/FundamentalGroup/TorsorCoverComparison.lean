module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.InducedCharacterCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.SchemeTorsorRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField

/-!
# A torsor of finite étale covers is a torsor scheme

Let `q : T ⟶ Y` be a morphism of finite étale covers of a connected scheme `X` and let
`τ : ℤ/n → End(T)` be translations over `Y`. If on the geometric fibre at a point `x` the
translations act freely and transitively on the fibres of `q`, then `T` is a `ℤ/n`-torsor over `Y`
in the scheme sense: `∐_a T ⟶ T ×_Y T`, `(t, a) ↦ (t, τ_a t)`, is an isomorphism of schemes. The
comparison is a morphism of finite étale covers of `X`, so this is checked on the fibre at `x`,
where a lift of the geometric point to `∐_a T` lies in one component.

## Main definitions

* `AlgebraicGeometry.CharacterTorsorData`: the torsor cover of a character `χ : V → ℤ/n` of an
  open subgroup `V`, over a cover with fibre `π₁ ⧸ V`.

## Main results

* `AlgebraicGeometry.isIso_torsorComparison_of_fiber`: the scheme-torsor isomorphism.
* `AlgebraicGeometry.nonempty_characterTorsorData`: the torsor cover of a continuous character
  exists.
* `AlgebraicGeometry.CharacterTorsorData.isIso_torsorComparison`: the torsor cover of a character
  is a `ℤ/n`-torsor scheme over the cover with fibre `π₁ ⧸ V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Kummer

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X) {n : ℕ}

omit [ConnectedSpace X] in
/-- The underlying morphism of schemes of a morphism of finite étale covers is finite étale. -/
theorem finiteEtale_left_of_hom {Y T : FiniteEtaleOver X} (q : T ⟶ Y) : finiteEtale q.left :=
  MorphismProperty.of_postcomp finiteEtale (W' := finiteEtale) q.left Y.hom Y.prop
    (by rw [MorphismProperty.Over.w q]; exact T.prop)

omit [ConnectedSpace X] in
/-- If each `τ a` commutes with `q` over `Y`, then so do the underlying morphisms of schemes. -/
theorem translation_left_comp {Y T : FiniteEtaleOver X} (q : T ⟶ Y) (τ : ZMod n → (T ⟶ T))
    (hτq : ∀ a, τ a ≫ q = q) (a : ZMod n) : (τ a).left ≫ q.left = q.left := by
  rw [← MorphismProperty.Comma.comp_left, hτq]

omit [ConnectedSpace X] in
/-- A lift of a geometric point to a coproduct lies in one component. -/
theorem exists_eq_comp_sigmaι {ι : Type} [Finite ι] (Z : ι → Scheme.{u})
    (f : x.source ⟶ ∐ Z) : ∃ (a : ι) (t : x.source ⟶ Z a), t ≫ Sigma.ι Z a = f := by
  obtain ⟨a, y, hy⟩ := (sigmaOpenCover Z).exists_eq (f (default : x.source))
  have H : Set.range f ⊆ Set.range (Sigma.ι Z a) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact ⟨y, hy⟩
  exact ⟨a, IsOpenImmersion.lift _ _ H, IsOpenImmersion.lift_fac _ _ _⟩

variable [NeZero n]

omit [ConnectedSpace X] in
/-- On lifts of a geometric point, the torsor comparison is injective when the translations act
freely on the fibre. -/
theorem eq_of_comp_torsorComparison_eq {Y T : FiniteEtaleOver X} (q : T ⟶ Y)
    (τ : ZMod n → (T ⟶ T)) (hτq : ∀ a, τ a ≫ q = q)
    (hfree : ∀ (t : (finiteEtaleFiberFunctor x).obj T) (a b : ZMod n),
      (finiteEtaleFiberFunctor x).map (τ a) t = (finiteEtaleFiberFunctor x).map (τ b) t → a = b)
    {g g' : x.source ⟶ ∐ fun _ : ZMod n => T.left}
    (hg : g ≫ Sigma.desc (fun _ : ZMod n => T.hom) = x.hom)
    (h : g ≫ torsorComparison (fun a => (τ a).left) (translation_left_comp q τ hτq) =
      g' ≫ torsorComparison (fun a => (τ a).left) (translation_left_comp q τ hτq)) : g = g' := by
  obtain ⟨a, t₀, rfl⟩ := exists_eq_comp_sigmaι x (fun _ : ZMod n => T.left) g
  obtain ⟨b, t₀', rfl⟩ := exists_eq_comp_sigmaι x (fun _ : ZMod n => T.left) g'
  simp only [Category.assoc, ι_torsorComparison] at h
  have e₁ := congrArg (· ≫ pullback.fst q.left q.left) h
  have e := congrArg (· ≫ pullback.snd q.left q.left) h
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at e₁ e
  subst e₁
  have ht : t₀ ≫ T.hom = x.hom := by simpa only [Category.assoc, Sigma.ι_comp_desc] using hg
  obtain rfl : a = b := hfree ⟨t₀, ht⟩ a b (Subtype.ext e)
  rfl

omit [ConnectedSpace X] [NeZero n] in
/-- When the translations act transitively on the fibres of `q`, every lift of a geometric point
to `T ×_Y T` is the image under the torsor comparison of a lift to `∐_a T`. -/
theorem exists_comp_torsorComparison_eq {Y T : FiniteEtaleOver X} (q : T ⟶ Y)
    (τ : ZMod n → (T ⟶ T)) (hτq : ∀ a, τ a ≫ q = q)
    (htrans : ∀ t t' : (finiteEtaleFiberFunctor x).obj T,
      (finiteEtaleFiberFunctor x).map q t = (finiteEtaleFiberFunctor x).map q t' →
        ∃ a, (finiteEtaleFiberFunctor x).map (τ a) t = t')
    (g : x.source ⟶ pullback q.left q.left) (hg : g ≫ pullback.fst q.left q.left ≫ T.hom = x.hom) :
    ∃ r : x.source ⟶ ∐ fun _ : ZMod n => T.left,
      r ≫ Sigma.desc (fun _ : ZMod n => T.hom) = x.hom ∧
        r ≫ torsorComparison (fun a => (τ a).left) (translation_left_comp q τ hτq) = g := by
  have h₂ : (g ≫ pullback.snd q.left q.left) ≫ T.hom = x.hom := by
    rw [Category.assoc, ← MorphismProperty.Over.w q, ← Category.assoc
      (pullback.snd _ _), ← pullback.condition, Category.assoc, MorphismProperty.Over.w q]
    exact hg
  obtain ⟨a, ha⟩ := htrans ⟨g ≫ pullback.fst q.left q.left, (Category.assoc _ _ _).trans hg⟩
    ⟨g ≫ pullback.snd q.left q.left, h₂⟩ (Subtype.ext (by
      change (g ≫ pullback.fst q.left q.left) ≫ q.left =
        (g ≫ pullback.snd q.left q.left) ≫ q.left
      rw [Category.assoc, Category.assoc, pullback.condition]))
  refine ⟨g ≫ pullback.fst q.left q.left ≫ Sigma.ι (fun _ : ZMod n => T.left) a, ?_, ?_⟩
  · simpa only [Category.assoc, Sigma.ι_comp_desc] using hg
  · simp only [Category.assoc, ι_torsorComparison]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc]
      exact congrArg Subtype.val ha

/-- **A torsor of finite étale covers is a torsor scheme.** -/
theorem isIso_torsorComparison_of_fiber {Y T : FiniteEtaleOver X} (q : T ⟶ Y)
    (τ : ZMod n → (T ⟶ T)) (hτq : ∀ a, τ a ≫ q = q)
    (hfree : ∀ (t : (finiteEtaleFiberFunctor x).obj T) (a b : ZMod n),
      (finiteEtaleFiberFunctor x).map (τ a) t = (finiteEtaleFiberFunctor x).map (τ b) t → a = b)
    (htrans : ∀ t t' : (finiteEtaleFiberFunctor x).obj T,
      (finiteEtaleFiberFunctor x).map q t = (finiteEtaleFiberFunctor x).map q t' →
        ∃ a, (finiteEtaleFiberFunctor x).map (τ a) t = t') :
    IsIso (torsorComparison (fun a => (τ a).left) (translation_left_comp q τ hτq)) := by
  set Ψ := torsorComparison (fun a => (τ a).left) (translation_left_comp q τ hτq)
  have hq := finiteEtale_left_of_hom q
  let A : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : ZMod n => T.hom)
    (Stacks.FundamentalGroup.finiteEtale_sigmaDesc fun _ => T.prop)
  let B : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ (pullback.fst q.left q.left ≫ T.hom)
    (MorphismProperty.comp_mem _ _ _ (MorphismProperty.pullback_fst _ _ hq) T.prop)
  have hw : Ψ ≫ B.hom = A.hom := by
    refine Sigma.hom_ext _ _ fun a => ?_
    change Sigma.ι (fun _ : ZMod n => T.left) a ≫ Ψ ≫ pullback.fst q.left q.left ≫ T.hom =
      Sigma.ι (fun _ : ZMod n => T.left) a ≫ Sigma.desc _
    rw [Sigma.ι_comp_desc, ← Category.assoc, ι_torsorComparison, pullback.lift_fst_assoc,
      Category.id_comp]
  let Φ : A ⟶ B := MorphismProperty.Over.homMk Ψ hw
  have : IsIso Φ := by
    have := reflectsIsomorphisms_finiteEtaleFiberFunctor x
    suffices hb : Function.Bijective ((finiteEtaleFiberFunctor x).map Φ) by
      have : IsIso ((finiteEtaleFiberFunctor x).map Φ) := (isIso_iff_bijective _).2 hb
      exact isIso_of_reflects_iso Φ (finiteEtaleFiberFunctor x)
    refine ⟨fun f f' h => Subtype.ext (eq_of_comp_torsorComparison_eq x q τ hτq hfree
      (g := f.1) (g' := f'.1) f.2 (congrArg Subtype.val h)), fun f => ?_⟩
    obtain ⟨r, hr, e⟩ := exists_comp_torsorComparison_eq x q τ hτq htrans f.1 f.2
    exact ⟨⟨r, hr⟩, Subtype.ext e⟩
  refine ⟨(inv Φ).left, ?_, ?_⟩
  · change Φ.left ≫ (inv Φ).left = 𝟙 A.left
    rw [← MorphismProperty.Comma.comp_left, IsIso.hom_inv_id]
    rfl
  · change (inv Φ).left ≫ Φ.left = 𝟙 B.left
    rw [← MorphismProperty.Comma.comp_left, IsIso.inv_hom_id]
    rfl

section CharacterTorsor

open Stacks.LAdic

variable {V : Subgroup (EtaleFundamentalGroup X x)}
  (hV : IsOpen (V : Set (EtaleFundamentalGroup X x)))
  (χ : V → ZMod n) (hadd : ∀ a b, χ (a * b) = χ a + χ b) (hχc : IsLocallyConstant χ)

/-- **The torsor cover of a character of an open subgroup**, over a fixed cover `Y` with fibre
`π₁ ⧸ V`: the cover `T` with fibre the induced torsor, the projection `q : T ⟶ Y` and the
translations `τ_a`, compatibly with the identifications of the fibres at `x`. -/
structure CharacterTorsorData (Y : FiniteEtaleOver X)
    (eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V) where
  /-- The cover with fibre the induced torsor. -/
  T : FiniteEtaleOver X
  /-- The fibre of `T`. -/
  eT : (finiteEtaleFiberFunctor x).obj T ≃ InducedTorsor V χ hadd
  eT_smul : ∀ (σ : EtaleFundamentalGroup X x) t, eT (σ • t) = σ • eT t
  /-- The projection. -/
  q : T ⟶ Y
  /-- The translations. -/
  τ : ZMod n → (T ⟶ T)
  q_apply : ∀ t, eY ((finiteEtaleFiberFunctor x).map q t) = InducedTorsor.proj (eT t)
  τ_apply : ∀ a t, eT ((finiteEtaleFiberFunctor x).map (τ a) t) = InducedTorsor.translate a (eT t)

variable {x χ hadd}

include hV in
omit [NeZero n] in
/-- For an open subgroup `V`, there is a finite étale cover of `X` whose fibre at `x` is
`π₁ ⧸ V`, equivariantly. -/
theorem exists_quotientCover :
    ∃ (Y : FiniteEtaleOver X)
      (e : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V),
      ∀ (σ : EtaleFundamentalGroup X x) y, e (σ • y) = σ • e y := by
  have : Finite (EtaleFundamentalGroup X x ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  exact exists_finiteEtaleOver_fiber_equiv x _ (isOpen_stabilizer_quotient x V hV)

include hV hχc in
/-- A locally constant character `χ` of an open subgroup `V` has a torsor cover over every cover
whose fibre at `x` is equivariantly `π₁ ⧸ V`. -/
theorem nonempty_characterTorsorData (Y : FiniteEtaleOver X)
    (eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V)
    (heY : ∀ (σ : EtaleFundamentalGroup X x) y, eY (σ • y) = σ • eY y) :
    Nonempty (CharacterTorsorData x χ hadd Y eY) := by
  obtain ⟨T, eT, heT⟩ := exists_inducedCharacterCover x χ hadd hV hχc
  obtain ⟨q, hq⟩ := exists_hom_of_equivariant x (fun t => eY.symm (InducedTorsor.proj (eT t)))
    (fun σ t => by
      apply eY.injective
      rw [Equiv.apply_symm_apply, heY, Equiv.apply_symm_apply, heT, InducedTorsor.proj_smul])
  choose τ hτ using fun a : ZMod n => exists_hom_of_equivariant x
    (fun t => eT.symm (InducedTorsor.translate a (eT t))) (fun σ t => by
      apply eT.injective
      rw [Equiv.apply_symm_apply, heT, heT, Equiv.apply_symm_apply, InducedTorsor.translate_smul])
  exact ⟨⟨T, eT, heT, q, τ, fun t => by rw [hq, Equiv.apply_symm_apply],
    fun a t => by rw [hτ, Equiv.apply_symm_apply]⟩⟩

namespace CharacterTorsorData

variable {Y : FiniteEtaleOver X}
  {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}
  (D : CharacterTorsorData x χ hadd Y eY)

omit [NeZero n] in
/-- The translation by `0` is the identity. -/
theorem τ_zero : D.τ 0 = 𝟙 D.T := by
  refine finiteEtaleFiberFunctor_map_injective x fun t => D.eT.injective ?_
  rw [D.τ_apply, InducedTorsor.translate_zero, CategoryTheory.Functor.map_id]
  rfl

omit [NeZero n] in
/-- The translation by `a + b` is the translation by `a` followed by the translation by `b`. -/
theorem τ_add (a b : ZMod n) : D.τ (a + b) = D.τ a ≫ D.τ b := by
  refine finiteEtaleFiberFunctor_map_injective x fun t => D.eT.injective ?_
  rw [D.τ_apply, InducedTorsor.translate_add, CategoryTheory.Functor.map_comp]
  change _ = D.eT ((finiteEtaleFiberFunctor x).map (D.τ b)
    ((finiteEtaleFiberFunctor x).map (D.τ a) t))
  rw [D.τ_apply, D.τ_apply]

omit [NeZero n] in
/-- The translations are morphisms over `Y`. -/
theorem τ_q (a : ZMod n) : D.τ a ≫ D.q = D.q := by
  refine finiteEtaleFiberFunctor_map_injective x fun t => eY.injective ?_
  rw [CategoryTheory.Functor.map_comp]
  change eY ((finiteEtaleFiberFunctor x).map D.q ((finiteEtaleFiberFunctor x).map (D.τ a) t)) = _
  rw [D.q_apply, D.q_apply, D.τ_apply, InducedTorsor.proj_translate]

/-- The torsor cover `T` of a character is a `ℤ/n`-torsor scheme over `Y`: the map
`∐_a T ⟶ T ×_Y T`, `(t, a) ↦ (t, τ_a t)`, is an isomorphism. -/
theorem isIso_torsorComparison :
    IsIso (torsorComparison (fun a => (D.τ a).left) (translation_left_comp D.q D.τ D.τ_q)) :=
  isIso_torsorComparison_of_fiber x D.q D.τ D.τ_q
    (fun t a b h => InducedTorsor.eq_of_translate_eq a b (D.eT t) (by
      rw [← D.τ_apply, ← D.τ_apply, h]))
    (fun t t' h => by
      obtain ⟨a, ha⟩ := InducedTorsor.exists_translate_eq (D.eT t) (D.eT t') (by
        rw [← D.q_apply, ← D.q_apply, h])
      exact ⟨a, D.eT.injective (by rw [D.τ_apply, ha])⟩)

omit [NeZero n] in
/-- Over a connected `Y`, the projection `q : T ⟶ Y` is surjective. -/
theorem surjective_q [ConnectedSpace Y.left] : Function.Surjective D.q.left := by
  let W : FiniteEtaleOver Y.left :=
    MorphismProperty.Over.mk ⊤ D.q.left (finiteEtale_left_of_hom D.q)
  have : Nonempty W.left := ⟨(D.eT.symm (InducedTorsor.mk 1 0)).1 default⟩
  exact surjective_of_finiteEtale W

end CharacterTorsorData

omit [NeZero n] in
/-- The cover with fibre `π₁ ⧸ V` is connected. -/
theorem connectedSpace_of_quotient_equiv (Y : FiniteEtaleOver X)
    (eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V)
    (heY : ∀ (σ : EtaleFundamentalGroup X x) y, eY (σ • y) = σ • eY y) :
    ConnectedSpace Y.left :=
  connectedSpace_left_of_isPretransitive x Y (eY.symm (QuotientGroup.mk 1)) fun y => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (eY y)
    refine ⟨g, eY.injective ?_⟩
    rw [heY, Equiv.apply_symm_apply, ← hg]
    exact congrArg QuotientGroup.mk (mul_one g)

end CharacterTorsor

end AlgebraicGeometry
