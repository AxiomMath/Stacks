module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Objects
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.Affine
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Tangent vectors act on infinitesimal lifts

Fix an affine first-order thickening `T = Spec (A' ⧸ C) ⊂ T' = Spec A'` over `S`, a morphism
`f : X ⟶ Y` of algebraic spaces and a lifting problem `x ∈ X(T)`, `y ∈ Y(T')` with
`f x = y|_T`.  For an `A'`-algebra `R` this file defines

* `Lifts R`: the solutions of the lifting problem over `Spec R`, that is the sections of `X`
  over `Spec R` restricting to `x` over `Spec (R ⧸ CR)` and lying over `y`;
* `Tangents R`: the sections of `X` over the trivial square-zero extension
  `Spec (R ⧸ CR ⊕ CR)` restricting to `x` along the zero section and lying over `y`;
* `act R : Tangents R → Lifts R → Lifts R`, the action of tangent vectors on lifts.

The action is built from Stacks 07SY: `Spec (E ×_Q R)` is a pushout of `Spec R` and
`Spec E` along `Spec Q` not only in schemes (Stacks 0ET0) but in algebraic spaces, so a lift and
a tangent vector glue to a section of `X` over it, which is pulled back along the ring map
`σ : ((q, m), r) ↦ r + m`.  Everything is defined by precomposition, so the action is natural
in `R` with no further argument; this is what replaces the chart-by-chart action of
[Stacks Project, Tag 061C] in the proof of [Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Elementwise pushouts -/

/-- The algebraic space represented by an object of the site. -/
noncomputable abbrev rep (T : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩

section Glue

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {T₀ T₁ T₂ T₃ : BigFppfOver B S hS} {i : T₀ ⟶ T₁} {j : T₀ ⟶ T₂} {a : T₁ ⟶ T₃} {b : T₂ ⟶ T₃}
  (hP : IsPushout (ObjectProperty.homMk (yoneda.map i) : rep T₀ ⟶ rep T₁)
    (ObjectProperty.homMk (yoneda.map j) : rep T₀ ⟶ rep T₂)
    (ObjectProperty.homMk (yoneda.map a) : rep T₁ ⟶ rep T₃)
    (ObjectProperty.homMk (yoneda.map b) : rep T₂ ⟶ rep T₃))

/-- A section of `X`, as a morphism of algebraic spaces out of the represented space. -/
noncomputable abbrev toSp {T : BigFppfOver B S hS} (z : X.obj (op T)) :
    rep T ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (yonedaEquiv.symm z)

/-- **Glueing two sections along a pushout square of representables.** -/
noncomputable def glue (z₁ : X.obj (op T₁)) (z₂ : X.obj (op T₂))
    (h : X.map i.op z₁ = X.map j.op z₂) : X.obj (op T₃) :=
  yonedaEquiv (hP.desc (toSp hX z₁) (toSp hX z₂) (by
    apply ObjectProperty.hom_ext
    change yoneda.map i ≫ yonedaEquiv.symm z₁ = yoneda.map j ≫ yonedaEquiv.symm z₂
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, h])).hom

/-- Sections agreeing after restriction along `g` and `g'` agree after composing with the
corresponding maps of represented spaces. -/
private theorem homMk_comp_toSp_eq {U V V' : BigFppfOver B S hS} {g : U ⟶ V} {g' : U ⟶ V'}
    (z : X.obj (op V)) (z' : X.obj (op V')) (h : X.map g.op z = X.map g'.op z') :
    (ObjectProperty.homMk (yoneda.map g) : rep U ⟶ rep V) ≫ toSp hX z =
      (ObjectProperty.homMk (yoneda.map g') : rep U ⟶ rep V') ≫ toSp hX z' := by
  apply ObjectProperty.hom_ext
  change yoneda.map g ≫ yonedaEquiv.symm z = yoneda.map g' ≫ yonedaEquiv.symm z'
  rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, h]

/-- The glued section restricts to the first section along `a`. -/
theorem map_glue_left (z₁ : X.obj (op T₁)) (z₂ : X.obj (op T₂))
    (h : X.map i.op z₁ = X.map j.op z₂) : X.map a.op (glue hX hP z₁ z₂ h) = z₁ := by
  rw [glue, yonedaEquiv_naturality]
  have := congrArg (fun g => g.hom) (hP.inl_desc _ _ (homMk_comp_toSp_eq hX z₁ z₂ h))
  change yoneda.map a ≫ _ = yonedaEquiv.symm z₁ at this
  rw [this, Equiv.apply_symm_apply]

/-- The glued section restricts to the second section along `b`. -/
theorem map_glue_right (z₁ : X.obj (op T₁)) (z₂ : X.obj (op T₂))
    (h : X.map i.op z₁ = X.map j.op z₂) : X.map b.op (glue hX hP z₁ z₂ h) = z₂ := by
  rw [glue, yonedaEquiv_naturality]
  have := congrArg (fun g => g.hom) (hP.inr_desc _ _ (homMk_comp_toSp_eq hX z₁ z₂ h))
  change yoneda.map b ≫ _ = yonedaEquiv.symm z₂ at this
  rw [this, Equiv.apply_symm_apply]

include hX hP in
/-- **Uniqueness of the glued section.** -/
theorem eq_of_map_eq_map (w w' : X.obj (op T₃)) (h₁ : X.map a.op w = X.map a.op w')
    (h₂ : X.map b.op w = X.map b.op w') : w = w' := by
  have : toSp hX w = toSp hX w' :=
    hP.hom_ext (homMk_comp_toSp_eq hX w w' h₁) (homMk_comp_toSp_eq hX w w' h₂)
  have h' := congrArg (fun g => yonedaEquiv g.hom) this
  simpa using h'

/-- A section restricting to `z₁` along `a` and to `z₂` along `b` is the glued section. -/
theorem eq_glue (w : X.obj (op T₃)) (z₁ : X.obj (op T₁)) (z₂ : X.obj (op T₂))
    (h : X.map i.op z₁ = X.map j.op z₂) (h₁ : X.map a.op w = z₁) (h₂ : X.map b.op w = z₂) :
    w = glue hX hP z₁ z₂ h :=
  eq_of_map_eq_map hX hP _ _ (by rw [h₁, map_glue_left]) (by rw [h₂, map_glue_right])

end Glue

/-! ### The pushout square of a tangent thickening -/

variable {D : Base B S hS}

/-- The closed immersion `Spec (R ⧸ CR) ⟶ Spec R` is a thickening. -/
theorem isThickening_incl (R : Alg D) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map (incl R)) := by
  refine (Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) Ideal.Quotient.mk_surjective ?_
    ).isThickening
  change RingHom.ker (Ideal.Quotient.mk (sqIdeal D.C R.R)) ^ 2 = ⊥
  rw [Ideal.mk_ker, pow_two, sqIdeal_mul_self]

/-- `Spec (E ×_Q R)` is the pushout of `Spec R` and `Spec E` along `Spec Q` in schemes. -/
theorem isPushout_scheme (R : Alg D) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (incl R))
      ((BigFppfOver.toScheme B S hS).map (zeroSec R))
      ((BigFppfOver.toScheme B S hS).map (pInl R))
      ((BigFppfOver.toScheme B S hS).map (pInr R)) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (Stacks.Pushout.isPullback_ofHom_pullback (fstE D.C R.R)
      (Ideal.Quotient.mk (sqIdeal D.C R.R))) Ideal.Quotient.mk_surjective

/-- **The tangent pushout square, in algebraic spaces** (Stacks 07SY). -/
theorem isPushout_rep (R : Alg D) :
    IsPushout (ObjectProperty.homMk (yoneda.map (incl R)) : rep (O₀ R) ⟶ rep (O R))
      (ObjectProperty.homMk (yoneda.map (zeroSec R)) : rep (O₀ R) ⟶ rep (Oₑ R))
      (ObjectProperty.homMk (yoneda.map (pInl R)) : rep (O R) ⟶ rep (Oₚ R))
      (ObjectProperty.homMk (yoneda.map (pInr R)) : rep (Oₑ R) ⟶ rep (Oₚ R)) :=
  have : IsAffineHom ((BigFppfOver.toScheme B S hS).map (zeroSec R)) := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (fstE D.C R.R))); infer_instance
  isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS _ _ _ _
    (isThickening_incl R) (isPushout_scheme R)

/-! ### The lifting problem -/

/-- Restricting a section along `h` and then along `g` is restricting it along `g ≫ h`. -/
theorem map_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V W : BigFppfOver B S hS}
    (g : W ⟶ U) (h : U ⟶ V) (v : F.obj (op V)) :
    F.map g.op (F.map h.op v) = F.map (g ≫ h).op v := by
  rw [op_comp, Functor.map_comp_apply]

variable (D) in
/-- The base algebra `A'` itself. -/
noncomputable abbrev baseAlg : Alg D := ⟨D.A, D.size⟩

/-- The structure map of an algebra, as an algebra map from the base. -/
noncomputable abbrev toBase (R : Alg D) : (baseAlg D).R →ₐ[D.A] R.R := Algebra.ofId D.A R.R

/-- An algebra map composed with the structure map of its source is the structure map of
its target. -/
theorem comp_toBase {R R' : Alg D} (h : R.R →ₐ[D.A] R'.R) : h.comp (toBase R) = toBase R' :=
  AlgHom.ext fun a => h.commutes a

variable (D) in
/-- **A lifting problem** for `f : X ⟶ Y` along the thickening `Spec (A' ⧸ C) ⊂ Spec A'`. -/
structure Problem where
  /-- The source. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The source is an algebraic space. -/
  hX : IsAlgebraicSpace B S hS X
  /-- The target is an algebraic space. -/
  hY : IsAlgebraicSpace B S hS Y
  /-- The morphism. -/
  f : X ⟶ Y
  /-- The given section over the closed subscheme. -/
  x : X.obj (op (O₀ (baseAlg D)))
  /-- The given section of the target over the thickening. -/
  y : Y.obj (op (O (baseAlg D)))
  /-- The compatibility `f x = y|_T`. -/
  hxy : f.app _ x = Y.map (incl (baseAlg D)).op y

variable (𝔓 : Problem D)

/-- The restriction of `x` to `Spec (R ⧸ CR)`. -/
noncomputable abbrev Problem.xR (R : Alg D) : 𝔓.X.obj (op (O₀ R)) := 𝔓.X.map (mO₀ (toBase R)).op 𝔓.x

/-- The restriction of `y` to `Spec R`. -/
noncomputable abbrev Problem.yR (R : Alg D) : 𝔓.Y.obj (op (O R)) := 𝔓.Y.map (mO (toBase R)).op 𝔓.y

/-- The restrictions of `x` and `y` over `R` are compatible: `f (x|_R) = (y|_R)|_{R ⧸ CR}`. -/
theorem Problem.f_xR (R : Alg D) : 𝔓.f.app _ (𝔓.xR R) = 𝔓.Y.map (incl R).op (𝔓.yR R) := by
  rw [Problem.xR, NatTrans.naturality_apply, 𝔓.hxy, Problem.yR, map_map, map_map, incl_mO]

/-- **The lifts over `Spec R`.** -/
def Problem.Lifts (R : Alg D) : Type u :=
  {z : 𝔓.X.obj (op (O R)) // 𝔓.X.map (incl R).op z = 𝔓.xR R ∧ 𝔓.f.app _ z = 𝔓.yR R}

/-- **The tangent vectors over `Spec R`.** -/
def Problem.Tangents (R : Alg D) : Type u :=
  {t : 𝔓.X.obj (op (Oₑ R)) // 𝔓.X.map (zeroSec R).op t = 𝔓.xR R ∧
    𝔓.f.app _ t = 𝔓.Y.map (retr R ≫ incl R).op (𝔓.yR R)}

variable {𝔓}

/-- The glued section over the pushout `Spec (E ×_Q R)`. -/
noncomputable def glueLT {R : Alg D} (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    𝔓.X.obj (op (Oₚ R)) :=
  glue 𝔓.hX (isPushout_rep R) z.1 t.1 (z.2.1.trans t.2.1.symm)

/-- The image under `f` of the glued section is `y|_R` pulled back along the projection. -/
theorem f_glueLT {R : Alg D} (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    𝔓.f.app _ (glueLT t z) = 𝔓.Y.map (pProj R).op (𝔓.yR R) := by
  refine eq_of_map_eq_map 𝔓.hY (isPushout_rep R) _ _ ?_ ?_
  · rw [← NatTrans.naturality_apply, glueLT, map_glue_left, z.2.2, map_map, pInl_pProj]
    exact (Functor.map_id_apply 𝔓.Y _ _).symm
  · rw [← NatTrans.naturality_apply, glueLT, map_glue_right, t.2.2, map_map (pInr R),
      pInr_pProj]

/-- The section obtained by acting restricts to `x` over `Spec (R ⧸ CR)`. -/
theorem incl_act_eq {R : Alg D} (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    𝔓.X.map (incl R).op (𝔓.X.map (actHom R).op (glueLT t z)) = 𝔓.xR R := by
  rw [map_map, incl_actHom, ← map_map, glueLT, map_glue_left]
  exact z.2.1

/-- The section obtained by acting lies over `y|_R`. -/
theorem f_act_eq {R : Alg D} (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    𝔓.f.app _ (𝔓.X.map (actHom R).op (glueLT t z)) = 𝔓.yR R := by
  rw [NatTrans.naturality_apply, f_glueLT, map_map, actHom_pProj]
  exact Functor.map_id_apply 𝔓.Y _ _

/-- **The action of a tangent vector on a lift.** -/
noncomputable def act {R : Alg D} (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) : 𝔓.Lifts R :=
  ⟨𝔓.X.map (actHom R).op (glueLT t z), incl_act_eq t z, f_act_eq t z⟩

/-! ### Pullback along algebra maps -/

variable {R R' : Alg D}

/-- Restricting `x|_R` along an algebra map `R → R'` gives `x|_{R'}`. -/
theorem xR_comp (h : R.R →ₐ[D.A] R'.R) : 𝔓.X.map (mO₀ h).op (𝔓.xR R) = 𝔓.xR R' := by
  rw [Problem.xR, map_map, mO₀_comp, comp_toBase]

/-- Restricting `y|_R` along an algebra map `R → R'` gives `y|_{R'}`. -/
theorem yR_comp (h : R.R →ₐ[D.A] R'.R) : 𝔓.Y.map (mO h).op (𝔓.yR R) = 𝔓.yR R' := by
  rw [Problem.yR, map_map, mO_comp, comp_toBase]

/-- The pullback of a lift along an algebra map `R → R'` is a lift over `R'`. -/
theorem Problem.Lifts.pull_prop (h : R.R →ₐ[D.A] R'.R) (z : 𝔓.Lifts R) :
    𝔓.X.map (incl R').op (𝔓.X.map (mO h).op z.1) = 𝔓.xR R' ∧
      𝔓.f.app _ (𝔓.X.map (mO h).op z.1) = 𝔓.yR R' := by
  refine ⟨?_, ?_⟩
  · rw [map_map, incl_mO, ← map_map, z.2.1, xR_comp]
  · rw [NatTrans.naturality_apply, z.2.2, yR_comp]

/-- Pullback of lifts along an algebra map. -/
noncomputable def Problem.Lifts.pull (h : R.R →ₐ[D.A] R'.R) (z : 𝔓.Lifts R) : 𝔓.Lifts R' :=
  ⟨𝔓.X.map (mO h).op z.1, Problem.Lifts.pull_prop h z⟩

/-- The pullback of a tangent vector along an algebra map `R → R'` is a tangent vector over
`R'`. -/
theorem Problem.Tangents.pull_prop (h : R.R →ₐ[D.A] R'.R) (t : 𝔓.Tangents R) :
    𝔓.X.map (zeroSec R').op (𝔓.X.map (mOₑ h).op t.1) = 𝔓.xR R' ∧
      𝔓.f.app _ (𝔓.X.map (mOₑ h).op t.1) = 𝔓.Y.map (retr R' ≫ incl R').op (𝔓.yR R') := by
  refine ⟨?_, ?_⟩
  · rw [map_map, zeroSec_mOₑ, ← map_map, t.2.1, xR_comp]
  · rw [NatTrans.naturality_apply, t.2.2]
    simp only [Problem.yR, map_map]
    refine congrArg (fun g => 𝔓.Y.map (Quiver.Hom.op g) 𝔓.y) ?_
    have e : mO h ≫ mO (toBase R) = mO (toBase R') := by rw [mO_comp, comp_toBase]
    rw [← e]
    simp only [Category.assoc]
    rw [reassoc_of% incl_mO, reassoc_of% retr_mO₀]

/-- Pullback of tangent vectors along an algebra map. -/
noncomputable def Problem.Tangents.pull (h : R.R →ₐ[D.A] R'.R) (t : 𝔓.Tangents R) :
    𝔓.Tangents R' :=
  ⟨𝔓.X.map (mOₑ h).op t.1, Problem.Tangents.pull_prop h t⟩

/-- **The action is natural in the algebra.** -/
theorem act_pull (h : R.R →ₐ[D.A] R'.R) (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    act (t.pull h) (z.pull h) = (act t z).pull h := by
  apply Subtype.ext
  change 𝔓.X.map (actHom R').op (glueLT (t.pull h) (z.pull h)) =
    𝔓.X.map (mO h).op (𝔓.X.map (actHom R).op (glueLT t z))
  have : glueLT (t.pull h) (z.pull h) = 𝔓.X.map (mOₚ h).op (glueLT t z) := by
    symm
    refine eq_glue 𝔓.hX (isPushout_rep R') _ _ _ _ ?_ ?_
    · rw [map_map, pInl_mOₚ, ← map_map, glueLT, map_glue_left]; rfl
    · rw [map_map, pInr_mOₚ, ← map_map, glueLT, map_glue_right]; rfl
  rw [this, map_map, actHom_mOₚ, ← map_map]

/-- Pulling back tangent vectors along `h` and then `h'` is pulling back along `h' ∘ h`. -/
theorem Problem.Tangents.pull_comp {R'' : Alg D} (h : R.R →ₐ[D.A] R'.R)
    (h' : R'.R →ₐ[D.A] R''.R) (t : 𝔓.Tangents R) : (t.pull h).pull h' = t.pull (h'.comp h) := by
  obtain ⟨t₀, ht⟩ := t
  apply Subtype.ext
  change 𝔓.X.map (mOₑ h').op (𝔓.X.map (mOₑ h).op t₀) = 𝔓.X.map (mOₑ (h'.comp h)).op t₀
  rw [map_map, mOₑ_comp]

/-- Pulling back lifts along `h` and then `h'` is pulling back along `h' ∘ h`. -/
theorem Problem.Lifts.pull_comp {R'' : Alg D} (h : R.R →ₐ[D.A] R'.R)
    (h' : R'.R →ₐ[D.A] R''.R) (z : 𝔓.Lifts R) : (z.pull h).pull h' = z.pull (h'.comp h) := by
  obtain ⟨z₀, hz⟩ := z
  apply Subtype.ext
  change 𝔓.X.map (mO h').op (𝔓.X.map (mO h).op z₀) = 𝔓.X.map (mO (h'.comp h)).op z₀
  rw [map_map, mO_comp]

/-! ### Scalars -/

/-- Scalar multiplication of tangent vectors by elements of the reduction. -/
noncomputable def Problem.Tangents.smul (a : Q D.C R.R) (t : 𝔓.Tangents R) : 𝔓.Tangents R :=
  ⟨𝔓.X.map (smulHom R a).op t.1, by rw [map_map, zeroSec_smul]; exact t.2.1, by
    rw [NatTrans.naturality_apply, t.2.2, map_map, ← Category.assoc, smul_retr]⟩

/-- Pullback of tangent vectors along an algebra map commutes with scalar multiplication. -/
theorem Problem.Tangents.smul_pull (h : R.R →ₐ[D.A] R'.R) (a : Q D.C R.R) (t : 𝔓.Tangents R) :
    (t.smul a).pull h = (t.pull h).smul (qMap D.C h a) := by
  obtain ⟨t₀, ht⟩ := t
  apply Subtype.ext
  change 𝔓.X.map (mOₑ h).op (𝔓.X.map (smulHom R a).op t₀) =
    𝔓.X.map (smulHom R' (qMap D.C h a)).op (𝔓.X.map (mOₑ h).op t₀)
  rw [map_map, map_map, smul_mOₑ]

end AlgebraicGeometry.Space.SmoothLift
