module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Action
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.Algebra.TrivSqZeroExtKernel

/-!
# Tangent vectors and lifts in an affine étale chart

Let `𝔓` be a lifting problem for `f : X ⟶ Y` along `Spec (A' ⧸ C) ⊂ Spec A'` and let `R` be an
`A'`-algebra.  A *chart* of `𝔓` over `R` is an affine étale chart `w : W ⟶ X`, an affine étale
chart `v : V ⟶ Y`, a morphism `k : W ⟶ V` over `f`, a factorisation `ℓ₀ : Spec (R ⧸ CR) ⟶ W`
of the restriction of `x`, and a factorisation `β : Spec R ⟶ V` of the restriction of `y`,
compatible with `k`.

Over a chart, both the tangent vectors and the lifts of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Action` are described by ring
maps out of `Γ(W)`: a tangent vector is a `Γ(V)`-derivation `D : Γ(W) → CR` relative to `ℓ₀`
(`Chart.tangent`), a lift is a ring map `φ : Γ(W) → R` reducing to `ℓ₀` and lying over `β`
(`Chart.lift`), both descriptions are bijective (Stacks 04AL: `W ⟶ X` and `V ⟶ Y` are formally
étale), and the action of a tangent vector on a lift is translation `φ ↦ φ + D`.

## References

* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

/-! ### Morphisms out of a spectrum into an affine scheme -/

section Affine

variable {W W' : Scheme.{u}} [IsAffine W]

/-- The ring map attached to a morphism `Spec A ⟶ W`. -/
noncomputable def sharp {A : CommRingCat.{u}} (g : Spec A ⟶ W) : Γ(W, ⊤) ⟶ A :=
  g.appTop ≫ (Scheme.ΓSpecIso A).hom

/-- The morphism `Spec A ⟶ W` attached to a ring map. -/
noncomputable def flat {A : CommRingCat.{u}} (χ : Γ(W, ⊤) ⟶ A) : Spec A ⟶ W :=
  Spec.map χ ≫ W.isoSpec.inv

/-- The global sections of `W.isoSpec.inv`, followed by `Γ(Spec Γ(W)) ≅ Γ(W)`, are the identity. -/
theorem isoSpec_inv_appTop_comp : W.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(W, ⊤)).hom = 𝟙 _ := by
  rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop,
    Iso.hom_inv_id, Scheme.Hom.id_appTop]

/-- `sharp` is a left inverse of `flat`. -/
theorem sharp_flat {A : CommRingCat.{u}} (χ : Γ(W, ⊤) ⟶ A) : sharp (flat χ) = χ := by
  rw [sharp, flat, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, isoSpec_inv_appTop_comp, Category.id_comp]

/-- A morphism `Spec A ⟶ W` is determined by its ring map. -/
theorem eq_of_sharp_eq {A : CommRingCat.{u}} {g g' : Spec A ⟶ W} (h : sharp g = sharp g') :
    g = g' :=
  ext_of_isAffine ((cancel_mono (Scheme.ΓSpecIso A).hom).mp h)

/-- `flat` is a left inverse of `sharp`. -/
theorem flat_sharp {A : CommRingCat.{u}} (g : Spec A ⟶ W) : flat (sharp g) = g :=
  eq_of_sharp_eq (sharp_flat _)

omit [IsAffine W] in
/-- The ring map of `Spec.map a ≫ g` is the ring map of `g` followed by `a`. -/
theorem sharp_specMap_comp {A A' : CommRingCat.{u}} (a : A ⟶ A') (g : Spec A ⟶ W) :
    sharp (Spec.map a ≫ g) = sharp g ≫ a := by
  rw [sharp, sharp, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Category.assoc]

omit [IsAffine W] in
/-- The ring map of `g ≫ k` is `k.appTop` followed by the ring map of `g`. -/
theorem sharp_comp {A : CommRingCat.{u}} [IsAffine W'] (g : Spec A ⟶ W) (k : W ⟶ W') :
    sharp (g ≫ k) = k.appTop ≫ sharp g := by
  rw [sharp, sharp, Scheme.Hom.comp_appTop, Category.assoc]

/-- Precomposing `flat χ` with `Spec.map a` gives `flat (χ ≫ a)`. -/
theorem flat_comp {A A' : CommRingCat.{u}} (a : A ⟶ A') (χ : Γ(W, ⊤) ⟶ A) :
    Spec.map a ≫ flat χ = flat (χ ≫ a) :=
  eq_of_sharp_eq (by rw [sharp_specMap_comp, sharp_flat, sharp_flat])

/-- Postcomposing `flat χ` with `k` gives `flat (k.appTop ≫ χ)`. -/
theorem flat_comp_right {A : CommRingCat.{u}} [IsAffine W'] (χ : Γ(W, ⊤) ⟶ A) (k : W ⟶ W') :
    flat χ ≫ k = flat (k.appTop ≫ χ) :=
  eq_of_sharp_eq (by rw [sharp_comp, sharp_flat, sharp_flat])

end Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of schemes over `S` between objects of the site, as a morphism of the site. -/
noncomputable def siteHom {U W : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hg : g ≫ B.inclusion.map W.hom = B.inclusion.map U.hom) : U ⟶ W :=
  Over.homMk (B.inclusion.preimage g) (B.inclusion.map_injective
    (by rwa [Functor.map_comp, B.inclusion.map_preimage]))

/-- The underlying morphism of schemes of `siteHom g hg` is `g`. -/
@[simp] theorem toScheme_map_siteHom {U W : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hg : g ≫ B.inclusion.map W.hom = B.inclusion.map U.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHom g hg) = g :=
  B.inclusion.map_preimage g

/-- The underlying morphism of schemes of a morphism of the site lies over `S`. -/
theorem toScheme_map_comp_hom {U W : BigFppfOver B S hS} (g : U ⟶ W) :
    (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map W.hom = B.inclusion.map U.hom := by
  change B.inclusion.map g.left ≫ B.inclusion.map W.hom = _
  rw [← B.inclusion.map_comp]
  exact congrArg B.inclusion.map (Over.w g)

/-! ### The square-zero thickenings of the lifting problem -/

variable {D : Base B S hS}

/-- `Spec (R ⧸ CR) ⟶ Spec R` is a square-zero closed immersion. -/
theorem isSquareZero_incl (R : Alg D) : IsSquareZeroClosedImmersion B S hS (incl R) := by
  have h := Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) Ideal.Quotient.mk_surjective (by
      change RingHom.ker (Ideal.Quotient.mk (sqIdeal D.C R.R)) ^ 2 = ⊥
      rw [Ideal.mk_ker, pow_two, sqIdeal_mul_self])
  exact ⟨h.1, h.2⟩

/-- The zero section `Spec (R ⧸ CR) ⟶ Spec (R ⧸ CR ⊕ CR)` is a square-zero closed immersion. -/
theorem isSquareZero_zeroSec (R : Alg D) : IsSquareZeroClosedImmersion B S hS (zeroSec R) := by
  have h := Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (fstE D.C R.R)) (fun q => ⟨TrivSqZeroExt.inl q, rfl⟩) (by
      change RingHom.ker (TrivSqZeroExt.fstHom (Q D.C R.R) (Q D.C R.R) (M D.C R.R)).toRingHom ^ 2
        = ⊥
      rw [pow_two]
      exact TrivSqZeroExt.ker_fstHom_mul_self_eq_bot)
  exact ⟨h.1, h.2⟩

/-- The scheme of the object `objOf Rc φ h` of the site is affine. -/
instance (Rc : CommRingCat.{u}) (φ : CommRingCat.of D.A ⟶ Rc) (h : #Rc < B.cutoff) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (objOf Rc φ h)) :=
  inferInstanceAs (IsAffine (Spec Rc))

/-! ### Charts -/

variable (𝔓 : Problem D)

/-- **An affine étale chart square of the morphism of the lifting problem.** -/
structure Frame where
  /-- The chart of the source. -/
  W : BigFppfOver B S hS
  /-- The chart of the target. -/
  V : BigFppfOver B S hS
  [affW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
  [affV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  /-- The chart morphism of the source. -/
  w : yoneda.obj W ⟶ 𝔓.X
  /-- The chart morphism of the target. -/
  v : yoneda.obj V ⟶ 𝔓.Y
  /-- The morphism of charts. -/
  k : W ⟶ V
  hk : yoneda.map k ≫ v = w ≫ 𝔓.f
  /-- The chart morphism of the source is étale. -/
  ew : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w
  /-- The chart morphism of the target is étale. -/
  ev : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v
  /-- The morphism of charts is smooth. -/
  sm : Smooth ((BigFppfOver.toScheme B S hS).map k)

attribute [instance] Frame.affW Frame.affV

variable {𝔓} (F : Frame 𝔓)

/-- **A chart of the lifting problem over an algebra.** -/
structure Framing (R : Alg D) where
  /-- The factorisation of `x` through the chart of the source. -/
  red : O₀ R ⟶ F.W
  /-- The factorisation of `y` through the chart of the target. -/
  base : O R ⟶ F.V
  hred : F.w.app (op (O₀ R)) red = 𝔓.xR R
  hbase : F.v.app (op (O R)) base = 𝔓.yR R
  comm : incl R ≫ base = red ≫ F.k

variable {F} {R : Alg D} (Fr : Framing F R)

/-- Naturality of the chart of the source with respect to precomposition. -/
theorem w_app_comp {U U' : BigFppfOver B S hS} (g : U' ⟶ U) (h : U ⟶ F.W) :
    F.w.app _ (g ≫ h) = 𝔓.X.map g.op (F.w.app _ h) :=
  NatTrans.naturality_apply F.w g.op h

/-- Naturality of the chart of the target with respect to precomposition. -/
theorem v_app_comp {U U' : BigFppfOver B S hS} (g : U' ⟶ U) (h : U ⟶ F.V) :
    F.v.app _ (g ≫ h) = 𝔓.Y.map g.op (F.v.app _ h) :=
  NatTrans.naturality_apply F.v g.op h

/-- The chart of the target at `h ≫ F.k` is the image under `𝔓.f` of the chart of the source at
`h`. -/
theorem v_app_comp_k {U : BigFppfOver B S hS} (h : U ⟶ F.W) :
    F.v.app _ (h ≫ F.k) = 𝔓.f.app _ (F.w.app _ h) :=
  congrFun (congrArg (fun α => α.app (op U)) F.hk) h

/-- The formal étaleness of the two charts, Stacks 04AL. -/
theorem formallyEtale_w : FormallyEtale F.w := formallyEtale_of_etale B S hS F.w F.ew

/-- The chart of the target is formally étale. -/
theorem formallyEtale_v : FormallyEtale F.v := formallyEtale_of_etale B S hS F.v F.ev

/-! ### Tangent vectors as morphisms into the chart -/

/-- The morphisms `Spec (R ⧸ CR ⊕ CR) ⟶ W` extending the chart of `x` over the chart of `y`. -/
abbrev Framing.Tau : Type u :=
  {τ : Oₑ R ⟶ F.W // zeroSec R ≫ τ = Fr.red ∧ τ ≫ F.k = retr R ≫ incl R ≫ Fr.base}

/-- The morphisms `Spec R ⟶ W` extending the chart of `x` over the chart of `y`. -/
abbrev Framing.Zeta : Type u :=
  {ζ : O R ⟶ F.W // incl R ≫ ζ = Fr.red ∧ ζ ≫ F.k = Fr.base}

/-- A tangent vector comes from a unique morphism `Spec (R ⧸ CR ⊕ CR) ⟶ W` extending the
factorisation of `x`. -/
theorem exists_tau (t : 𝔓.Tangents R) :
    ∃! τ : Oₑ R ⟶ F.W, zeroSec R ≫ τ = Fr.red ∧ F.w.app (op (Oₑ R)) τ = t.1 :=
  formallyEtale_w (F := F) _ _ inferInstance inferInstance (zeroSec R) (isSquareZero_zeroSec R)
    Fr.red t.1 (Fr.hred.trans t.2.1.symm)

/-- A lift comes from a unique morphism `Spec R ⟶ W` extending the factorisation of `x`. -/
theorem exists_zeta (z : 𝔓.Lifts R) :
    ∃! ζ : O R ⟶ F.W, incl R ≫ ζ = Fr.red ∧ F.w.app (op (O R)) ζ = z.1 :=
  formallyEtale_w (F := F) _ _ inferInstance inferInstance (incl R) (isSquareZero_incl R)
    Fr.red z.1 (Fr.hred.trans z.2.1.symm)

/-- The chart morphism of a tangent vector. -/
noncomputable def Framing.tau (t : 𝔓.Tangents R) : Oₑ R ⟶ F.W := (exists_tau Fr t).exists.choose

/-- The chart morphism of a tangent vector restricts to the factorisation of `x` along the zero
section. -/
theorem Framing.zeroSec_tau (t : 𝔓.Tangents R) : zeroSec R ≫ Fr.tau t = Fr.red :=
  (exists_tau Fr t).exists.choose_spec.1

/-- The chart of the source sends the chart morphism of a tangent vector to the tangent vector. -/
theorem Framing.w_tau (t : 𝔓.Tangents R) : F.w.app (op (Oₑ R)) (Fr.tau t) = t.1 :=
  (exists_tau Fr t).exists.choose_spec.2

/-- The chart morphism of a lift. -/
noncomputable def Framing.zeta (z : 𝔓.Lifts R) : O R ⟶ F.W := (exists_zeta Fr z).exists.choose

/-- The chart morphism of a lift restricts to the factorisation of `x` on `Spec (R ⧸ CR)`. -/
theorem Framing.incl_zeta (z : 𝔓.Lifts R) : incl R ≫ Fr.zeta z = Fr.red :=
  (exists_zeta Fr z).exists.choose_spec.1

/-- The chart of the source sends the chart morphism of a lift to the lift. -/
theorem Framing.w_zeta (z : 𝔓.Lifts R) : F.w.app (op (O R)) (Fr.zeta z) = z.1 :=
  (exists_zeta Fr z).exists.choose_spec.2

/-- The chart morphism of a tangent vector lies over the factorisation of `y` composed with the
retraction `Spec (R ⧸ CR ⊕ CR) ⟶ Spec (R ⧸ CR) ⟶ Spec R`. -/
theorem Framing.tau_k (t : 𝔓.Tangents R) : Fr.tau t ≫ F.k = retr R ≫ incl R ≫ Fr.base := by
  obtain ⟨_, -, huniq⟩ := formallyEtale_v (F := F) _ _ inferInstance inferInstance (zeroSec R)
    (isSquareZero_zeroSec R) (Fr.red ≫ F.k) (𝔓.Y.map (retr R ≫ incl R).op (𝔓.yR R)) (by
      rw [v_app_comp_k, Fr.hred, 𝔓.f_xR, map_map (zeroSec R) (retr R ≫ incl R),
        ← Category.assoc, zeroSec_retr, Category.id_comp])
  have h₁ := huniq (Fr.tau t ≫ F.k) ⟨by
    change zeroSec R ≫ Fr.tau t ≫ F.k = _
    rw [← Category.assoc, Fr.zeroSec_tau], by
    rw [v_app_comp_k, Fr.w_tau]; exact t.2.2⟩
  have h₂ := huniq (retr R ≫ incl R ≫ Fr.base) ⟨by
    change zeroSec R ≫ retr R ≫ incl R ≫ Fr.base = _
    rw [← Category.assoc, zeroSec_retr, Category.id_comp, Fr.comm], by
    rw [← Category.assoc, v_app_comp, Fr.hbase]⟩
  exact h₁.trans h₂.symm

/-- The chart morphism of a lift lies over the factorisation of `y`. -/
theorem Framing.zeta_k (z : 𝔓.Lifts R) : Fr.zeta z ≫ F.k = Fr.base := by
  obtain ⟨_, -, huniq⟩ := formallyEtale_v (F := F) _ _ inferInstance inferInstance (incl R)
    (isSquareZero_incl R) (Fr.red ≫ F.k) (𝔓.yR R) (by rw [v_app_comp_k, Fr.hred, 𝔓.f_xR])
  have h₁ := huniq (Fr.zeta z ≫ F.k) ⟨by
    change incl R ≫ Fr.zeta z ≫ F.k = _
    rw [← Category.assoc, Fr.incl_zeta], by
    rw [v_app_comp_k, Fr.w_zeta]; exact z.2.2⟩
  have h₂ := huniq Fr.base ⟨Fr.comm, Fr.hbase⟩
  exact h₁.trans h₂.symm

/-- **Tangent vectors are chart morphisms**, by formal étaleness of the two charts. -/
noncomputable def Framing.tauEquiv : 𝔓.Tangents R ≃ Fr.Tau where
  toFun t := ⟨Fr.tau t, Fr.zeroSec_tau t, Fr.tau_k t⟩
  invFun τ := ⟨F.w.app _ τ.1, by
    rw [← w_app_comp, τ.2.1, Fr.hred], by
    rw [← v_app_comp_k, τ.2.2, ← Category.assoc, v_app_comp, Fr.hbase]⟩
  left_inv t := Subtype.ext (Fr.w_tau t)
  right_inv τ := Subtype.ext ((exists_tau Fr _).unique
    ⟨Fr.zeroSec_tau _, Fr.w_tau _⟩ ⟨τ.2.1, rfl⟩)

/-- **Lifts are chart morphisms**, by formal étaleness of the two charts. -/
noncomputable def Framing.zetaEquiv : 𝔓.Lifts R ≃ Fr.Zeta where
  toFun z := ⟨Fr.zeta z, Fr.incl_zeta z, Fr.zeta_k z⟩
  invFun ζ := ⟨F.w.app _ ζ.1, by
    rw [← w_app_comp, ζ.2.1, Fr.hred], by
    rw [← v_app_comp_k, ζ.2.2, Fr.hbase]⟩
  left_inv z := Subtype.ext (Fr.w_zeta z)
  right_inv ζ := Subtype.ext ((exists_zeta Fr _).unique
    ⟨Fr.incl_zeta _, Fr.w_zeta _⟩ ⟨ζ.2.1, rfl⟩)

/-- The tangent vector of a chart morphism is its image under the chart of the source. -/
theorem Framing.tauEquiv_symm_val (τ : Fr.Tau) : (Fr.tauEquiv.symm τ).1 = F.w.app _ τ.1 := rfl

/-- The lift of a chart morphism is its image under the chart of the source. -/
theorem Framing.zetaEquiv_symm_val (ζ : Fr.Zeta) : (Fr.zetaEquiv.symm ζ).1 = F.w.app _ ζ.1 := rfl

/-! ### Ring coordinates -/

/-- A morphism of schemes into the chart of the source which lies over a morphism of the site
into the chart of the target is a morphism of the site. -/
noncomputable def siteHomVia {U : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj F.W)
    (m : U ⟶ F.V) (hg : g ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map m) : U ⟶ F.W :=
  siteHom g (by rw [← toScheme_map_comp_hom F.k, ← Category.assoc, hg, toScheme_map_comp_hom])

/-- The underlying morphism of schemes of `siteHomVia g m hg` is `g`. -/
@[simp] theorem toScheme_map_siteHomVia {U : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj F.W)
    (m : U ⟶ F.V) (hg : g ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map m) :
    (BigFppfOver.toScheme B S hS).map (siteHomVia g m hg) = g :=
  toScheme_map_siteHom _ _

/-- `siteHomVia g m hg` lies over `m`. -/
theorem siteHomVia_k {U : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj F.W)
    (m : U ⟶ F.V) (hg : g ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map m) : siteHomVia g m hg ≫ F.k = m :=
  ext_toScheme (by rw [Functor.map_comp, toScheme_map_siteHomVia, hg])

/-- The ring of the chart of the source. -/
noncomputable abbrev Frame.PW : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj F.W, ⊤)

/-- The ring of the chart of the target. -/
noncomputable abbrev Frame.PV : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj F.V, ⊤)

/-- The ring map of the morphism of charts. -/
noncomputable abbrev Frame.kS : F.PV ⟶ F.PW := ((BigFppfOver.toScheme B S hS).map F.k).appTop

/-- The factorisation of `x`, as a morphism of schemes out of a spectrum. -/
noncomputable abbrev Framing.redS :
    Spec (CommRingCat.of (Q D.C R.R)) ⟶ (BigFppfOver.toScheme B S hS).obj F.W :=
  (BigFppfOver.toScheme B S hS).map Fr.red

/-- The factorisation of `y`, as a morphism of schemes out of a spectrum. -/
noncomputable abbrev Framing.baseS :
    Spec (CommRingCat.of R.R) ⟶ (BigFppfOver.toScheme B S hS).obj F.V :=
  (BigFppfOver.toScheme B S hS).map Fr.base

/-- The factorisations of `x` and `y` are compatible, as morphisms of schemes. -/
theorem Framing.commS : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) ≫
    Fr.baseS = Fr.redS ≫ (BigFppfOver.toScheme B S hS).map F.k := by
  have := congrArg (BigFppfOver.toScheme B S hS).map Fr.comm
  simp only [Functor.map_comp] at this
  exact this

/-- The ring map `Γ(W) → R ⧸ CR` of the factorisation of `x`. -/
noncomputable def Framing.lS : F.PW ⟶ CommRingCat.of (Q D.C R.R) := sharp Fr.redS

/-- The ring map `Γ(V) → R` of the factorisation of `y`. -/
noncomputable def Framing.bS : F.PV ⟶ CommRingCat.of R.R := sharp Fr.baseS

/-- The ring maps of the factorisations of `x` and `y` are compatible with `Γ(V) → Γ(W)` and
`R → R ⧸ CR`. -/
theorem Framing.kS_lS : F.kS ≫ Fr.lS = Fr.bS ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) := by
  rw [Framing.lS, Framing.bS, ← sharp_specMap_comp, ← sharp_comp, Fr.commS]

/-- **Tangent vectors in coordinates**: the additive maps `Γ(W) → CR` which are derivations
relative to `Γ(W) → R ⧸ CR` and kill `Γ(V)`, as a submodule over `R ⧸ CR`. -/
def Framing.DerSub : Submodule (Q D.C R.R) (F.PW →+ M D.C R.R) where
  carrier := {δ | (∀ a b, δ (a * b) = Fr.lS a • δ b + Fr.lS b • δ a) ∧ ∀ v, δ (F.kS v) = 0}
  add_mem' {δ δ'} hδ hδ' := ⟨fun a b => by
      simp only [AddMonoidHom.add_apply, hδ.1, hδ'.1, smul_add]; abel,
    fun v => by simp [hδ.2, hδ'.2]⟩
  zero_mem' := ⟨fun a b => by simp, fun v => by simp⟩
  smul_mem' c {δ} hδ := ⟨fun a b => by
      simp only [AddMonoidHom.smul_apply, hδ.1, smul_add]
      rw [smul_comm c (Fr.lS a), smul_comm c (Fr.lS b)],
    fun v => by simp [hδ.2]⟩

/-- A coordinate tangent vector. -/
abbrev Framing.Der : Type u := Fr.DerSub

/-- The Leibniz rule of a coordinate tangent vector. -/
theorem Framing.Der.map_mul (δ : Fr.Der) (a b : F.PW) :
    (δ : F.PW →+ M D.C R.R) (a * b) = Fr.lS a • (δ : F.PW →+ M D.C R.R) b +
      Fr.lS b • (δ : F.PW →+ M D.C R.R) a := δ.2.1 a b

/-- A coordinate tangent vector vanishes on `Γ(V)`. -/
theorem Framing.Der.map_base (δ : Fr.Der) (v : F.PV) :
    (δ : F.PW →+ M D.C R.R) (F.kS v) = 0 := δ.2.2 v

/-- The ring map `Γ(W) → R ⧸ CR ⊕ CR` of a coordinate derivation. -/
noncomputable def Framing.chi (δ : Fr.Der) : F.PW ⟶ CommRingCat.of (E D.C R.R) :=
  CommRingCat.ofHom
    { toFun a := TrivSqZeroExt.inl (Fr.lS a) + TrivSqZeroExt.inr ((δ : F.PW →+ M D.C R.R) a)
      map_one' := by
        have h1 : (δ : F.PW →+ M D.C R.R) 1 = 0 := by
          simpa using Framing.Der.map_mul Fr δ 1 1
        ext <;> simp [h1]
      map_mul' a b := by
        apply TrivSqZeroExt.ext
        · simp
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
            zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
            TrivSqZeroExt.fst_inr, add_zero, op_smul_M, Framing.Der.map_mul]
      map_zero' := by ext <;> simp
      map_add' a b := by ext <;> simp }

/-- `chi δ` reduces to the ring map `Γ(W) → R ⧸ CR` of the factorisation of `x`. -/
theorem Framing.chi_fstE (δ : Fr.Der) : Fr.chi δ ≫ CommRingCat.ofHom (fstE D.C R.R) = Fr.lS := by
  ext a
  simp [Framing.chi]

/-- On `Γ(V)`, `chi δ` is the ring map of the factorisation of `y` followed by
`R → R ⧸ CR → R ⧸ CR ⊕ CR`. -/
theorem Framing.kS_chi (δ : Fr.Der) :
    F.kS ≫ Fr.chi δ = Fr.bS ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) ≫
      CommRingCat.ofHom (inlE D.C R.R) := by
  rw [← Category.assoc, ← Fr.kS_lS]
  ext v
  · simp [Framing.chi]
  · simp [Framing.chi, Framing.Der.map_base]

/-- The morphism of schemes of `chi δ` lies over the factorisation of `y`. -/
theorem Framing.flat_chi_k (δ : Fr.Der) :
    flat (Fr.chi δ) ≫ (BigFppfOver.toScheme B S hS).map F.k =
      Spec.map (CommRingCat.ofHom (inlE D.C R.R)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) ≫ Fr.baseS := by
  rw [flat_comp_right, Fr.kS_chi, ← flat_sharp Fr.baseS, flat_comp, flat_comp]
  simp only [Category.assoc]
  rfl

/-- The morphism of schemes of `chi δ` restricts to the factorisation of `x` along the zero
section. -/
theorem Framing.fstE_flat_chi (δ : Fr.Der) :
    Spec.map (CommRingCat.ofHom (fstE D.C R.R)) ≫ flat (Fr.chi δ) = Fr.redS := by
  rw [flat_comp, Fr.chi_fstE, Framing.lS, flat_sharp]

/-- The morphism of schemes of `chi δ` lies over `retr R ≫ incl R ≫ Fr.base`. -/
theorem Framing.flat_chi_k' (δ : Fr.Der) :
    flat (Fr.chi δ) ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map (retr R ≫ incl R ≫ Fr.base) := by
  rw [Functor.map_comp, Functor.map_comp]
  exact Fr.flat_chi_k δ

/-- The chart morphism of a coordinate derivation, as a morphism of the site. -/
noncomputable def Framing.tauHom (δ : Fr.Der) : Oₑ R ⟶ F.W :=
  siteHomVia (flat (Fr.chi δ)) (retr R ≫ incl R ≫ Fr.base) (Fr.flat_chi_k' δ)

/-- The underlying morphism of schemes of `tauHom δ` is `flat (chi δ)`. -/
theorem Framing.toScheme_tauHom (δ : Fr.Der) :
    (BigFppfOver.toScheme B S hS).map (Fr.tauHom δ) = flat (Fr.chi δ) :=
  toScheme_map_siteHomVia _ _ _

/-- `tauHom δ` restricts to the factorisation of `x` along the zero section. -/
theorem Framing.zeroSec_tauHom (δ : Fr.Der) : zeroSec R ≫ Fr.tauHom δ = Fr.red := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_tauHom]
  exact Fr.fstE_flat_chi δ

/-- `tauHom δ` lies over `retr R ≫ incl R ≫ Fr.base`. -/
theorem Framing.tauHom_k (δ : Fr.Der) : Fr.tauHom δ ≫ F.k = retr R ≫ incl R ≫ Fr.base :=
  siteHomVia_k _ _ _

/-- The chart morphism of a coordinate derivation. -/
noncomputable def Framing.tauOf (δ : Fr.Der) : Fr.Tau :=
  ⟨Fr.tauHom δ, Fr.zeroSec_tauHom δ, Fr.tauHom_k δ⟩

/-- A chart morphism of a tangent vector, as a morphism of schemes out of a spectrum. -/
noncomputable abbrev Framing.tauS (τ : Fr.Tau) :
    Spec (CommRingCat.of (E D.C R.R)) ⟶ (BigFppfOver.toScheme B S hS).obj F.W :=
  (BigFppfOver.toScheme B S hS).map τ.1

/-- A chart morphism of a tangent vector restricts to the factorisation of `x` along the zero
section, as morphisms of schemes. -/
theorem Framing.tauS_zeroSec (τ : Fr.Tau) :
    Spec.map (CommRingCat.ofHom (fstE D.C R.R)) ≫ Fr.tauS τ = Fr.redS :=
  (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map τ.2.1)

/-- A chart morphism of a tangent vector lies over the factorisation of `y`, as morphisms of
schemes. -/
theorem Framing.tauS_k (τ : Fr.Tau) :
    Fr.tauS τ ≫ (BigFppfOver.toScheme B S hS).map F.k =
      Spec.map (CommRingCat.ofHom (inlE D.C R.R)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) ≫ Fr.baseS := by
  have := congrArg (BigFppfOver.toScheme B S hS).map τ.2.2
  simp only [Functor.map_comp] at this
  exact this

/-- The ring map `Γ(W) → R ⧸ CR ⊕ CR` of a chart morphism. -/
noncomputable def Framing.chiOf (τ : Fr.Tau) : F.PW ⟶ CommRingCat.of (E D.C R.R) :=
  sharp (Fr.tauS τ)

/-- The ring map of a chart morphism reduces to the ring map of the factorisation of `x`. -/
theorem Framing.chiOf_fstE (τ : Fr.Tau) :
    Fr.chiOf τ ≫ CommRingCat.ofHom (fstE D.C R.R) = Fr.lS := by
  rw [Framing.chiOf, ← sharp_specMap_comp, Fr.tauS_zeroSec, Framing.lS]

/-- On `Γ(V)`, the ring map of a chart morphism is the ring map of the factorisation of `y`
followed by `R → R ⧸ CR → R ⧸ CR ⊕ CR`. -/
theorem Framing.kS_chiOf (τ : Fr.Tau) :
    F.kS ≫ Fr.chiOf τ = Fr.bS ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) ≫
      CommRingCat.ofHom (inlE D.C R.R) := by
  rw [Framing.chiOf, ← sharp_comp, Fr.tauS_k, sharp_specMap_comp, sharp_specMap_comp,
    Framing.bS, Category.assoc]

/-- The first component of the ring map of a chart morphism is the ring map of the factorisation of
`x`. -/
theorem Framing.fst_chiOf (τ : Fr.Tau) (a : F.PW) : (Fr.chiOf τ a).fst = Fr.lS a :=
  ConcreteCategory.congr_hom (Fr.chiOf_fstE τ) a

/-- On `Γ(V)`, the ring map of a chart morphism is the reduction of the ring map of the
factorisation of `y`, included in `R ⧸ CR ⊕ CR`. -/
theorem Framing.chiOf_kS (τ : Fr.Tau) (v : F.PV) :
    Fr.chiOf τ (F.kS v) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (Fr.bS v)) :=
  ConcreteCategory.congr_hom (Fr.kS_chiOf τ) v

/-- The coordinate derivation of a chart morphism. -/
noncomputable def Framing.derOf (τ : Fr.Tau) : Fr.Der :=
  ⟨{ toFun a := (Fr.chiOf τ a).snd
     map_zero' := by simp
     map_add' a b := by simp }, fun a b => by
    change (Fr.chiOf τ (a * b)).snd = Fr.lS a • (Fr.chiOf τ b).snd + Fr.lS b • (Fr.chiOf τ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, Fr.fst_chiOf, Fr.fst_chiOf, op_smul_M], fun v => by
    change (Fr.chiOf τ (F.kS v)).snd = 0
    rw [Fr.chiOf_kS, TrivSqZeroExt.snd_inl]⟩

/-- The ring map of the coordinate derivation of a chart morphism `τ` is the ring map of `τ`. -/
theorem Framing.chi_derOf (τ : Fr.Tau) : Fr.chi (Fr.derOf τ) = Fr.chiOf τ := by
  ext a
  · simp [Framing.chi, Fr.fst_chiOf]
  · simp [Framing.chi, Framing.derOf]

/-- The ring map of the chart morphism of a coordinate derivation `δ` is `chi δ`. -/
theorem Framing.chiOf_tauOf (δ : Fr.Der) : Fr.chiOf (Fr.tauOf δ) = Fr.chi δ := by
  rw [Framing.chiOf]
  change sharp ((BigFppfOver.toScheme B S hS).map (Fr.tauHom δ)) = _
  rw [Fr.toScheme_tauHom, sharp_flat]

/-- A chart morphism of a tangent vector is determined by its ring map. -/
theorem Framing.tau_ext {τ τ' : Fr.Tau} (h : Fr.chiOf τ = Fr.chiOf τ') : τ = τ' :=
  Subtype.ext (ext_toScheme (eq_of_sharp_eq h))

/-- **Chart morphisms are coordinate derivations.** -/
noncomputable def Framing.derEquiv : Fr.Tau ≃ Fr.Der where
  toFun := Fr.derOf
  invFun := Fr.tauOf
  left_inv τ := Fr.tau_ext (by rw [Fr.chiOf_tauOf, Fr.chi_derOf])
  right_inv δ := by
    refine Subtype.ext (AddMonoidHom.ext fun a => ?_)
    change (Fr.chiOf (Fr.tauOf δ) a).snd = _
    rw [Fr.chiOf_tauOf]
    simp [Framing.chi]

/-- **Tangent vectors in coordinates.** -/
noncomputable def Framing.tangentEquiv : 𝔓.Tangents R ≃ Fr.Der :=
  Fr.tauEquiv.trans Fr.derEquiv

/-! ### Lifts in coordinates -/

/-- **A lift in coordinates**: a ring map `Γ(W) → R` reducing to `Γ(W) → R ⧸ CR` and lying
over `Γ(V) → R`. -/
abbrev Framing.RingLift : Type u :=
  {φ : F.PW ⟶ CommRingCat.of R.R //
    φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R)) = Fr.lS ∧ F.kS ≫ φ = Fr.bS}

/-- A chart morphism of a lift, as a morphism of schemes out of a spectrum. -/
noncomputable abbrev Framing.zetaS (ζ : Fr.Zeta) :
    Spec (CommRingCat.of R.R) ⟶ (BigFppfOver.toScheme B S hS).obj F.W :=
  (BigFppfOver.toScheme B S hS).map ζ.1

/-- A chart morphism of a lift restricts to the factorisation of `x` on `Spec (R ⧸ CR)`, as
morphisms of schemes. -/
theorem Framing.zetaS_incl (ζ : Fr.Zeta) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) ≫ Fr.zetaS ζ = Fr.redS :=
  (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map ζ.2.1)

/-- A chart morphism of a lift lies over the factorisation of `y`, as morphisms of schemes. -/
theorem Framing.zetaS_k (ζ : Fr.Zeta) :
    Fr.zetaS ζ ≫ (BigFppfOver.toScheme B S hS).map F.k = Fr.baseS :=
  (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map ζ.2.2)

/-- The ring map of a chart morphism of a lift. -/
noncomputable def Framing.phiOf (ζ : Fr.Zeta) : Fr.RingLift :=
  ⟨sharp (Fr.zetaS ζ), by rw [← sharp_specMap_comp, Fr.zetaS_incl, Framing.lS], by
    rw [← sharp_comp, Fr.zetaS_k, Framing.bS]⟩

/-- The morphism of schemes of a ring lift lies over the factorisation of `y`. -/
theorem Framing.flat_ringLift_k (φ : Fr.RingLift) :
    flat φ.1 ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map Fr.base := by
  rw [flat_comp_right, φ.2.2, Framing.bS, flat_sharp]

/-- The chart morphism of a ring lift, as a morphism of the site. -/
noncomputable def Framing.zetaHom (φ : Fr.RingLift) : O R ⟶ F.W :=
  siteHomVia (flat φ.1) Fr.base (Fr.flat_ringLift_k φ)

/-- The underlying morphism of schemes of `zetaHom φ` is `flat φ`. -/
theorem Framing.toScheme_zetaHom (φ : Fr.RingLift) :
    (BigFppfOver.toScheme B S hS).map (Fr.zetaHom φ) = flat φ.1 :=
  toScheme_map_siteHomVia _ _ _

/-- `zetaHom φ` restricts to the factorisation of `x` on `Spec (R ⧸ CR)`. -/
theorem Framing.incl_zetaHom (φ : Fr.RingLift) : incl R ≫ Fr.zetaHom φ = Fr.red := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_zetaHom]
  change Spec.map _ ≫ flat φ.1 = Fr.redS
  rw [flat_comp, φ.2.1, Framing.lS, flat_sharp]

/-- The chart morphism of a ring lift. -/
noncomputable def Framing.zetaOf (φ : Fr.RingLift) : Fr.Zeta :=
  ⟨Fr.zetaHom φ, Fr.incl_zetaHom φ, siteHomVia_k _ _ _⟩

/-- `zetaOf` is a left inverse of `phiOf`. -/
theorem Framing.zetaOf_phiOf (ζ : Fr.Zeta) : Fr.zetaOf (Fr.phiOf ζ) = ζ := by
  apply Subtype.ext
  apply ext_toScheme
  change (BigFppfOver.toScheme B S hS).map (Fr.zetaHom (Fr.phiOf ζ)) = _
  rw [Fr.toScheme_zetaHom]
  exact flat_sharp (Fr.zetaS ζ)

/-- `phiOf` is a left inverse of `zetaOf`. -/
theorem Framing.phiOf_zetaOf (φ : Fr.RingLift) : Fr.phiOf (Fr.zetaOf φ) = φ := by
  apply Subtype.ext
  change sharp ((BigFppfOver.toScheme B S hS).map (Fr.zetaHom φ)) = φ.1
  rw [Fr.toScheme_zetaHom, sharp_flat]

/-- **Chart morphisms of lifts are ring lifts.** -/
noncomputable def Framing.ringEquiv : Fr.Zeta ≃ Fr.RingLift where
  toFun := Fr.phiOf
  invFun := Fr.zetaOf
  left_inv := Fr.zetaOf_phiOf
  right_inv := Fr.phiOf_zetaOf

/-- **Lifts in coordinates.** -/
noncomputable def Framing.liftEquiv : 𝔓.Lifts R ≃ Fr.RingLift :=
  Fr.zetaEquiv.trans Fr.ringEquiv

/-! ### Translation of a ring lift by a coordinate derivation -/

/-- A ring lift reduces modulo `CR` to the ring map of the factorisation of `x`. -/
theorem Framing.ringLift_mk (φ : Fr.RingLift) (a : F.PW) :
    Ideal.Quotient.mk (sqIdeal D.C R.R) (φ.1 a) = Fr.lS a :=
  ConcreteCategory.congr_hom φ.2.1 a

/-- The action of `R ⧸ CR` on `CR`, computed through a ring lift `φ`, is multiplication by the
values of `φ` in `R`. -/
theorem Framing.coe_lS_smul (φ : Fr.RingLift) (a : F.PW) (m : M D.C R.R) :
    ((Fr.lS a • m : M D.C R.R) : R.R) = φ.1 a * m := by
  rw [← Fr.ringLift_mk φ a, mk_smul]
  rfl

/-- **The translate `φ + δ`** of a ring lift by a coordinate derivation. -/
noncomputable def Framing.translate (φ : Fr.RingLift) (δ : Fr.Der) : Fr.RingLift :=
  ⟨CommRingCat.ofHom
    { toFun a := φ.1 a + ((δ : F.PW →+ M D.C R.R) a : R.R)
      map_one' := by
        have h1 : (δ : F.PW →+ M D.C R.R) 1 = 0 := by
          simpa using Framing.Der.map_mul Fr δ 1 1
        simp [h1]
      map_mul' a b := by
        simp only [map_mul, Framing.Der.map_mul, Submodule.coe_add, Fr.coe_lS_smul φ]
        linear_combination -mul_eq_zero_of_mem D.C R.R ((δ : F.PW →+ M D.C R.R) a).2
          ((δ : F.PW →+ M D.C R.R) b).2
      map_zero' := by simp
      map_add' a b := by simp only [map_add, Submodule.coe_add]; ring }, by
    ext a
    change Ideal.Quotient.mk _ (φ.1 a + ((δ : F.PW →+ M D.C R.R) a : R.R)) = Fr.lS a
    rw [map_add, Fr.ringLift_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
      ((δ : F.PW →+ M D.C R.R) a).2, add_zero], by
    ext v
    change φ.1 (F.kS v) + ((δ : F.PW →+ M D.C R.R) (F.kS v) : R.R) = Fr.bS v
    rw [Framing.Der.map_base, Submodule.coe_zero, add_zero]
    exact congrArg (fun g => g.hom v) φ.2.2⟩

/-- The translate `φ + δ` takes `a` to `φ a + δ a`. -/
theorem Framing.translate_apply (φ : Fr.RingLift) (δ : Fr.Der) (a : F.PW) :
    (Fr.translate φ δ).1 a = φ.1 a + ((δ : F.PW →+ M D.C R.R) a : R.R) := rfl

/-- Translating by `δ + δ'` is translating by `δ'` and then by `δ`. -/
theorem Framing.translate_add (φ : Fr.RingLift) (δ δ' : Fr.Der) :
    Fr.translate φ (δ + δ') = Fr.translate (Fr.translate φ δ') δ := by
  apply Subtype.ext
  ext a
  change φ.1 a + (((δ + δ' : Fr.Der) : F.PW →+ M D.C R.R) a : R.R) =
    (φ.1 a + ((δ' : F.PW →+ M D.C R.R) a : R.R)) + ((δ : F.PW →+ M D.C R.R) a : R.R)
  rw [Submodule.coe_add, AddMonoidHom.add_apply, Submodule.coe_add]
  ring

/-- Translating by zero is the identity. -/
theorem Framing.translate_zero (φ : Fr.RingLift) : Fr.translate φ 0 = φ := by
  apply Subtype.ext
  ext a
  change φ.1 a + (((0 : Fr.Der) : F.PW →+ M D.C R.R) a : R.R) = φ.1 a
  simp

/-- Translating a fixed ring lift is injective in the coordinate derivation. -/
theorem Framing.translate_injective (φ : Fr.RingLift) :
    Function.Injective (Fr.translate φ) := by
  intro δ δ' h
  apply Subtype.ext
  ext a
  have h' : φ.1 a + ((δ : F.PW →+ M D.C R.R) a : R.R) =
      φ.1 a + ((δ' : F.PW →+ M D.C R.R) a : R.R) := congrArg (fun ψ : Fr.RingLift => ψ.1 a) h
  exact add_left_cancel h'

/-- Any two ring lifts differ by translation by a coordinate derivation. -/
theorem Framing.exists_translate (φ φ' : Fr.RingLift) : ∃ δ : Fr.Der, Fr.translate φ δ = φ' := by
  have hmem : ∀ a, φ'.1 a - φ.1 a ∈ sqIdeal D.C R.R := fun a => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Fr.ringLift_mk, Fr.ringLift_mk, sub_self]
  let δ₀ : F.PW →+ M D.C R.R :=
    { toFun a := ⟨φ'.1 a - φ.1 a, hmem a⟩
      map_zero' := Subtype.ext (by simp)
      map_add' a b := Subtype.ext (by simp only [map_add, Submodule.coe_add]; ring) }
  refine ⟨⟨δ₀, fun a b => Subtype.ext ?_, fun v => Subtype.ext ?_⟩, ?_⟩
  · simp only [δ₀, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, Submodule.coe_add,
      Fr.coe_lS_smul φ]
    linear_combination mul_eq_zero_of_mem D.C R.R (hmem a) (hmem b)
  · simp only [δ₀, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Submodule.coe_zero]
    rw [sub_eq_zero]
    exact (ConcreteCategory.congr_hom φ'.2.2 v).trans (ConcreteCategory.congr_hom φ.2.2 v).symm
  · apply Subtype.ext
    ext a
    change φ.1 a + (φ'.1 a - φ.1 a) = φ'.1 a
    ring

/-! ### The action in coordinates -/

/-- The ring map `Γ(W) → E ×_Q R` of a ring lift and a coordinate derivation. -/
noncomputable def Framing.psi (φ : Fr.RingLift) (δ : Fr.Der) :
    F.PW ⟶ CommRingCat.of (P D.C R.R) :=
  CommRingCat.ofHom
    { toFun a := ⟨((Fr.chi δ).hom a, φ.1 a), by
        change ((Fr.chi δ).hom a).fst = Ideal.Quotient.mk _ (φ.1 a)
        rw [Fr.ringLift_mk]
        simp [Framing.chi]⟩
      map_one' := by ext <;> simp
      map_mul' a b := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' a b := by ext <;> simp }

/-- The second component of `psi φ δ` is `φ`. -/
theorem Framing.psi_psnd (φ : Fr.RingLift) (δ : Fr.Der) :
    Fr.psi φ δ ≫ CommRingCat.ofHom ((fstE D.C R.R).pullbackSnd (Ideal.Quotient.mk _)) = φ.1 := rfl

/-- The first component of `psi φ δ` is `chi δ`. -/
theorem Framing.psi_pfst (φ : Fr.RingLift) (δ : Fr.Der) :
    Fr.psi φ δ ≫ CommRingCat.ofHom ((fstE D.C R.R).pullbackFst (Ideal.Quotient.mk _)) =
      Fr.chi δ := rfl

/-- `psi φ δ` followed by `sigma` is the translate `φ + δ`. -/
theorem Framing.psi_sigma (φ : Fr.RingLift) (δ : Fr.Der) :
    Fr.psi φ δ ≫ CommRingCat.ofHom (sigma D.C R.R) = (Fr.translate φ δ).1 := by
  ext a
  change φ.1 a + ((((Fr.chi δ).hom a).snd : M D.C R.R) : R.R) = φ.1 a + _
  simp [Framing.chi]

/-- On `Γ(V)`, `psi φ δ` is the ring map of the factorisation of `y` followed by
`pDiag R`. -/
theorem Framing.kS_psi (φ : Fr.RingLift) (δ : Fr.Der) :
    F.kS ≫ Fr.psi φ δ = Fr.bS ≫ CommRingCat.ofHom (pDiag R) :=
  CommRingCat.hom_ext <| RingHom.ext fun v => Subtype.ext <| Prod.ext
    (ConcreteCategory.congr_hom (Fr.kS_chi δ) v) (ConcreteCategory.congr_hom φ.2.2 v)

/-- The morphism of schemes of `psi φ δ` lies over `pProj R ≫ Fr.base`. -/
theorem Framing.flat_psi_k (φ : Fr.RingLift) (δ : Fr.Der) :
    flat (Fr.psi φ δ) ≫ (BigFppfOver.toScheme B S hS).map F.k =
      (BigFppfOver.toScheme B S hS).map (pProj R ≫ Fr.base) := by
  rw [flat_comp_right, Fr.kS_psi, Functor.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (pDiag R)) ≫ Fr.baseS
  rw [← flat_comp, Framing.bS, flat_sharp]

/-- The chart morphism out of the pushout `Spec (E ×_Q R)`. -/
noncomputable def Framing.pHom (φ : Fr.RingLift) (δ : Fr.Der) : Oₚ R ⟶ F.W :=
  siteHomVia (flat (Fr.psi φ δ)) (pProj R ≫ Fr.base) (Fr.flat_psi_k φ δ)

/-- The underlying morphism of schemes of `pHom φ δ` is `flat (psi φ δ)`. -/
theorem Framing.toScheme_pHom (φ : Fr.RingLift) (δ : Fr.Der) :
    (BigFppfOver.toScheme B S hS).map (Fr.pHom φ δ) = flat (Fr.psi φ δ) :=
  toScheme_map_siteHomVia _ _ _

/-- `pHom φ δ` restricts to `zetaHom φ` along `pInl R`. -/
theorem Framing.pInl_pHom (φ : Fr.RingLift) (δ : Fr.Der) :
    pInl R ≫ Fr.pHom φ δ = Fr.zetaHom φ := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_zetaHom, Fr.toScheme_pHom]
  exact (flat_comp _ _).trans (by rw [Fr.psi_psnd])

/-- `pHom φ δ` restricts to `tauHom δ` along `pInr R`. -/
theorem Framing.pInr_pHom (φ : Fr.RingLift) (δ : Fr.Der) :
    pInr R ≫ Fr.pHom φ δ = Fr.tauHom δ := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_tauHom, Fr.toScheme_pHom]
  exact (flat_comp _ _).trans (by rw [Fr.psi_pfst])

/-- `pHom φ δ` restricts along `actHom R` to the chart morphism of the translate `φ + δ`. -/
theorem Framing.actHom_pHom (φ : Fr.RingLift) (δ : Fr.Der) :
    actHom R ≫ Fr.pHom φ δ = Fr.zetaHom (Fr.translate φ δ) := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_zetaHom, Fr.toScheme_pHom]
  exact (flat_comp _ _).trans (by rw [Fr.psi_sigma])

/-- The tangent vector of a coordinate derivation `δ` is the image of `tauHom δ` under the chart of
the source. -/
theorem Framing.tangentEquiv_symm_val (δ : Fr.Der) :
    (Fr.tangentEquiv.symm δ).1 = F.w.app (op (Oₑ R)) (Fr.tauHom δ) := rfl

/-- The lift of a ring lift `φ` is the image of `zetaHom φ` under the chart of the source. -/
theorem Framing.liftEquiv_symm_val (φ : Fr.RingLift) :
    (Fr.liftEquiv.symm φ).1 = F.w.app (op (O R)) (Fr.zetaHom φ) := rfl

/-- **The action is translation in coordinates.** -/
theorem Framing.act_symm (δ : Fr.Der) (φ : Fr.RingLift) :
    act (Fr.tangentEquiv.symm δ) (Fr.liftEquiv.symm φ) = Fr.liftEquiv.symm (Fr.translate φ δ) := by
  apply Subtype.ext
  have hg : glueLT (Fr.tangentEquiv.symm δ) (Fr.liftEquiv.symm φ) =
      F.w.app (op (Oₚ R)) (Fr.pHom φ δ) := by
    refine (eq_glue 𝔓.hX (isPushout_rep R) _ _ _ _ ?_ ?_).symm
    · rw [← w_app_comp, Fr.pInl_pHom]
      rfl
    · rw [← w_app_comp, Fr.pInr_pHom]
      rfl
  change 𝔓.X.map (actHom R).op (glueLT _ _) = _
  rw [hg, ← w_app_comp, Fr.actHom_pHom]
  rfl

/-- **The action in coordinates.** -/
theorem Framing.liftEquiv_act (t : 𝔓.Tangents R) (z : 𝔓.Lifts R) :
    Fr.liftEquiv (act t z) = Fr.translate (Fr.liftEquiv z) (Fr.tangentEquiv t) := by
  conv_lhs => rw [← Fr.tangentEquiv.symm_apply_apply t, ← Fr.liftEquiv.symm_apply_apply z]
  rw [Fr.act_symm, Equiv.apply_symm_apply]

include Fr in
/-- **The action is free over a framed algebra.** -/
theorem Framing.act_injective (z : 𝔓.Lifts R) :
    Function.Injective (fun t : 𝔓.Tangents R => act t z) := by
  intro t t' h
  exact Fr.tangentEquiv.injective (Fr.translate_injective _
    (by simpa only [Fr.liftEquiv_act] using congrArg Fr.liftEquiv h))

include Fr in
/-- **The action is transitive over a framed algebra.** -/
theorem Framing.exists_act (z z' : 𝔓.Lifts R) : ∃ t : 𝔓.Tangents R, act t z = z' := by
  obtain ⟨δ, hδ⟩ := Fr.exists_translate (Fr.liftEquiv z) (Fr.liftEquiv z')
  refine ⟨Fr.tangentEquiv.symm δ, Fr.liftEquiv.injective ?_⟩
  rw [Fr.liftEquiv_act, Equiv.apply_symm_apply, hδ]

/-! ### Scalars in coordinates -/

/-- `chi δ` followed by multiplication by `a` on `CR` is `chi (a • δ)`. -/
theorem Framing.chi_smul (a : Q D.C R.R) (δ : Fr.Der) :
    Fr.chi δ ≫ CommRingCat.ofHom (smulE D.C R.R a) = Fr.chi (a • δ) := by
  ext x <;> simp [Framing.chi]

/-- `tauHom (a • δ)` is `tauHom δ` precomposed with the scalar multiplication by `a`. -/
theorem Framing.smulHom_tauHom (a : Q D.C R.R) (δ : Fr.Der) :
    smulHom R a ≫ Fr.tauHom δ = Fr.tauHom (a • δ) := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_tauHom, Fr.toScheme_tauHom]
  exact (flat_comp _ _).trans (by rw [Fr.chi_smul])

/-- The tangent vector of `a • δ` is `a` times the tangent vector of `δ`. -/
theorem Framing.smul_symm (a : Q D.C R.R) (δ : Fr.Der) :
    (Fr.tangentEquiv.symm δ).smul a = Fr.tangentEquiv.symm (a • δ) := by
  apply Subtype.ext
  change 𝔓.X.map (smulHom R a).op (F.w.app (op (Oₑ R)) (Fr.tauHom δ)) =
    F.w.app (op (Oₑ R)) (Fr.tauHom (a • δ))
  rw [← w_app_comp, Fr.smulHom_tauHom]

/-- **Scalar multiplication in coordinates.** -/
theorem Framing.tangentEquiv_smul (a : Q D.C R.R) (t : 𝔓.Tangents R) :
    Fr.tangentEquiv (t.smul a) = a • Fr.tangentEquiv t := by
  conv_lhs => rw [← Fr.tangentEquiv.symm_apply_apply t]
  rw [Fr.smul_symm, Equiv.apply_symm_apply]

/-! ### Pulling back a framing -/

variable {R' : Alg D} (h : R.R →ₐ[D.A] R'.R)

/-- The pullback of a framing along an algebra map. -/
noncomputable def Framing.pull : Framing F R' where
  red := mO₀ h ≫ Fr.red
  base := mO h ≫ Fr.base
  hred := by rw [w_app_comp, Fr.hred, xR_comp]
  hbase := by rw [v_app_comp, Fr.hbase, yR_comp]
  comm := by rw [← Category.assoc, incl_mO, Category.assoc, Fr.comm, Category.assoc]

/-- The ring map of the factorisation of `x` of a pulled back framing is the original one followed
by `R ⧸ CR → R' ⧸ CR'`. -/
theorem Framing.pull_lS : (Fr.pull h).lS = Fr.lS ≫ CommRingCat.ofHom (qMap D.C h) := by
  change sharp (Spec.map (CommRingCat.ofHom (qMap D.C h)) ≫ Fr.redS) = _
  rw [sharp_specMap_comp, Framing.lS]

/-- The ring map of the factorisation of `y` of a pulled back framing is the original one followed
by `h`. -/
theorem Framing.pull_bS : (Fr.pull h).bS = Fr.bS ≫ CommRingCat.ofHom h.toRingHom := by
  change sharp (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ Fr.baseS) = _
  rw [sharp_specMap_comp, Framing.bS]

/-- The pushforward of a coordinate derivation along an algebra map. -/
noncomputable def Framing.pushDer (δ : Fr.Der) : (Fr.pull h).Der :=
  ⟨(mMap D.C h).comp (δ : F.PW →+ M D.C R.R), fun a b => by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Framing.Der.map_mul, map_add,
      mMap_smul, Fr.pull_lS]
    rfl, fun v => by simp [Framing.Der.map_base]⟩

/-- `pushDer h δ` is `δ` followed by `CR → CR'`. -/
theorem Framing.pushDer_apply (δ : Fr.Der) (a : F.PW) :
    ((Fr.pushDer h δ : (Fr.pull h).Der) : F.PW →+ M D.C R'.R) a =
      mMap D.C h ((δ : F.PW →+ M D.C R.R) a) := rfl

/-- `chi δ` followed by the map induced by `h` is `chi` of the pushforward of `δ`. -/
theorem Framing.chi_eMap (δ : Fr.Der) :
    Fr.chi δ ≫ CommRingCat.ofHom (eMap D.C h) = (Fr.pull h).chi (Fr.pushDer h δ) := by
  ext x
  · simp [Framing.chi, Fr.pull_lS, -map_add]
  · simp [Framing.chi, Framing.pushDer_apply, -map_add]

/-- `tauHom` of the pushforward of `δ` is `tauHom δ` precomposed with `mOₑ h`. -/
theorem Framing.mOₑ_tauHom (δ : Fr.Der) :
    mOₑ h ≫ Fr.tauHom δ = (Fr.pull h).tauHom (Fr.pushDer h δ) := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_tauHom, (Fr.pull h).toScheme_tauHom]
  exact (flat_comp _ _).trans (by rw [Fr.chi_eMap])

/-- **Pulling back tangent vectors, in coordinates.** -/
theorem Framing.pull_symm (δ : Fr.Der) :
    (Fr.tangentEquiv.symm δ).pull h = (Fr.pull h).tangentEquiv.symm (Fr.pushDer h δ) := by
  apply Subtype.ext
  change 𝔓.X.map (mOₑ h).op (F.w.app (op (Oₑ R)) (Fr.tauHom δ)) =
    F.w.app (op (Oₑ R')) ((Fr.pull h).tauHom (Fr.pushDer h δ))
  rw [← w_app_comp, Fr.mOₑ_tauHom]

/-- Pulling back a tangent vector along `h` is pushing forward its coordinate derivation. -/
theorem Framing.tangentEquiv_pull (t : 𝔓.Tangents R) :
    (Fr.pull h).tangentEquiv (t.pull h) = Fr.pushDer h (Fr.tangentEquiv t) := by
  conv_lhs => rw [← Fr.tangentEquiv.symm_apply_apply t]
  rw [Fr.pull_symm, Equiv.apply_symm_apply]

/-- The pushforward of a ring lift along an algebra map. -/
noncomputable def Framing.pushLift (φ : Fr.RingLift) : (Fr.pull h).RingLift :=
  ⟨φ.1 ≫ CommRingCat.ofHom h.toRingHom, by
    rw [Category.assoc, ← CommRingCat.ofHom_comp, ← qMap_comp_mk, CommRingCat.ofHom_comp,
      ← Category.assoc, φ.2.1, Fr.pull_lS], by
    rw [← Category.assoc, φ.2.2, Fr.pull_bS]⟩

/-- `zetaHom` of the pushforward of `φ` is `zetaHom φ` precomposed with `mO h`. -/
theorem Framing.mO_zetaHom (φ : Fr.RingLift) :
    mO h ≫ Fr.zetaHom φ = (Fr.pull h).zetaHom (Fr.pushLift h φ) := by
  apply ext_toScheme
  rw [Functor.map_comp, Fr.toScheme_zetaHom, (Fr.pull h).toScheme_zetaHom]
  exact flat_comp _ _

/-- **Pulling back lifts, in coordinates.** -/
theorem Framing.pullLift_symm (φ : Fr.RingLift) :
    (Fr.liftEquiv.symm φ).pull h = (Fr.pull h).liftEquiv.symm (Fr.pushLift h φ) := by
  apply Subtype.ext
  change 𝔓.X.map (mO h).op (F.w.app (op (O R)) (Fr.zetaHom φ)) =
    F.w.app (op (O R')) ((Fr.pull h).zetaHom (Fr.pushLift h φ))
  rw [← w_app_comp, Fr.mO_zetaHom]

end AlgebraicGeometry.Space.SmoothLift
