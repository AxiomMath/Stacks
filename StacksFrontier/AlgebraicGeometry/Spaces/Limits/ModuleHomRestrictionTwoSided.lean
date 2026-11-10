module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleHomRestriction

/-!
# Restriction of morphisms between inverse images along two morphisms

Let `M` be an `𝒪_{Z₁}`-module, `N` an `𝒪_{Z₂}`-module and `p : P ⟶ Z₁`, `p' : P ⟶ Z₂` two
morphisms of algebraic spaces.  A morphism `x : p^*M ⟶ p'^*N` restricts along `g : Q ⟶ P` to a
morphism `q^*M ⟶ q'^*N` for any `q`, `q'` equal to `g ≫ p`, `g ≫ p'`, through the comparisons of
iterated inverse images of Stacks 03LU.  This is the two-sided form of
`AlgebraicGeometry.Space.moduleHomRestrict`, with the two inverse images allowed to be taken along
different morphisms into different spaces.  It is the language in which the descent data of
Stacks 07V7 are written: their transition maps relate inverse images along the two projections
of a kernel pair, and the identifications of a descent datum with the inverse images of a module
relate inverse images of modules on two different spaces.

## Main definitions

* `AlgebraicGeometry.Space.moduleHomRestrict₂`: the restriction.
* `AlgebraicGeometry.Space.homConjL`: conjugation of a morphism between inverse images along
  composites into a morphism between iterated inverse images.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z₁ Z₂ Z₃ : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS Z₁.1 Z₁.2)
  (N : Modules.{u, u} B S hS Z₂.1 Z₂.2)

/-- The restriction of a morphism `p^*M ⟶ p'^*N` along `g : Q ⟶ P`, as a morphism
`q^*M ⟶ q'^*N` for `q = g ≫ p`, `q' = g ≫ p'`. -/
noncomputable def moduleHomRestrict₂ {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N) :
    (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q').obj N :=
  (pullbackComparison B S hS g p q h M).hom ≫ (modulePullback B S hS g).map x ≫
    (pullbackComparison B S hS g p' q' h' N).inv

variable {M N}

/-- When both inverse images are along the same morphism, `moduleHomRestrict₂` is
`moduleHomRestrict`. -/
theorem moduleHomRestrict₂_self {N : Modules.{u, u} B S hS Z₁.1 Z₁.2} {P Q : AlgebraicSpaces B S hS}
    (g : Q ⟶ P) (p : P ⟶ Z₁) (q : Q ⟶ Z₁) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict₂ M N g p p q q h h x = moduleHomRestrict M N g p q h x := rfl

/-- Along the composites `g ≫ p` and `g ≫ p'`, `moduleHomRestrict₂` is the inverse image along `g`
conjugated by the comparisons `modulePullbackCompIso`. -/
theorem moduleHomRestrict₂_rfl {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N) :
    moduleHomRestrict₂ M N g p p' (g ≫ p) (g ≫ p') rfl rfl x =
      (modulePullbackCompIso B S hS g p).inv.app M ≫ (modulePullback B S hS g).map x ≫
        (modulePullbackCompIso B S hS g p').hom.app N := by
  simp only [moduleHomRestrict₂, pullbackComparison_rfl]
  rfl

/-- Mapping a conjugate by `s^*` and regrouping the comparisons through
`modulePullbackCompIsoAssoc` is conjugating `s^*x` by the comparisons along `s ≫ a`, `s ≫ b`. -/
private theorem map_conj_eq_conj_map {V P Q : AlgebraicSpaces B S hS} (s : Q ⟶ P) (a b : P ⟶ V)
    (f₁ : V ⟶ Z₁) (f₂ : V ⟶ Z₂)
    (x : (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N)) :
    (modulePullbackCompIso B S hS s (a ≫ f₁)).inv.app M ≫
        (modulePullback B S hS s).map ((modulePullbackCompIso B S hS a f₁).inv.app M ≫ x ≫
          (modulePullbackCompIso B S hS b f₂).hom.app N) ≫
        (modulePullbackCompIso B S hS s (b ≫ f₂)).hom.app N =
      (modulePullbackCompIso B S hS (s ≫ a) f₁).inv.app M ≫
        ((modulePullbackCompIso B S hS s a).inv.app ((modulePullback B S hS f₁).obj M) ≫
          (modulePullback B S hS s).map x ≫
          (modulePullbackCompIso B S hS s b).hom.app ((modulePullback B S hS f₂).obj N)) ≫
        (modulePullbackCompIso B S hS (s ≫ b) f₂).hom.app N := by
  have hM := (modulePullbackCompIsoAssoc B S hS).inv_app s a f₁ M
  have hN := (modulePullbackCompIsoAssoc B S hS).hom_app s b f₂ N
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hM, hN]

/-- **Two-sided restriction is functorial.** -/
theorem moduleHomRestrict₂_moduleHomRestrict₂ {P Q R : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (g' : R ⟶ Q) (k : R ⟶ P) (hk : g' ≫ g = k) (p : P ⟶ Z₁) (p' : P ⟶ Z₂) (q : Q ⟶ Z₁)
    (q' : Q ⟶ Z₂) (r : R ⟶ Z₁) (r' : R ⟶ Z₂)
    (h : g ≫ p = q) (h' : g ≫ p' = q') (hr : g' ≫ q = r) (hr' : g' ≫ q' = r')
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N) :
    moduleHomRestrict₂ M N g' q q' r r' hr hr' (moduleHomRestrict₂ M N g p p' q q' h h' x) =
      moduleHomRestrict₂ M N k p p' r r' (by rw [← hk, Category.assoc, h, hr])
        (by rw [← hk, Category.assoc, h', hr']) x := by
  subst hk h h' hr hr'
  rw [moduleHomRestrict₂_rfl, moduleHomRestrict₂_rfl]
  change _ = moduleHomRestrict₂ M N (g' ≫ g) p p' ((g' ≫ g) ≫ p) ((g' ≫ g) ≫ p') rfl rfl x
  rw [moduleHomRestrict₂_rfl]
  have hnat := (modulePullbackCompIso B S hS g' g).hom.naturality x
  simp only [Functor.comp_map] at hnat
  have key := map_conj_eq_conj_map g' g g p p' ((modulePullback B S hS g).map x)
  simp only [Category.assoc] at key ⊢
  rw [key, reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- **Two-sided restriction is compatible with composition.** -/
theorem moduleHomRestrict₂_comp {K : Modules.{u, u} B S hS Z₃.1 Z₃.2} {P Q : AlgebraicSpaces B S hS}
    (g : Q ⟶ P) (p : P ⟶ Z₁) (p' : P ⟶ Z₂) (p'' : P ⟶ Z₃) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂)
    (q'' : Q ⟶ Z₃) (h : g ≫ p = q) (h' : g ≫ p' = q') (h'' : g ≫ p'' = q'')
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N)
    (y : (modulePullback B S hS p').obj N ⟶ (modulePullback B S hS p'').obj K) :
    moduleHomRestrict₂ M K g p p'' q q'' h h'' (x ≫ y) =
      moduleHomRestrict₂ M N g p p' q q' h h' x ≫
        moduleHomRestrict₂ N K g p' p'' q' q'' h' h'' y := by
  simp [moduleHomRestrict₂]

/-- Two-sided restriction sends the identity to the identity. -/
theorem moduleHomRestrict₂_id {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (q : Q ⟶ Z₁) (h : g ≫ p = q) :
    moduleHomRestrict₂ M M g p p q q h h (𝟙 _) = 𝟙 _ := by
  simp [moduleHomRestrict₂]

/-- Two-sided restriction along equal morphisms `g = g'` gives equal results. -/
theorem moduleHomRestrict₂_congr {P Q : AlgebraicSpaces B S hS} {g g' : Q ⟶ P} (e : g = g')
    (p : P ⟶ Z₁) (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N) :
    moduleHomRestrict₂ M N g p p' q q' h h' x =
      moduleHomRestrict₂ M N g' p p' q q' (e ▸ h) (e ▸ h') x := by
  subst e
  rfl

/-- Two-sided restrictions agree when the inverse images agree. -/
theorem moduleHomRestrict₂_eq_iff {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x y : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N) :
    moduleHomRestrict₂ M N g p p' q q' h h' x = moduleHomRestrict₂ M N g p p' q q' h h' y ↔
      (modulePullback B S hS g).map x = (modulePullback B S hS g).map y := by
  unfold moduleHomRestrict₂
  rw [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right]

/-- The restriction of a two-sided isomorphism, as an isomorphism. -/
noncomputable def moduleIsoRestrict₂ {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x : (modulePullback B S hS p).obj M ≅ (modulePullback B S hS p').obj N) :
    (modulePullback B S hS q).obj M ≅ (modulePullback B S hS q').obj N where
  hom := moduleHomRestrict₂ M N g p p' q q' h h' x.hom
  inv := moduleHomRestrict₂ N M g p' p q' q h' h x.inv
  hom_inv_id := by rw [← moduleHomRestrict₂_comp, x.hom_inv_id, moduleHomRestrict₂_id]
  inv_hom_id := by rw [← moduleHomRestrict₂_comp, x.inv_hom_id, moduleHomRestrict₂_id]

/-- The forward morphism of `moduleIsoRestrict₂` is the restriction of the forward morphism. -/
@[simp]
theorem moduleIsoRestrict₂_hom {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x : (modulePullback B S hS p).obj M ≅ (modulePullback B S hS p').obj N) :
    (moduleIsoRestrict₂ g p p' q q' h h' x).hom = moduleHomRestrict₂ M N g p p' q q' h h' x.hom :=
  rfl

/-- The inverse of `moduleIsoRestrict₂` is the restriction of the inverse. -/
@[simp]
theorem moduleIsoRestrict₂_inv {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z₁)
    (p' : P ⟶ Z₂) (q : Q ⟶ Z₁) (q' : Q ⟶ Z₂) (h : g ≫ p = q) (h' : g ≫ p' = q')
    (x : (modulePullback B S hS p).obj M ≅ (modulePullback B S hS p').obj N) :
    (moduleIsoRestrict₂ g p p' q q' h h' x).inv = moduleHomRestrict₂ N M g p' p q' q h' h x.inv :=
  rfl

/-- **Restriction of an inverse image along the same morphism is the inverse image.** -/
theorem moduleHomRestrict₂_map {N : Modules.{u, u} B S hS Z₁.1 Z₁.2} {P Q : AlgebraicSpaces B S hS}
    (g : Q ⟶ P) (p : P ⟶ Z₁) (q : Q ⟶ Z₁) (h : g ≫ p = q) (χ : M ⟶ N) :
    moduleHomRestrict₂ M N g p p q q h h ((modulePullback B S hS p).map χ) =
      (modulePullback B S hS q).map χ :=
  moduleHomRestrict_map g p q h χ

/-- **Restriction of a comparison of iterated inverse images.**  The restriction of the
comparison `fp^*M ⟶ f^*(p^*M)` along `s` is the comparison along `t = s ≫ f`. -/
theorem moduleHomRestrict₂_pullbackComparison_hom {V P T : AlgebraicSpaces B S hS} (f : P ⟶ V)
    (p : V ⟶ Z₁) (fp : P ⟶ Z₁) (hfp : f ≫ p = fp) (s : T ⟶ P) (t : T ⟶ V) (ht : s ≫ f = t)
    (tp : T ⟶ Z₁) (htp : s ≫ fp = tp) (htp' : t ≫ p = tp) :
    moduleHomRestrict₂ M ((modulePullback B S hS p).obj M) s fp f tp t htp ht
        (pullbackComparison B S hS f p fp hfp M).hom =
      (pullbackComparison B S hS t p tp htp' M).hom := by
  subst hfp ht htp
  change _ = (pullbackComparison B S hS (s ≫ f) p ((s ≫ f) ≫ p) rfl M).hom
  rw [moduleHomRestrict₂_rfl, pullbackComparison_rfl, pullbackComparison_rfl]
  have hM := (modulePullbackCompIsoAssoc B S hS).inv_app s f p M
  simp only [Iso.symm_hom, Iso.app_inv]
  rw [reassoc_of% hM, Iso.inv_hom_id_app, Category.comp_id]

/-- The inverse form of `moduleHomRestrict₂_pullbackComparison_hom`. -/
theorem moduleHomRestrict₂_pullbackComparison_inv {V P T : AlgebraicSpaces B S hS} (f : P ⟶ V)
    (p : V ⟶ Z₁) (fp : P ⟶ Z₁) (hfp : f ≫ p = fp) (s : T ⟶ P) (t : T ⟶ V) (ht : s ≫ f = t)
    (tp : T ⟶ Z₁) (htp : s ≫ fp = tp) (htp' : t ≫ p = tp) :
    moduleHomRestrict₂ ((modulePullback B S hS p).obj M) M s f fp t tp ht htp
        (pullbackComparison B S hS f p fp hfp M).inv =
      (pullbackComparison B S hS t p tp htp' M).inv := by
  have e : moduleIsoRestrict₂ s fp f tp t htp ht (pullbackComparison B S hS f p fp hfp M) =
      pullbackComparison B S hS t p tp htp' M :=
    Iso.ext (moduleHomRestrict₂_pullbackComparison_hom f p fp hfp s t ht tp htp htp')
  exact congrArg Iso.inv e

/-- **Two restrictions which agree on a common source agree on everything factoring through
it.** -/
theorem moduleHomRestrict₂_eq_of_factor {Q Q' L T : AlgebraicSpaces B S hS} (lam : L ⟶ Q)
    (θ : L ⟶ Q') (p : Q ⟶ Z₁) (p' : Q ⟶ Z₂) (q : Q' ⟶ Z₁) (q' : Q' ⟶ Z₂) (e : L ⟶ Z₁)
    (e' : L ⟶ Z₂) (h₁ : lam ≫ p = e) (h₂ : lam ≫ p' = e') (h₃ : θ ≫ q = e) (h₄ : θ ≫ q' = e')
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p').obj N)
    (x' : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q').obj N)
    (hx : moduleHomRestrict₂ M N lam p p' e e' h₁ h₂ x =
      moduleHomRestrict₂ M N θ q q' e e' h₃ h₄ x')
    (z : T ⟶ Q) (y : T ⟶ Q') (s : T ⟶ L) (hs : s ≫ lam = z) (hs' : s ≫ θ = y)
    (vz : T ⟶ Z₁) (vz' : T ⟶ Z₂) (hz : z ≫ p = vz) (hz' : z ≫ p' = vz') (hy : y ≫ q = vz)
    (hy' : y ≫ q' = vz') :
    moduleHomRestrict₂ M N z p p' vz vz' hz hz' x =
      moduleHomRestrict₂ M N y q q' vz vz' hy hy' x' := by
  have hse : s ≫ e = vz := by rw [← h₁, ← Category.assoc, hs, hz]
  have hse' : s ≫ e' = vz' := by rw [← h₂, ← Category.assoc, hs, hz']
  rw [← moduleHomRestrict₂_moduleHomRestrict₂ lam s z hs p p' e e' vz vz' h₁ h₂ hse hse' x,
    ← moduleHomRestrict₂_moduleHomRestrict₂ θ s y hs' q q' e e' vz vz' h₃ h₄ hse hse' x', hx]

/-! ### Conjugation into iterated inverse images -/

/-- Conjugation of a morphism between the inverse images of `M` and `N` along `a ≫ f₁` and
`b ≫ f₂` into a morphism between the inverse images along `a` and `b` of `f₁^*M` and `f₂^*N`. -/
noncomputable def homConjL {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f₁ : V ⟶ Z₁)
    (f₂ : V ⟶ Z₂)
    (y : (modulePullback B S hS (a ≫ f₁)).obj M ⟶ (modulePullback B S hS (b ≫ f₂)).obj N) :
    (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N) :=
  (modulePullbackCompIso B S hS a f₁).hom.app M ≫ y ≫ (modulePullbackCompIso B S hS b f₂).inv.app N

/-- The inverse of `homConjL`. -/
noncomputable def homConjLInv {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f₁ : V ⟶ Z₁)
    (f₂ : V ⟶ Z₂)
    (x : (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N)) :
    (modulePullback B S hS (a ≫ f₁)).obj M ⟶ (modulePullback B S hS (b ≫ f₂)).obj N :=
  (modulePullbackCompIso B S hS a f₁).inv.app M ≫ x ≫ (modulePullbackCompIso B S hS b f₂).hom.app N

/-- `homConjLInv` is a left inverse of `homConjL`. -/
theorem homConjLInv_homConjL {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f₁ : V ⟶ Z₁)
    (f₂ : V ⟶ Z₂)
    (y : (modulePullback B S hS (a ≫ f₁)).obj M ⟶ (modulePullback B S hS (b ≫ f₂)).obj N) :
    homConjLInv a b f₁ f₂ (homConjL a b f₁ f₂ y) = y := by
  simp [homConjL, homConjLInv]

/-- `homConjLInv` is a right inverse of `homConjL`. -/
theorem homConjL_homConjLInv {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f₁ : V ⟶ Z₁)
    (f₂ : V ⟶ Z₂)
    (x : (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N)) :
    homConjL a b f₁ f₂ (homConjLInv a b f₁ f₂ x) = x := by
  simp [homConjL, homConjLInv]

/-- `homConjLInv` is compatible with composition. -/
theorem homConjLInv_comp {K : Modules.{u, u} B S hS Z₃.1 Z₃.2} {V P : AlgebraicSpaces B S hS}
    (a b c : P ⟶ V) (f₁ : V ⟶ Z₁) (f₂ : V ⟶ Z₂) (f₃ : V ⟶ Z₃)
    (x : (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N))
    (y : (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N) ⟶
      (modulePullback B S hS c).obj ((modulePullback B S hS f₃).obj K)) :
    homConjLInv a c f₁ f₃ (x ≫ y) = homConjLInv a b f₁ f₂ x ≫ homConjLInv b c f₂ f₃ y := by
  simp [homConjLInv]

/-- `homConjL` is compatible with composition. -/
theorem homConjL_comp {K : Modules.{u, u} B S hS Z₃.1 Z₃.2} {V P : AlgebraicSpaces B S hS}
    (a b c : P ⟶ V) (f₁ : V ⟶ Z₁) (f₂ : V ⟶ Z₂) (f₃ : V ⟶ Z₃)
    (x : (modulePullback B S hS (a ≫ f₁)).obj M ⟶ (modulePullback B S hS (b ≫ f₂)).obj N)
    (y : (modulePullback B S hS (b ≫ f₂)).obj N ⟶ (modulePullback B S hS (c ≫ f₃)).obj K) :
    homConjL a c f₁ f₃ (x ≫ y) = homConjL a b f₁ f₂ x ≫ homConjL b c f₂ f₃ y := by
  simp [homConjL]

/-- `homConjL` sends the identity to the identity. -/
theorem homConjL_id {V P : AlgebraicSpaces B S hS} (a : P ⟶ V) (f : V ⟶ Z₁) :
    homConjL (M := M) (N := M) a a f f (𝟙 _) = 𝟙 _ := by
  simp [homConjL]

/-- If `x ≫ y = 𝟙`, then the conjugates `e₁.hom ≫ x ≫ e₂.inv` and `e₂.hom ≫ y ≫ e₁.inv` compose
to the identity. -/
theorem conj_comp_conj_eq_id {C : Type*} [Category C] {P Q P' Q' : C} (e₁ : P ≅ Q)
    (e₂ : P' ≅ Q') (x : Q ⟶ Q') (y : Q' ⟶ Q) (h : x ≫ y = 𝟙 Q) :
    (e₁.hom ≫ x ≫ e₂.inv) ≫ (e₂.hom ≫ y ≫ e₁.inv) = 𝟙 P := by
  simp [reassoc_of% h]

/-- If `x ≫ y = 𝟙`, then the conjugates satisfy `homConjL a b f f x ≫ homConjL b a f f y = 𝟙`. -/
theorem homConjL_comp_homConjL_eq_id {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f : V ⟶ Z₁)
    (x : (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ f)).obj M)
    (y : (modulePullback B S hS (b ≫ f)).obj M ⟶ (modulePullback B S hS (a ≫ f)).obj M)
    (h : x ≫ y = 𝟙 _) : homConjL a b f f x ≫ homConjL b a f f y = 𝟙 _ :=
  conj_comp_conj_eq_id ((modulePullbackCompIso B S hS a f).app M)
    ((modulePullbackCompIso B S hS b f).app M) x y h

/-- The conjugate of an isomorphism, as an isomorphism. -/
noncomputable def homConjLIso {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f : V ⟶ Z₁)
    (x : (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ f)).obj M)
    (y : (modulePullback B S hS (b ≫ f)).obj M ⟶ (modulePullback B S hS (a ≫ f)).obj M)
    (h₁ : x ≫ y = 𝟙 _) (h₂ : y ≫ x = 𝟙 _) :
    (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ≅
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M) where
  hom := homConjL a b f f x
  inv := homConjL b a f f y
  hom_inv_id := by rw [← homConjL_comp, h₁, homConjL_id]
  inv_hom_id := by rw [← homConjL_comp, h₂, homConjL_id]

/-- `homConjLInv` is injective. -/
theorem homConjLInv_injective {V P : AlgebraicSpaces B S hS} (a b : P ⟶ V) (f₁ : V ⟶ Z₁)
    (f₂ : V ⟶ Z₂) : Function.Injective (homConjLInv (M := M) (N := N) a b f₁ f₂) :=
  fun x y h => by
    rw [← homConjL_homConjLInv a b f₁ f₂ x, h, homConjL_homConjLInv]

/-- **Two-sided restriction commutes with `homConjLInv`**, with flexible targets. -/
theorem homConjLInv_moduleHomRestrict₂ {V P Q : AlgebraicSpaces B S hS} (a b : P ⟶ V)
    (f₁ : V ⟶ Z₁) (f₂ : V ⟶ Z₂) (s : Q ⟶ P) (qa qb : Q ⟶ V) (ha : s ≫ a = qa)
    (hb : s ≫ b = qb)
    (x : (modulePullback B S hS a).obj ((modulePullback B S hS f₁).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f₂).obj N)) :
    homConjLInv qa qb f₁ f₂ (moduleHomRestrict₂ ((modulePullback B S hS f₁).obj M)
        ((modulePullback B S hS f₂).obj N) s a b qa qb ha hb x) =
      moduleHomRestrict₂ M N s (a ≫ f₁) (b ≫ f₂) (qa ≫ f₁) (qb ≫ f₂)
        (by rw [← ha, Category.assoc]) (by rw [← hb, Category.assoc])
        (homConjLInv a b f₁ f₂ x) := by
  subst ha hb
  exact (map_conj_eq_conj_map s a b f₁ f₂ x).symm

/-- **Two-sided restriction commutes with `homConjL`**, with flexible targets. -/
theorem moduleHomRestrict₂_homConjL {V P Q : AlgebraicSpaces B S hS} (a b : P ⟶ V)
    (f₁ : V ⟶ Z₁) (f₂ : V ⟶ Z₂) (s : Q ⟶ P) (qa qb : Q ⟶ V) (ha : s ≫ a = qa)
    (hb : s ≫ b = qb)
    (y : (modulePullback B S hS (a ≫ f₁)).obj M ⟶ (modulePullback B S hS (b ≫ f₂)).obj N) :
    moduleHomRestrict₂ ((modulePullback B S hS f₁).obj M) ((modulePullback B S hS f₂).obj N)
        s a b qa qb ha hb (homConjL a b f₁ f₂ y) =
      homConjL qa qb f₁ f₂ (moduleHomRestrict₂ M N s (a ≫ f₁) (b ≫ f₂) (qa ≫ f₁) (qb ≫ f₂)
        (by rw [← ha, Category.assoc]) (by rw [← hb, Category.assoc]) y) := by
  rw [← homConjL_homConjLInv qa qb f₁ f₂ (moduleHomRestrict₂ _ _ s a b qa qb ha hb _),
    homConjLInv_moduleHomRestrict₂, homConjLInv_homConjL]

end AlgebraicGeometry.Space

end
