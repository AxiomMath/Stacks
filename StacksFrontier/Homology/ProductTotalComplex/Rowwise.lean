module

public import StacksFrontier.Homology.ProductTotalComplex

@[expose] public section

-- The `change` and `rfl` steps through the degree casts `CplxCplx.cast` are checked at default
-- transparency.
set_option backward.isDefEq.respectTransparency false

/-!
# Rowwise quasi-isomorphisms of complexes of complexes

A morphism of complexes of cochain complexes of abelian groups induces a morphism of their
product total complexes.  This file proves that if the morphism is a quasi-isomorphism on
every internal complex, then the induced morphism of product total complexes is a
quasi-isomorphism.

## Main definitions

* `CplxCplx.castTot`: transport of a total-degree term along an equality of degrees.
* `CplxCplx.Hom`: a morphism of complexes of cochain complexes.
* `CplxCplx.Hom.mapTot`: the induced map on product total complexes.
* `CplxCplx.Hom.IsInternalQuasiIso`, `CplxCplx.Hom.IsTotalQuasiIso`: quasi-isomorphy of the
  internal maps, and of the induced total map.

## Main results

* `CplxCplx.Hom.isTotalQuasiIso_of_isInternalQuasiIso` (Stacks Tag 0EYX): a rowwise
  quasi-isomorphism induces a quasi-isomorphism of product total complexes.

## Implementation notes

Quasi-isomorphy is expressed elementwise, by the injectivity and surjectivity conditions on
cohomology classes, matching the concrete additive-group model of totalization in
`StacksFrontier.Homology.ProductTotalComplex`.  The proof compares the two complexes through the
cone of the morphism, whose internal complexes are exact by hypothesis, and exactness of the
internal complexes propagates to the product totalization (Stacks Tag 0H0Q).

## References

* [Stacks Project, Tag 0EYX](https://stacks.math.columbia.edu/tag/0EYX)
-/

/-! ### The internal differential followed by a degree transport -/

namespace CplxCplx

/-- The internal differential followed by the degree transport `A_p^{q+1} ≃+ A_p^{q'}`. -/
def dTo (c : CplxCplx) (p : ℕ) (q q' : ℤ) (h : q + 1 = q') : c.A p q →+ c.A p q' :=
  (c.cast p h).toAddMonoidHom.comp (c.d p q)

/-- The degree transport `A_p^q ≃+ A_p^{q'}` is injective. -/
theorem cast_injective (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q') :
    Function.Injective (c.cast p h) := (c.cast p h).injective

/-- An element is zero exactly when its degree transport is zero. -/
@[simp] theorem cast_eq_zero_iff (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q')
    (x : c.A p q) : c.cast p h x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (c.cast_injective p h)

end CplxCplx

namespace CplxCplx

/-- Reindex a term of a product total complex along an equality of total degrees. -/
public def castTot (c : CplxCplx) {n n' : ℤ} (h : n = n') : c.Tot n →+ c.Tot n' where
  toFun x p := c.cast p (by rw [h]) (x p)
  map_zero' := by
    funext p
    exact map_zero (c.cast p (by rw [h]))
  map_add' x y := by
    funext p
    exact map_add (c.cast p (by rw [h])) (x p) (y p)

/-- A morphism of complexes of cochain complexes of abelian groups. -/
public structure Hom (c c' : CplxCplx) where
  /-- The map `c.A p q ⟶ c'.A p q` in bidegree `(p, q)`. -/
  app : ∀ p q, c.A p q →+ c'.A p q
  /-- The maps commute with the internal differentials. -/
  comm_d : ∀ p q (x : c.A p q),
    app p (q + 1) (c.d p q x) = c'.d p q (app p q x)
  /-- The maps commute with the horizontal differentials. -/
  comm_f : ∀ p q (x : c.A p q),
    app (p + 1) q (c.f p q x) = c'.f p q (app p q x)

namespace Hom

/-- The map on product totalizations induced by a morphism of complexes of complexes. -/
public def mapTot {c c' : CplxCplx} (g : c.Hom c') (n : ℤ) : c.Tot n →+ c'.Tot n where
  toFun x p := g.app p (n - p) (x p)
  map_zero' := by
    funext p
    exact map_zero (g.app p (n - p))
  map_add' x y := by
    funext p
    exact map_add (g.app p (n - p)) (x p) (y p)

/-- The column-`p` component of the image of `x` under the induced map on product
totalizations is the image of `x p` under `g.app p (n - p)`. -/
@[simp]
public theorem mapTot_apply {c c' : CplxCplx} (g : c.Hom c') (n : ℤ) (x : c.Tot n)
    (p : ℕ) : g.mapTot n x p = g.app p (n - p) (x p) := rfl

/-- A morphism is a quasi-isomorphism on every internal complex. The first clause is
surjectivity on cohomology and the second is injectivity. -/
public def IsInternalQuasiIso {c c' : CplxCplx} (g : c.Hom c') : Prop :=
  ∀ p q,
    (∀ z : c'.A p q, c'.d p q z = 0 →
      ∃ x : c.A p q, c.d p q x = 0 ∧
        ∃ w : c'.A p (q - 1),
          g.app p q x + c'.dTo p (q - 1) q (by ring) w = z) ∧
    (∀ x : c.A p q, c.d p q x = 0 →
      (∃ w : c'.A p (q - 1), c'.dTo p (q - 1) q (by ring) w = g.app p q x) →
        ∃ y : c.A p (q - 1), c.dTo p (q - 1) q (by ring) y = x)

/-- A morphism induces a quasi-isomorphism on product total complexes. The first clause is
surjectivity on total cohomology and the second is injectivity. -/
public def IsTotalQuasiIso {c c' : CplxCplx} (g : c.Hom c') : Prop :=
  ∀ n,
    (∀ z : c'.Tot n, c'.totalD n z = 0 →
      ∃ x : c.Tot n, c.totalD n x = 0 ∧
        ∃ w : c'.Tot (n - 1),
          g.mapTot n x + c'.castTot (by ring) (c'.totalD (n - 1) w) = z) ∧
    (∀ x : c.Tot n, c.totalD n x = 0 →
      (∃ w : c'.Tot (n - 1), c'.castTot (by ring) (c'.totalD (n - 1) w) = g.mapTot n x) →
        ∃ y : c.Tot (n - 1), c.castTot (by ring) (c.totalD (n - 1) y) = x)

end Hom

end CplxCplx

/-! ### Mapping cones and degree shifts -/

namespace CplxCplx.RowwiseQuasiIso

open CplxCplx

private def cone {c c' : CplxCplx} (g : c.Hom c') : CplxCplx where
  A p q := c'.A p q × c.A p (q + 1)
  instAb p q := inferInstance
  d p q := {
    toFun := fun x => (c'.d p q x.1 + ((-1 : ℤ) ^ p) • g.app p (q + 1) x.2,
      -c.d p (q + 1) x.2)
    map_zero' := by simp
    map_add' x y := by ext <;> simp [map_add, smul_add, add_comm, add_left_comm, add_assoc] }
  f p q := {
    toFun := fun x => (c'.f p q x.1, -c.f p (q + 1) x.2)
    map_zero' := by simp
    map_add' x y := by ext <;> simp [map_add, add_comm] }
  d_d := by
    intro p q x
    apply Prod.ext
    · change c'.d p (q+1) (c'.d p q x.1 + ((-1 : ℤ)^p) • g.app p (q+1) x.2) +
          ((-1 : ℤ)^p) • g.app p ((q+1)+1) (-c.d p (q+1) x.2) = 0
      rw [map_add, map_zsmul, c'.d_d, zero_add, map_neg, g.comm_d]
      simp
    · change -c.d p ((q+1)+1) (-c.d p (q+1) x.2) = 0
      simp [c.d_d]
  f_f := by
    intro p q x
    apply Prod.ext
    · change c'.f (p+1) q (c'.f p q x.1) = 0
      exact c'.f_f p q x.1
    · change -c.f (p+1) (q+1) (-c.f p (q+1) x.2) = 0
      simp [c.f_f]
  f_d := by
    intro p q x
    apply Prod.ext
    · change c'.d (p+1) q (c'.f p q x.1) +
          ((-1 : ℤ)^(p+1)) • g.app (p+1) (q+1) (-c.f p (q+1) x.2) =
          c'.f p (q+1) (c'.d p q x.1 + ((-1 : ℤ)^p) • g.app p (q+1) x.2)
      rw [c'.f_d, map_add, map_zsmul, map_neg, g.comm_f, pow_succ]
      simp [neg_smul]
    · change -c.d (p+1) (q+1) (-c.f p (q+1) x.2) =
          -c.f p ((q+1)+1) (-c.d p (q+1) x.2)
      simp [c.f_d]

private theorem app_cast {c c' : CplxCplx} (g : c.Hom c') (p : ℕ)
    {q q' : ℤ} (h : q = q') (x : c.A p q) :
    g.app p q' (c.cast p h x) = c'.cast p h (g.app p q x) := by
  cases h
  rfl

/-- Transporting along `q = q'` and then back along `q' = q` is the identity. -/
private theorem cast_cast_self (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q') (h' : q' = q)
    (x : c.A p q) : c.cast p h' (c.cast p h x) = x := by
  rw [c.cast_cast, c.cast_rfl]

private theorem cone_cast_fst {c c' : CplxCplx} (g : c.Hom c') (p : ℕ)
    {q q' : ℤ} (h : q = q') (x : (cone g).A p q) :
    ((cone g).cast p h x).1 = c'.cast p h x.1 := by
  cases h
  rfl

private theorem cone_cast_snd {c c' : CplxCplx} (g : c.Hom c') (p : ℕ)
    {q q' : ℤ} (h : q = q') (x : (cone g).A p q) :
    ((cone g).cast p h x).2 = c.cast p (by rw [h]) x.2 := by
  cases h
  rfl

private theorem cone_d_fst {c c' : CplxCplx} (g : c.Hom c') (p : ℕ) (q : ℤ)
    (x : (cone g).A p q) :
    ((cone g).d p q x).1 =
      c'.d p q x.1 + ((-1 : ℤ) ^ p) • g.app p (q + 1) x.2 := rfl

private theorem cone_d_snd {c c' : CplxCplx} (g : c.Hom c') (p : ℕ) (q : ℤ)
    (x : (cone g).A p q) :
    ((cone g).d p q x).2 = -c.d p (q + 1) x.2 := rfl

private theorem cone_f_fst {c c' : CplxCplx} (g : c.Hom c') (p : ℕ) (q : ℤ)
    (x : (cone g).A p q) :
    ((cone g).f p q x).1 = c'.f p q x.1 := rfl

private theorem cone_f_snd {c c' : CplxCplx} (g : c.Hom c') (p : ℕ) (q : ℤ)
    (x : (cone g).A p q) :
    ((cone g).f p q x).2 = -c.f p (q + 1) x.2 := rfl

private theorem cone_zsmul_fst {c c' : CplxCplx} (g : c.Hom c') (p : ℕ)
    (q : ℤ) (z : ℤ) (x : (cone g).A p q) : (z • x).1 = z • x.1 := rfl

private theorem cone_zsmul_snd {c c' : CplxCplx} (g : c.Hom c') (p : ℕ)
    (q : ℤ) (z : ℤ) (x : (cone g).A p q) : (z • x).2 = z • x.2 := rfl

private theorem neg_one_pow_mul_self (p : ℕ) : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
  rw [← pow_add]
  simp

private theorem cone_snd_lift {c c' : CplxCplx} (g : c.Hom c')
    (hg : g.IsInternalQuasiIso) (p : ℕ) (q : ℤ)
    (z : (cone g).A p q) (hz : (cone g).d p q z = 0) :
    ∃ t : c.A p q, c.d p q t = z.2 := by
  let s : ℤ := (-1) ^ p
  have hss : s * s = 1 := neg_one_pow_mul_self p
  have hb : c'.d p q z.1 + s • g.app p (q + 1) z.2 = 0 := congrArg Prod.fst hz
  have ha : c.d p (q + 1) z.2 = 0 := by
    have h := congrArg Prod.snd hz
    change -c.d p (q+1) z.2 = 0 at h
    exact neg_eq_zero.mp h
  have hb' : s • g.app p (q + 1) z.2 = -c'.d p q z.1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hb
  have hboundary : ∃ w : c'.A p (q + 1 - 1),
      c'.dTo p (q + 1 - 1) (q + 1) (by ring) w = g.app p (q + 1) z.2 := by
    refine ⟨c'.cast p (by ring) ((-s) • z.1), ?_⟩
    simp only [dTo, AddMonoidHom.coe_comp, Function.comp_apply, c'.d_cast,
      map_zsmul, c'.cast_cast, c'.cast_rfl, AddEquiv.coe_toAddMonoidHom]
    calc
      (-s) • c'.d p q z.1 = s • (s • g.app p (q + 1) z.2) := by
        rw [hb', smul_neg, neg_smul]
      _ = g.app p (q + 1) z.2 := by rw [smul_smul, hss, one_smul]
  obtain ⟨t₀, ht₀⟩ := (hg p (q + 1)).2 z.2 ha hboundary
  refine ⟨c.cast p (by ring) t₀, ?_⟩
  rw [c.d_cast]
  simpa only [dTo, AddMonoidHom.coe_comp, Function.comp_apply, c.cast_cast,
    c.cast_rfl, AddEquiv.coe_toAddMonoidHom] using ht₀

private theorem cone_internal_exact {c c' : CplxCplx} (g : c.Hom c')
    (hg : g.IsInternalQuasiIso) (p : ℕ) (q : ℤ)
    (z : (cone g).A p q) (hz : (cone g).d p q z = 0) :
    ∃ w : (cone g).A p (q - 1),
      (cone g).dTo p (q - 1) q (by ring) w = z := by
  obtain ⟨t, ht'⟩ := cone_snd_lift g hg p q z hz
  let s : ℤ := (-1) ^ p
  have hss : s * s = 1 := neg_one_pow_mul_self p
  have hb : c'.d p q z.1 + s • g.app p (q + 1) z.2 = 0 := congrArg Prod.fst hz
  let r : c'.A p q := z.1 + s • g.app p q t
  have hr : c'.d p q r = 0 := by
    dsimp [r]
    rw [map_add, map_zsmul, ← g.comm_d, ht']
    exact hb
  obtain ⟨x, hx, w, hw⟩ := (hg p q).1 r hr
  have hw' : g.app p q x + c'.dTo p (q-1) q (by ring) w = r := hw
  refine ⟨(w, c.cast p (by ring) (-t + s • x)), ?_⟩
  apply Prod.ext
  · show ((cone g).cast p (by ring)
        ((cone g).d p (q-1) (w, c.cast p (by ring) (-t+s • x)))).1 = z.1
    rw [cone_cast_fst]
    show c'.cast p (by ring)
        (c'.d p (q-1) w + s • g.app p ((q-1)+1)
          (c.cast p (by ring) (-t + s • x))) = z.1
    rw [map_add, map_zsmul, app_cast, c'.cast_cast,
      show c'.cast p (show (q-1)+1 = q by ring)
        (c'.d p (q-1) w) = c'.dTo p (q-1) q (by ring) w from rfl,
      c'.cast_rfl, map_add, map_neg, map_zsmul, smul_add, smul_neg, smul_smul, hss,
      one_smul]
    dsimp [r] at hw'
    calc
      _ = (g.app p q x + c'.dTo p (q-1) q (by ring) w) - s • g.app p q t := by abel
      _ = z.1 := by rw [hw']; abel
  · show ((cone g).cast p (by ring)
        ((cone g).d p (q-1) (w, c.cast p (by ring) (-t+s • x)))).2 = z.2
    rw [cone_cast_snd]
    show c.cast p (by ring)
        (-c.d p ((q-1)+1) (c.cast p (by ring) (-t + s • x))) = z.2
    rw [c.d_cast, map_neg, map_add, map_neg, map_zsmul, hx, smul_zero]
    simp only [add_zero]
    rw [ht', c.cast_cast, c.cast_rfl]
    simp

private def shift (c : CplxCplx) (n : ℤ) : CplxCplx where
  A p q := c.A p (q + n)
  instAb p q := inferInstance
  d p q := (c.cast p (by ring)).toAddMonoidHom.comp (c.d p (q+n))
  f p q := c.f p (q+n)
  d_d := by
    intro p q x
    change c.cast p (by ring) (c.d p ((q+1)+n)
      (c.cast p (by ring) (c.d p (q+n) x))) = 0
    rw [c.d_cast, c.cast_cast, c.d_d, map_zero]
  f_f := by
    intro p q x
    change c.f (p+1) (q+n) (c.f p (q+n) x) = 0
    exact c.f_f p (q+n) x
  f_d := by
    intro p q x
    change c.cast (p+1) (by ring) (c.d (p+1) (q+n) (c.f p (q+n) x)) =
      c.f p ((q+1)+n) (c.cast p (by ring) (c.d p (q+n) x))
    rw [c.f_d, c.f_cast]

private theorem shift_cast (c : CplxCplx) (n : ℤ) (p : ℕ)
    {q q' : ℤ} (h : q = q') (x : (shift c n).A p q) :
    (shift c n).cast p h x = c.cast p (by rw [h]) x := by
  cases h
  rfl

private theorem shift_d (c : CplxCplx) (n : ℤ) (p : ℕ) (q : ℤ)
    (x : (shift c n).A p q) :
    (shift c n).d p q x = c.cast p (by ring) (c.d p (q+n) x) := rfl

private theorem shift_f (c : CplxCplx) (n : ℤ) (p : ℕ) (q : ℤ)
    (x : (shift c n).A p q) :
    (shift c n).f p q x = c.f p (q+n) x := rfl

private def shiftTot (c : CplxCplx) (n k : ℤ) :
    c.Tot (k+n) →+ (shift c n).Tot k where
  toFun x p := c.cast p (by ring) (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

private theorem shiftTot_apply (c : CplxCplx) (n k : ℤ) (x : c.Tot (k + n))
    (p : ℕ) : shiftTot c n k x p = c.cast p (by ring) (x p) := rfl

private def unshiftTot (c : CplxCplx) (n k : ℤ) :
    (shift c n).Tot k →+ c.Tot (k+n) where
  toFun x p := c.cast p (by ring) (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

private theorem unshift_shiftTot (c : CplxCplx) (n k : ℤ) (x : c.Tot (k + n)) :
    unshiftTot c n k (shiftTot c n k x) = x := by
  funext p
  exact cast_cast_self c p _ _ (x p)

private theorem shift_unshiftTot (c : CplxCplx) (n k : ℤ) (x : (shift c n).Tot k) :
    shiftTot c n k (unshiftTot c n k x) = x := by
  funext p
  exact cast_cast_self c p _ _ (x p)

private theorem shiftTot_D (c : CplxCplx) (n k : ℤ) (x : c.Tot (k + n)) :
    (shift c n).totalD k (shiftTot c n k x) =
      shiftTot c n (k+1) (c.castTot (by ring) (c.totalD (k+n) x)) := by
  funext p
  cases p with
  | zero =>
    show (shift c n).totalD k (shiftTot c n k x) 0 =
      c.cast 0 (by ring) (c.cast 0 (by ring) (c.totalD (k+n) x 0))
    rw [totalD_apply_zero, totalD_apply_zero, dPartHom_apply, dPartHom_apply]
    rw [shift_cast, shift_d, shiftTot_apply]
    show c.cast 0 (show (k-(0:ℕ)+1)+n = (k+1-(0:ℕ))+n by ring) (((-1:ℤ)^0) •
      c.cast 0 (show (k-(0:ℕ))+n+1 = (k-(0:ℕ)+1)+n by ring)
        (c.d 0 ((k-(0:ℕ))+n)
          (c.cast 0 (show (k+n)-(0:ℕ) = (k-(0:ℕ))+n by ring) (x 0)))) =
      c.cast 0 (show ((k+1)+n)-(0:ℕ) = (k+1-(0:ℕ))+n by ring)
        (c.cast 0 (show (k+n+1)-(0:ℕ) = ((k+1)+n)-(0:ℕ) by ring)
          (c.cast 0 (show (k+n)-(0:ℕ)+1 = (k+n+1)-(0:ℕ) by ring)
            (((-1:ℤ)^0) • c.d 0 ((k+n)-(0:ℕ)) (x 0))))
    simp only [pow_zero, one_smul, c.d_cast, c.cast_cast]
  | succ p =>
    show (shift c n).totalD k (shiftTot c n k x) (p+1) =
      c.cast (p+1) (by ring) (c.cast (p+1) (by ring) (c.totalD (k+n) x (p+1)))
    rw [totalD_apply_succ, totalD_apply_succ, dPartHom_apply, dPartHom_apply,
      fPartHom_apply, fPartHom_apply]
    rw [shift_cast, shift_d, shiftTot_apply, shift_cast, shift_f, shiftTot_apply]
    simp only [map_add, map_zsmul, c.d_cast, c.f_cast, c.cast_cast]

private theorem D_castTot (c : CplxCplx) {n n' : ℤ} (h : n = n')
    (x : c.Tot n) :
    c.totalD n' (c.castTot h x) = c.castTot (by rw [h]) (c.totalD n x) := by
  cases h
  funext p
  show c.totalD n (fun p => c.cast p rfl (x p)) p = c.cast p rfl (c.totalD n x p)
  simp

private theorem castTot_castTot (c : CplxCplx) {n n' n'' : ℤ}
    (h : n = n') (h' : n' = n'') (x : c.Tot n) :
    c.castTot h' (c.castTot h x) = c.castTot (h.trans h') x := by
  cases h
  cases h'
  rfl

private theorem castTot_rfl (c : CplxCplx) (n : ℤ) (x : c.Tot n) :
    c.castTot rfl x = x := by
  funext p
  exact c.cast_rfl p (x p)

/-- Transporting the differential of a transported element gives the differential. -/
private theorem castTot_D_castTot (c : CplxCplx) {m m' : ℤ} (h : m = m') (h' : m' + 1 = m + 1)
    (w : c.Tot m) : c.castTot h' (c.totalD m' (c.castTot h w)) = c.totalD m w := by
  cases h
  rw [castTot_rfl, castTot_rfl]

private theorem shift_internal_exact (c : CplxCplx) (n : ℤ)
    (hH : ∀ p q (z : c.A p q), c.d p q z = 0 →
      ∃ w : c.A p (q - 1), c.dTo p (q - 1) q (by ring) w = z) (p : ℕ) :
    (shift c n).InternalCohomologyVanishes p := by
  intro z hz
  have hz' : c.d p (-(p:ℤ)+n) z = 0 := by
    rw [shift_d] at hz
    exact (c.cast_eq_zero_iff p _ _).mp hz
  obtain ⟨w, hw⟩ := hH p (-(p:ℤ)+n) z hz'
  refine ⟨c.cast p (by ring) w, ?_⟩
  show (shift c n).cast p (by ring)
    ((shift c n).d p (-(p:ℤ)-1) (c.cast p (by ring) w)) = z
  rw [shift_cast, shift_d, c.d_cast, c.cast_cast, c.cast_cast]
  exact hw

private theorem total_exact (c : CplxCplx)
    (hH : ∀ p q (z : c.A p q), c.d p q z = 0 →
      ∃ w : c.A p (q - 1), c.dTo p (q - 1) q (by ring) w = z)
    (n : ℤ) (x : c.Tot n) (hx : c.totalD n x = 0) :
    ∃ y : c.Tot (n-1), c.castTot (by ring) (c.totalD (n-1) y) = x := by
  let x₀ : c.Tot (0+n) := c.castTot (by ring) x
  have hx₀ : c.totalD (0+n) x₀ = 0 := by
    dsimp [x₀]
    rw [D_castTot, hx, map_zero]
  have hxs : (shift c n).totalD 0 (shiftTot c n 0 x₀) = 0 := by
    rw [shiftTot_D, hx₀, map_zero, map_zero]
  obtain ⟨ys, hys⟩ := (shift c n).total_H0_eq_zero
    (shift_internal_exact c n hH) (shiftTot c n 0 x₀) hxs
  let y₀ : c.Tot ((-1)+n) := unshiftTot c n (-1) ys
  have hys' : c.castTot (by ring) (c.totalD ((-1)+n) y₀) = x₀ := by
    have h := shiftTot_D c n (-1) y₀
    rw [shift_unshiftTot] at h
    have h' : shiftTot c n 0 (c.castTot (by ring) (c.totalD ((-1)+n) y₀)) =
        shiftTot c n 0 x₀ := h.symm.trans hys
    exact Function.LeftInverse.injective (unshift_shiftTot c n 0) h'
  refine ⟨c.castTot (by ring) y₀, ?_⟩
  rw [D_castTot]
  have h := congrArg (c.castTot (show 0 + n = n by ring)) hys'
  simpa only [castTot_castTot, castTot_rfl, x₀] using h

private def coneFst {c c' : CplxCplx} (g : c.Hom c') (n : ℤ) :
    (cone g).Tot n →+ c'.Tot n where
  toFun x p := (x p).1
  map_zero' := rfl
  map_add' _ _ := rfl

private def coneSnd {c c' : CplxCplx} (g : c.Hom c') (n : ℤ) :
    (cone g).Tot n →+ c.Tot (n + 1) where
  toFun x p := c.cast p (by ring) (x p).2
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

private theorem coneFst_apply {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (x : (cone g).Tot n) (p : ℕ) : coneFst g n x p = (x p).1 := rfl

private theorem coneSnd_apply {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (x : (cone g).Tot n) (p : ℕ) :
    coneSnd g n x p = c.cast p (by ring) (x p).2 := rfl

private def conePair {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (b : c'.Tot n) (a : c.Tot (n + 1)) : (cone g).Tot n :=
  fun p => (b p, c.cast p (by ring) (a p))

private theorem coneFst_pair {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (b : c'.Tot n) (a : c.Tot (n + 1)) :
    coneFst g n (conePair g n b a) = b := rfl

private theorem coneSnd_pair {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (b : c'.Tot n) (a : c.Tot (n + 1)) :
    coneSnd g n (conePair g n b a) = a := by
  funext p
  exact cast_cast_self c p _ _ (a p)

private theorem conePair_fst_snd {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (x : (cone g).Tot n) :
    conePair g n (coneFst g n x) (coneSnd g n x) = x := by
  funext p
  apply Prod.ext
  · rfl
  · exact cast_cast_self c p _ _ (x p).2

private theorem coneFst_D {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (x : (cone g).Tot n) :
    coneFst g (n + 1) ((cone g).totalD n x) =
      c'.totalD n (coneFst g n x) + g.mapTot (n + 1) (coneSnd g n x) := by
  funext p
  cases p with
  | zero =>
    rw [Pi.add_apply, coneFst_apply, totalD_apply_zero, dPartHom_apply,
      Hom.mapTot_apply]
    rw [cone_cast_fst]
    simp only [pow_zero, one_smul, cone_d_fst]
    rw [totalD_apply_zero, dPartHom_apply, coneFst_apply, coneSnd_apply]
    simp only [pow_zero, one_smul, map_add, app_cast]
  | succ p =>
    rw [Pi.add_apply, coneFst_apply, totalD_apply_succ, dPartHom_apply,
      fPartHom_apply, Hom.mapTot_apply]
    rw [Prod.fst_add, cone_cast_fst, cone_cast_fst]
    simp only [cone_zsmul_fst, cone_d_fst, cone_f_fst]
    rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply, coneFst_apply,
      coneFst_apply, coneSnd_apply]
    rw [smul_add, smul_smul]
    rw [neg_one_pow_mul_self, one_smul, map_add, app_cast]
    abel

private theorem coneSnd_D {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (x : (cone g).Tot n) :
    coneSnd g (n + 1) ((cone g).totalD n x) =
      -c.totalD (n + 1) (coneSnd g n x) := by
  funext p
  cases p with
  | zero =>
    rw [Pi.neg_apply, coneSnd_apply, totalD_apply_zero, dPartHom_apply]
    rw [cone_cast_snd]
    simp only [cone_zsmul_snd, cone_d_snd]
    rw [totalD_apply_zero, dPartHom_apply, coneSnd_apply]
    simp only [pow_zero, one_smul, c.d_cast, map_neg, c.cast_cast]
  | succ p =>
    rw [Pi.neg_apply, coneSnd_apply, totalD_apply_succ, dPartHom_apply,
      fPartHom_apply]
    rw [Prod.snd_add, map_add, cone_cast_snd, cone_cast_snd]
    simp only [cone_zsmul_snd, cone_d_snd, cone_f_snd]
    rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply, coneSnd_apply,
      coneSnd_apply]
    rw [c.d_cast, c.f_cast]
    simp only [map_neg, map_zsmul, c.cast_cast]
    simp only [smul_neg]
    abel

private theorem conePair_D {c c' : CplxCplx} (g : c.Hom c') (n : ℤ)
    (b : c'.Tot n) (a : c.Tot (n + 1)) :
    (cone g).totalD n (conePair g n b a) =
      conePair g (n + 1) (c'.totalD n b + g.mapTot (n + 1) a) (-c.totalD (n + 1) a) := by
  calc
    _ = conePair g (n + 1)
          (coneFst g (n + 1) ((cone g).totalD n (conePair g n b a)))
          (coneSnd g (n + 1) ((cone g).totalD n (conePair g n b a))) :=
            (conePair_fst_snd g (n + 1) _).symm
    _ = _ := by rw [coneFst_D, coneSnd_D, coneFst_pair, coneSnd_pair]

private theorem conePair_zero {c c' : CplxCplx} (g : c.Hom c') (n : ℤ) :
    conePair g n 0 0 = 0 := by
  funext p
  exact Prod.ext rfl (map_zero (c.cast p (by ring)))

private theorem total_exact_succ (c : CplxCplx)
    (hH : ∀ p q (z : c.A p q), c.d p q z = 0 →
      ∃ w : c.A p (q - 1), c.dTo p (q - 1) q (by ring) w = z)
    (m : ℤ) (x : c.Tot (m + 1)) (hx : c.totalD (m + 1) x = 0) :
    ∃ y : c.Tot m, c.totalD m y = x := by
  obtain ⟨y, hy⟩ := total_exact c hH (m + 1) x hx
  refine ⟨c.castTot (by ring) y, ?_⟩
  rwa [D_castTot]

private theorem total_quasiIso_at_succ {c c' : CplxCplx} (g : c.Hom c')
    (hg : g.IsInternalQuasiIso) (m : ℤ) :
    (∀ z : c'.Tot (m + 1), c'.totalD (m + 1) z = 0 →
      ∃ x : c.Tot (m + 1), c.totalD (m + 1) x = 0 ∧
        ∃ w : c'.Tot m, g.mapTot (m + 1) x + c'.totalD m w = z) ∧
    (∀ x : c.Tot (m + 1), c.totalD (m + 1) x = 0 →
      (∃ w : c'.Tot m, c'.totalD m w = g.mapTot (m + 1) x) →
        ∃ y : c.Tot m, c.totalD m y = x) := by
  constructor
  · intro z hz
    have hv : (cone g).totalD (m + 1) (conePair g (m + 1) z 0) = 0 := by
      simp only [conePair_D, hz, map_zero, add_zero, neg_zero, conePair_zero]
    obtain ⟨t, ht⟩ := total_exact_succ (cone g) (cone_internal_exact g hg)
      m (conePair g (m + 1) z 0) hv
    have ha : c.totalD (m + 1) (coneSnd g m t) = 0 := by
      simpa only [coneSnd_D, coneSnd_pair, neg_eq_zero] using congrArg (coneSnd g (m + 1)) ht
    have hb : c'.totalD m (coneFst g m t) + g.mapTot (m + 1) (coneSnd g m t) = z := by
      simpa only [coneFst_D, coneFst_pair] using congrArg (coneFst g (m + 1)) ht
    exact ⟨coneSnd g m t, ha, coneFst g m t, (add_comm _ _).trans hb⟩
  · intro x hx ⟨w, hw⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = k + 1 := ⟨m - 1, by ring⟩
    have hv : (cone g).totalD (k + 1) (conePair g (k + 1) (-w) x) = 0 := by
      rw [conePair_D]
      have hb : c'.totalD (k + 1) (-w) + g.mapTot ((k + 1) + 1) x = 0 := by
        rw [map_neg, ← hw]
        exact neg_add_cancel _
      have ha : -c.totalD ((k + 1) + 1) x = 0 := by rw [hx, neg_zero]
      rw [hb, ha, conePair_zero]
    obtain ⟨t, ht⟩ := total_exact_succ (cone g) (cone_internal_exact g hg)
      k (conePair g (k + 1) (-w) x) hv
    have ha : -c.totalD (k + 1) (coneSnd g k t) = x := by
      simpa only [coneSnd_D, coneSnd_pair] using congrArg (coneSnd g (k + 1)) ht
    exact ⟨-coneSnd g k t, by rwa [map_neg]⟩

end CplxCplx.RowwiseQuasiIso

namespace CplxCplx.Hom

open CplxCplx.RowwiseQuasiIso CplxCplx

/-- A morphism between complexes of cochain complexes
which is a quasi-isomorphism on every internal complex induces a quasi-isomorphism between
their product total complexes. -/
@[stacks 0EYX]
theorem isTotalQuasiIso_of_isInternalQuasiIso {c c' : CplxCplx} (g : CplxCplx.Hom c c')
    (hg : g.IsInternalQuasiIso) : g.IsTotalQuasiIso := by
  intro n
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  rcases total_quasiIso_at_succ g hg m with ⟨hsurj, hinj⟩
  refine ⟨fun z hz => ?_, fun x hx ⟨w, hw⟩ => ?_⟩
  · obtain ⟨x, hx, w, hw⟩ := hsurj z hz
    refine ⟨x, hx, c'.castTot (by ring) w, ?_⟩
    rwa [castTot_D_castTot]
  · obtain ⟨y, hy⟩ := hinj x hx ⟨c'.castTot (by ring) w, by rwa [D_castTot]⟩
    refine ⟨c.castTot (by ring) y, ?_⟩
    rwa [castTot_D_castTot]

end CplxCplx.Hom

end
