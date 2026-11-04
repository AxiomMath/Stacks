module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints

/-!
# Stalks of a module on a scheme, and rank-one trivializations

Let `X` be a scheme and `L` an `𝒪_X`-module. The stalk `L_x` is a module over the local ring
`𝒪_{X, x}`; the germ map is semilinear over the germ map of the structure sheaf, and so is the
specialization map `L_y → L_x` attached to a specialization `x ⤳ y`.

A *stalk basis* of `L` at `x` is an element `m ∈ L_x` with `r ↦ r • m` a bijection
`𝒪_{X, x} → L_x`, that is, a basis of the free rank-one module `L_x`; and `L` is *trivialized
near* `x` when some open neighbourhood of `x` carries a section whose germ at every one of its
points is a stalk basis there. That is local freeness of rank one read on stalks; an
invertible module satisfies it at every point. A section `e` of `L` over `W` such that
`c ↦ c • e|_V` is bijective on sections over every open `V ≤ W` trivializes `L` near every point
of `W`.

## Main definitions

* `Stacks.Divisors.IsStalkBasis` — an element of `L_x` by which multiplication is a bijection
  `𝒪_{X, x} → L_x`.
* `Stacks.Divisors.IsTrivializedNear` — `L` has a section near `x` whose germs are stalk bases.

## Main results

* `AlgebraicGeometry.Scheme.Modules.stalkSpecializes_smul` — the specialization map of the
  stalks of `L` is semilinear over the specialization map of the structure sheaf.
* `AlgebraicGeometry.Scheme.ord_algebraMap_of_isUnit` — the order of vanishing of the image in
  the function field of a unit of a local ring is zero.
* `Stacks.Divisors.exists_isUnit_smul_eq` — two stalk bases at the same point differ by a unit.
* `Stacks.Divisors.isTrivializedNear_of_bijective_smul` — a section by which multiplication is
  bijective on sections over every smaller open trivializes `L` near every point of its domain.
* `Stacks.Divisors.isTrivializedNear_unit` — the structure sheaf is trivialized everywhere.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (L : X.Modules)

/-- The germ map of an `𝒪_X`-module is semilinear over the germ map of the structure sheaf. -/
theorem germ_smul {U : X.Opens} {y : X} (hy : y ∈ U) (r : Γ(X, U)) (t : Γ(L, U)) :
    L.presheaf.germ U y hy (r • t) = X.presheaf.germ U y hy r • L.presheaf.germ U y hy t :=
  PresheafOfModules.germ_smul L.val y U hy r t

/-- The specialization map on the stalks of an `𝒪_X`-module is semilinear over the
specialization map on the stalks of the structure sheaf. -/
theorem stalkSpecializes_smul {x y : X} (h : x ⤳ y) (r : X.presheaf.stalk y)
    (m : L.presheaf.stalk y) :
    L.presheaf.stalkSpecializes h (r • m) =
      X.presheaf.stalkSpecializes h r • L.presheaf.stalkSpecializes h m := by
  obtain ⟨U, hyU, ρ, hρ⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hyV, t, ht⟩ := L.presheaf.exists_le_germ_eq m hyU
  have hρ' : X.presheaf.germ V y hyV (X.presheaf.map (homOfLE hVU).op ρ) = r := by
    rw [← hρ]; exact X.presheaf.germ_res_apply _ y hyV ρ
  rw [← ht, ← hρ', ← germ_smul L hyV, TopCat.Presheaf.germ_stalkSpecializes_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    germ_smul L]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The order of vanishing of the image in the function field of a unit of the local ring at a
point of codimension one is zero. This is the stalkwise form of
`AlgebraicGeometry.Scheme.ord_of_isUnit`. -/
theorem ord_algebraMap_of_isUnit {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {ξ : X} (hξ : coheight ξ = 1) {u : X.presheaf.stalk ξ} (hu : IsUnit u) :
    X.ord (algebraMap (X.presheaf.stalk ξ) X.functionField u) ξ = 0 := by
  have h0 : algebraMap (X.presheaf.stalk ξ) X.functionField u ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective (X.presheaf.stalk ξ) X.functionField)).mpr hu.ne_zero
  rw [Scheme.ord_eq_iff hξ h0]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk ξ) := krullDimLE_of_coheight_le hξ.le
  show Ring.ordFrac (X.presheaf.stalk ξ) _ = _
  rw [Ring.ordFrac_of_isUnit hu]
  simp

end AlgebraicGeometry.Scheme

namespace Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)

/-! ### Stalk bases -/

/-- `m` is a **stalk basis** of the `𝒪_X`-module `L` at `x` when multiplication by `m` is a
bijection `𝒪_{X, x} → L_x`, that is, when `m` is a basis of the free rank-one
`𝒪_{X, x}`-module `L_x`. -/
def IsStalkBasis (x : X) (m : L.presheaf.stalk x) : Prop :=
  Function.Bijective fun r : X.presheaf.stalk x => r • m

variable {L}

/-- Two stalk bases at the same point differ by a unit of the local ring. -/
theorem exists_isUnit_smul_eq {x : X} {m m' : L.presheaf.stalk x} (hm : IsStalkBasis L x m)
    (hm' : IsStalkBasis L x m') : ∃ u : X.presheaf.stalk x, IsUnit u ∧ m' = u • m := by
  obtain ⟨u, hu⟩ := hm.surjective m'
  obtain ⟨v, hv⟩ := hm'.surjective m
  replace hu : u • m = m' := hu
  replace hv : v • m' = m := hv
  have huv : u * v = 1 := by
    refine hm.injective ?_
    rw [mul_comm, mul_smul, hu, hv, one_smul]
  exact ⟨u, .of_mul_eq_one v huv, hu.symm⟩

/-- A unit multiple of a stalk basis is a stalk basis. -/
theorem IsStalkBasis.smul_of_isUnit {x : X} {m : L.presheaf.stalk x} (hm : IsStalkBasis L x m)
    {u : X.presheaf.stalk x} (hu : IsUnit u) : IsStalkBasis L x (u • m) := by
  obtain ⟨w, huw, hwu⟩ := isUnit_iff_exists.mp hu
  refine ⟨fun r r' hrr' => ?_, fun n => ?_⟩
  · replace hrr' : r • u • m = r' • u • m := hrr'
    rw [smul_smul, smul_smul] at hrr'
    exact hu.mul_left_inj.mp (hm.injective hrr')
  · obtain ⟨r, hr⟩ := hm.surjective n
    replace hr : r • m = n := hr
    refine ⟨r * w, ?_⟩
    show (r * w) • u • m = n
    rwa [smul_smul, mul_assoc, hwu, mul_one]

/-! ### Local trivializations -/

/-- `L` is **trivialized near** `x` when some open neighbourhood `W` of `x` carries a section of
`L` whose germ at every point of `W` is a stalk basis there. -/
def IsTrivializedNear (L : X.Modules) (x : X) : Prop :=
  ∃ W : X.Opens, x ∈ W ∧ ∃ t : Γ(L, W),
    ∀ (y : X) (hy : y ∈ W), IsStalkBasis L y (L.presheaf.germ W y hy t)

/-- A section `e` of `L` over `W` such that `c ↦ c • e|_V` is a bijection
`Γ(X, V) → Γ(L, V)` for every open `V ≤ W` has a stalk basis for its germ at every point of
`W`. -/
theorem isStalkBasis_germ_of_bijective_smul {W : X.Opens} (e : Γ(L, W))
    (h : ∀ V : X.Opens, ∀ hV : V ≤ W,
      Function.Bijective fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op e)
    (y : X) (hy : y ∈ W) : IsStalkBasis L y (L.presheaf.germ W y hy e) := by
  constructor
  · intro r r' hrr'
    replace hrr' : r • L.presheaf.germ W y hy e = r' • L.presheaf.germ W y hy e := hrr'
    obtain ⟨U, hUW, hyU, c, hc⟩ := X.presheaf.exists_le_germ_eq r hy
    obtain ⟨V, hVU, hyV, d', hd'⟩ := X.presheaf.exists_le_germ_eq r' hyU
    have hVW : V ≤ W := hVU.trans hUW
    set d : Γ(X, V) := X.presheaf.map (homOfLE hVU).op c with hd
    have hdr : X.presheaf.germ V y hyV d = r := by
      rw [hd, X.presheaf.germ_res_apply _ y hyV c]; exact hc
    have key : L.presheaf.germ V y hyV (d • L.presheaf.map (homOfLE hVW).op e) =
        L.presheaf.germ V y hyV (d' • L.presheaf.map (homOfLE hVW).op e) := by
      rw [Scheme.Modules.germ_smul L hyV, Scheme.Modules.germ_smul L hyV,
        L.presheaf.germ_res_apply _ y hyV e, hdr, hd']
      exact hrr'
    obtain ⟨V', hyV', iV, iV', hV'⟩ := L.presheaf.germ_eq y hyV hyV _ _ key
    cases Subsingleton.elim iV iV'
    have hV'W : V' ≤ W := le_trans (leOfHom iV) hVW
    have hres : ∀ f : Γ(X, V), L.presheaf.map iV.op (f • L.presheaf.map (homOfLE hVW).op e) =
        X.presheaf.map iV.op f • L.presheaf.map (homOfLE hV'W).op e := by
      intro f
      rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hres, hres] at hV'
    have := h V' hV'W |>.injective hV'
    rw [← hdr, ← hd', ← X.presheaf.germ_res_apply iV y hyV' d,
      ← X.presheaf.germ_res_apply iV y hyV' d', this]
  · intro m
    obtain ⟨V, hVW, hyV, g, hg⟩ := L.presheaf.exists_le_germ_eq m hy
    obtain ⟨c, hc⟩ := h V hVW |>.surjective g
    replace hc : c • L.presheaf.map (homOfLE hVW).op e = g := hc
    refine ⟨X.presheaf.germ V y hyV c, ?_⟩
    show X.presheaf.germ V y hyV c • L.presheaf.germ W y hy e = m
    rw [← L.presheaf.germ_res_apply (homOfLE hVW) y hyV e, ← Scheme.Modules.germ_smul L hyV, hc,
      hg]

/-- A section by which multiplication is bijective on sections over every smaller open
trivializes `L` near every point of its domain. -/
theorem isTrivializedNear_of_bijective_smul {W : X.Opens} {x : X} (hx : x ∈ W) (e : Γ(L, W))
    (h : ∀ V : X.Opens, ∀ hV : V ≤ W,
      Function.Bijective fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op e) :
    IsTrivializedNear L x :=
  ⟨W, hx, e, isStalkBasis_germ_of_bijective_smul e h⟩

/-- The structure sheaf, regarded as a module over itself, is trivialized near every point, by
its unit section. -/
theorem isTrivializedNear_unit (X : Scheme.{u}) (x : X) :
    IsTrivializedNear (SheafOfModules.unit X.ringCatSheaf : X.Modules) x := by
  set L : X.Modules := SheafOfModules.unit X.ringCatSheaf with hL
  refine isTrivializedNear_of_bijective_smul (W := ⊤) trivial
    (show Γ(L, ⊤) from (1 : Γ(X, ⊤))) fun V hV => ?_
  have h : ∀ c : Γ(X, V), (c • L.presheaf.map (homOfLE hV).op
      (show Γ(L, ⊤) from (1 : Γ(X, ⊤))) : Γ(L, V)) = (show Γ(L, V) from c) := by
    intro c
    have h1 : (L.presheaf.map (homOfLE hV).op) (show Γ(L, ⊤) from (1 : Γ(X, ⊤))) =
        (show Γ(L, V) from (1 : Γ(X, V))) := PresheafOfModules.unit_map_one _ _
    rw [h1]
    exact smul_eq_mul (α := Γ(X, V)) .. ▸ mul_one c
  exact ⟨fun c c' hcc' => by rw [← h c, ← h c']; exact hcc', fun g => ⟨g, h g⟩⟩

end Stacks.Divisors

end
