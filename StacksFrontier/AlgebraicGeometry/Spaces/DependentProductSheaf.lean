module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.CategoryTheory.DependentProduct

/-!
# The dependent product of presheaves is an fppf sheaf

Let `f : V ⟶ W` be a morphism of presheaves on the big fppf site of `S` and `Y : Over V`. This
file proves that the dependent product (Weil restriction) `CategoryTheory.Presheaf.depProdObj f Y`
of Stacks 0BGY is an fppf sheaf when `W` and `Y.left` are sheaves and `V` is separated. A section
of the dependent product over `A` is a pair `(w, y)`: a section `w` of `W` over `A` together with
the family of values `y` of a morphism `A ×_{w, W} V ⟶ Y` over `V`.

## The hypothesis on `V`

Besides `W` and `Y.left` being sheaves the statement needs `V` to be **separated**, and that
hypothesis is not removable. The `over` field of a section of the dependent product is the
equation `Y.hom.app _ (y.app h v hv) = v`, an equation between two sections of `V`; the glued
value satisfies it only locally on the covering sieve, and what upgrades local agreement in `V`
to agreement is exactly separatedness of `V`. The sheaf condition for `W` does give
`f.app _ (Y.hom.app _ z) = f.app _ v`, so nothing short of injectivity of `f` on sections would
replace the hypothesis, and no hypothesis on `f` is wanted here.

Without it the statement is false. Let `R` be a covering sieve of an object `A` with
`𝟙 A ∉ R`, put `V := yoneda A ⊔_{R.functor} yoneda A` — two copies of `yoneda A` glued along
`R`, so that `V` has two distinct sections over `A` agreeing on `R`, and is not separated — and
take `W := yoneda A` with `f` the fold map, `Y := (yoneda A, ι₁)`. Both `W` and `Y.left` are
sheaves, the big fppf site being subcanonical. A section of the dependent product over `T` is a
section `w : T ⟶ A` of `W` together with, for every `h : T' ⟶ T` and every `v` of `V` over
`h ≫ w`, a lift of `v` through `ι₁`; the fibre of `f` over `h ≫ w` is a single point when
`h ≫ w ∈ R` and two points otherwise, and in the second case the point coming from the second
copy has no lift. So the dependent product is exactly the subfunctor `R.functor` of
`yoneda A`, and that is not a sheaf: the family `g ↦ g` on `R` is compatible, and an
amalgamation would be a `t ∈ R A` with `g ≫ t = g` for every `g ∈ R`, forcing `t = 𝟙 A ∉ R A`.

## Main results

* `AlgebraicGeometry.Space.isSheaf_depProdObj_of_isSeparated`: the dependent product of `Y`
  along `f` is an fppf sheaf when `W` and `Y.left` are sheaves and `V` is separated.
* `AlgebraicGeometry.Space.isSheaf_depProdObj`: the same with `V` a sheaf.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The presheaf category on the big fppf site over `S` is locally `u`-small.
attribute [local instance] locallySmall_presheaf_bigFppfOver

variable {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The value of a section of the dependent product at the identity -/

/-- A pair `(w, y)` and a section `v` of `V` lying over `w` give a point of the fibre product at
which `y` may be evaluated: `v` lies over the restriction of `w` along the identity. -/
theorem depProdValAtId_compat (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) (v : V.obj (op A)) (hv : f.app (op A) v = p.1) :
    f.app (op A) v = W.map (𝟙 A).op p.1 := by
  rw [hv]
  simp

/-- The value of a section `p = (w, y)` of the dependent product at a section `v` of `V` lying
over `w`: the value of the family `y` at the identity and at `v`. -/
def depProdValAtId (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) (v : V.obj (op A)) (hv : f.app (op A) v = p.1) :
    Y.left.obj (op A) :=
  p.2.app (𝟙 A) v (depProdValAtId_compat B S hS f Y p v hv)

/-- The value at the identity depends only on the section of the dependent product and on the
section of `V`, not on the compatibility proof. -/
theorem depProdValAtId_congr (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    {p q : (depProdObj f Y).obj (op A)} (hpq : p = q) {v v' : V.obj (op A)} (hv₀ : v = v')
    (hv : f.app (op A) v = p.1) (hv' : f.app (op A) v' = q.1) :
    depProdValAtId B S hS f Y p v hv = depProdValAtId B S hS f Y q v' hv' := by
  subst hpq hv₀
  rfl

/-- The value at the identity lies over the given section of `V`. -/
theorem depProdValAtId_over (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) (v : V.obj (op A)) (hv : f.app (op A) v = p.1) :
    Y.hom.app (op A) (depProdValAtId B S hS f Y p v hv) = v :=
  p.2.over (𝟙 A) v (depProdValAtId_compat B S hS f Y p v hv)

/-- The value at the identity of a restricted section is the value of the original section at
the restricting morphism. -/
theorem depProdValAtId_restrict (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) {A' : BigFppfOver B S hS} (g : A' ⟶ A)
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map g.op p.1) :
    depProdValAtId B S hS f Y ((depProdObj f Y).map g.op p) v hv = p.2.app g v hv :=
  DepProdSection.restrict_app_of_eq p.2 g (𝟙 A') g (Category.id_comp g).symm v
    (depProdValAtId_compat B S hS f Y ((depProdObj f Y).map g.op p) v hv) hv

/-- The compatibility datum for the value at the identity of a restricted section. -/
theorem depProdMap_compat (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) {A' : BigFppfOver B S hS} (k : A' ⟶ A)
    (v : V.obj (op A)) (hv : f.app (op A) v = p.1) :
    f.app (op A') (V.map k.op v) = ((depProdObj f Y).map k.op p).1 := by
  rw [NatTrans.naturality_apply, hv, depProdObj_map]

/-- Restriction of the value at the identity is the value at the identity of the restriction. -/
theorem depProdMap_valAtId (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) {A' : BigFppfOver B S hS} (k : A' ⟶ A)
    (v : V.obj (op A)) (hv : f.app (op A) v = p.1) :
    Y.left.map k.op (depProdValAtId B S hS f Y p v hv) =
      depProdValAtId B S hS f Y ((depProdObj f Y).map k.op p) (V.map k.op v)
        (depProdMap_compat B S hS f Y p k v hv) := by
  rw [depProdValAtId_restrict B S hS f Y p k (V.map k.op v)
    (depProdMap_compat B S hS f Y p k v hv)]
  exact (p.2.naturality k (𝟙 A) v (depProdValAtId_compat B S hS f Y p v hv)).trans
    (p.2.app_congr (Category.comp_id k) (V.map k.op v)
      (map_compat f k (𝟙 A) (depProdValAtId_compat B S hS f Y p v hv))
      (depProdMap_compat B S hS f Y p k v hv))

/-- Two sections of the dependent product with a common restriction take the same value there:
the value of the restriction at the identity is the value of the original at the restricting
morphism. -/
theorem depProdValAtId_of_map_eq (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A)) {A' : BigFppfOver B S hS} (g : A' ⟶ A)
    (q : (depProdObj f Y).obj (op A')) (hpq : (depProdObj f Y).map g.op p = q)
    (v : V.obj (op A')) (hvp : f.app (op A') v = W.map g.op p.1)
    (hvq : f.app (op A') v = q.1) :
    p.2.app g v hvp = depProdValAtId B S hS f Y q v hvq := by
  subst hpq
  exact (depProdValAtId_restrict B S hS f Y p g v hvp).symm

/-- A section of the dependent product is the pair of its two components. -/
theorem depProdObj_eta (f : V ⟶ W) (Y : Over V) {A : (BigFppfOver B S hS)ᵒᵖ}
    (p : (depProdObj f Y).obj A) : (⟨p.1, p.2⟩ : (depProdObj f Y).obj A) = p :=
  rfl

/-! ### Gluing: the base component -/

/-- The family of base sections of a family of sections of the dependent product. -/
def depProdBaseFamily (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS} {R : Sieve A}
    (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows) :
    Presieve.FamilyOfElements W R.arrows :=
  fun _ g hg => (x g hg).1

/-- The member of `AlgebraicGeometry.Space.depProdBaseFamily` at `g` is the base section of the
member of the original family at `g`. -/
@[simp]
theorem depProdBaseFamily_apply (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS} {R : Sieve A}
    (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {A' : BigFppfOver B S hS} (g : A' ⟶ A) (hg : R.arrows g) :
    depProdBaseFamily B S hS f Y x g hg = (x g hg).1 :=
  rfl

/-- The family of base sections of a compatible family is compatible. -/
theorem depProdBaseFamily_compatible (f : V ⟶ W) (Y : Over V) {A : BigFppfOver B S hS}
    {R : Sieve A} (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    (hx : x.Compatible) : (depProdBaseFamily B S hS f Y x).Compatible := by
  intro A₁ A₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  simp only [depProdBaseFamily_apply]
  exact congrArg (fun p => p.1) (hx g₁ g₂ h₁ h₂ e)

/-! ### Gluing: the family of values -/

section Glue

variable {f : V ⟶ W} {Y : Over V} {A : BigFppfOver B S hS} {R : Sieve A}

/-- If `k` lies in the pullback of the sieve `R` along `h`, then `k ≫ h` lies in `R`. -/
theorem mem_of_mem_pullback {A' : BigFppfOver B S hS} (h : A' ⟶ A)
    {A'' : BigFppfOver B S hS} {k : A'' ⟶ A'} (hk : (R.pullback h).arrows k) :
    R.arrows (k ≫ h) :=
  hk

/-- A section of `V` lying over a restriction of the glued base section lies over the base
section of the corresponding member of the family. -/
theorem depProdApply_compat (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {w : W.obj (op A)}
    (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)
    {A'' : BigFppfOver B S hS} (g : A'' ⟶ A) (hg : R.arrows g) (u : V.obj (op A''))
    (hu : f.app (op A'') u = W.map g.op w) :
    f.app (op A'') u = (x g hg).1 := by
  rw [hw g hg]
  exact hu

/-- The value of a family of elements of the dependent product depends on its arrow only
through that arrow's value. -/
theorem depProdFamily_congr_arrow (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {A' : BigFppfOver B S hS} {g g' : A' ⟶ A} (hgg : g = g') (hg : R.arrows g)
    (hg' : R.arrows g') : x g hg = x g' hg' := by
  subst hgg
  rfl

/-- The compatibility datum for the local values of the glued family. -/
theorem depProdGlueFamily_compat (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {w : W.obj (op A)}
    (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)
    {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) {A'' : BigFppfOver B S hS} (k : A'' ⟶ A')
    (hk : R.arrows (k ≫ h)) :
    f.app (op A'') (V.map k.op v) = (x (k ≫ h) hk).1 :=
  depProdApply_compat B S hS x hw (k ≫ h) hk (V.map k.op v) (map_compat f k h hv)

/-- The local values out of which the value of the glued family at `(h, v)` is built: at
`k : A'' ⟶ A'` with `k ≫ h` in the sieve, the value of the member `x (k ≫ h)` at the identity
of `A''` and at the restriction of `v`. -/
def depProdGlueFamily (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {w : W.obj (op A)}
    (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)
    {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    Presieve.FamilyOfElements Y.left (R.pullback h).arrows :=
  fun _ k hk => depProdValAtId B S hS f Y (x (k ≫ h) hk) (V.map k.op v)
    (depProdGlueFamily_compat B S hS x hw h v hv k hk)

/-- The member of `AlgebraicGeometry.Space.depProdGlueFamily` at `k` is the value of the member
`x (k ≫ h)` at the identity and at the restriction of `v` along `k`. -/
@[simp]
theorem depProdGlueFamily_apply (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows)
    {w : W.obj (op A)}
    (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)
    {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) {A'' : BigFppfOver B S hS} (k : A'' ⟶ A')
    (hk : (R.pullback h).arrows k) :
    depProdGlueFamily B S hS x hw h v hv k hk =
      depProdValAtId B S hS f Y (x (k ≫ h) hk) (V.map k.op v)
        (depProdGlueFamily_compat B S hS x hw h v hv k hk) :=
  rfl

/-- The local values `AlgebraicGeometry.Space.depProdGlueFamily` of a compatible family form a
compatible family. -/
theorem depProdGlueFamily_compatible
    (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows) (hx : x.Compatible)
    {w : W.obj (op A)}
    (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)
    {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    (depProdGlueFamily B S hS x hw h v hv).Compatible := by
  intro A₁ A₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ e
  have hk₁' : R.arrows (k₁ ≫ h) := hk₁
  have hk₂' : R.arrows (k₂ ≫ h) := hk₂
  have e' : g₁ ≫ (k₁ ≫ h) = g₂ ≫ (k₂ ≫ h) := by
    rw [← Category.assoc, ← Category.assoc, e]
  have hv₀ : V.map g₁.op (V.map k₁.op v) = V.map g₂.op (V.map k₂.op v) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, e]
  rw [depProdGlueFamily_apply, depProdGlueFamily_apply, depProdMap_valAtId, depProdMap_valAtId]
  exact depProdValAtId_congr B S hS f Y (hx g₁ g₂ hk₁' hk₂' e') hv₀
    (depProdMap_compat B S hS f Y (x (k₁ ≫ h) hk₁) g₁ (V.map k₁.op v)
      (depProdGlueFamily_compat B S hS x hw h v hv k₁ hk₁))
    (depProdMap_compat B S hS f Y (x (k₂ ≫ h) hk₂) g₂ (V.map k₂.op v)
      (depProdGlueFamily_compat B S hS x hw h v hv k₂ hk₂))

/-! ### Gluing: the glued section -/

variable (hYt : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.left)
  (hR : R ∈ BigFppfOver.topology B S hS A)
  (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows) (hx : x.Compatible)
  {w : W.obj (op A)}
  (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)

include hYt hR hx hw in
/-- The value of the glued section at `(h, v)`: the amalgamation, in `Y.left`, of the local
values over the pullback of the covering sieve along `h`. -/
def depProdGlueVal {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    Y.left.obj (op A') :=
  (hYt (R.pullback h) ((BigFppfOver.topology B S hS).pullback_stable h hR)).amalgamate
    (depProdGlueFamily B S hS x hw h v hv)
    (depProdGlueFamily_compatible B S hS x hx hw h v hv)

include hYt hR hx hw in
/-- The restriction of the glued value at `(h, v)` along `k`, for `k ≫ h` in the sieve, is the
value of the member `x (k ≫ h)` at the identity and at the restriction of `v` along `k`. -/
theorem depProdGlueVal_spec {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) {A'' : BigFppfOver B S hS} (k : A'' ⟶ A')
    (hk : R.arrows (k ≫ h)) :
    Y.left.map k.op (depProdGlueVal B S hS hYt hR x hx hw h v hv) =
      depProdValAtId B S hS f Y (x (k ≫ h) hk) (V.map k.op v)
        (depProdGlueFamily_compat B S hS x hw h v hv k hk) :=
  (hYt (R.pullback h) ((BigFppfOver.topology B S hS).pullback_stable h hR)).isAmalgamation
    (depProdGlueFamily_compatible B S hS x hx hw h v hv) k hk

include hYt hR hx hw in
/-- The restriction law for the glued value, with the arrow of the sieve and the section of `V`
given only up to equality. -/
theorem depProdGlueVal_restrict_eq {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) {A'' : BigFppfOver B S hS} (k : A'' ⟶ A')
    (g : A'' ⟶ A) (hg : g = k ≫ h) (hgR : R.arrows g) (u : V.obj (op A''))
    (hu : u = V.map k.op v) (hu' : f.app (op A'') u = (x g hgR).1) :
    Y.left.map k.op (depProdGlueVal B S hS hYt hR x hx hw h v hv) =
      depProdValAtId B S hS f Y (x g hgR) u hu' := by
  subst hg
  subst hu
  exact depProdGlueVal_spec B S hS hYt hR x hx hw h v hv k hgR

include hYt hR hx hw in
/-- The glued values are compatible with restriction. -/
theorem depProdGlueVal_naturality {A₁ A₂ : BigFppfOver B S hS} (k : A₂ ⟶ A₁) (h : A₁ ⟶ A)
    (v : V.obj (op A₁)) (hv : f.app (op A₁) v = W.map h.op w) :
    Y.left.map k.op (depProdGlueVal B S hS hYt hR x hx hw h v hv) =
      depProdGlueVal B S hS hYt hR x hx hw (k ≫ h) (V.map k.op v) (map_compat f k h hv) := by
  refine (hYt (R.pullback (k ≫ h))
    ((BigFppfOver.topology B S hS).pullback_stable (k ≫ h) hR)).isSeparatedFor.ext
      fun A₃ m hm => ?_
  have hLHS : Y.left.map m.op (Y.left.map k.op (depProdGlueVal B S hS hYt hR x hx hw h v hv)) =
      Y.left.map (m ≫ k).op (depProdGlueVal B S hS hYt hR x hx hw h v hv) := by
    rw [op_comp, FunctorToTypes.map_comp_apply]
  rw [hLHS, depProdGlueVal_spec B S hS hYt hR x hx hw (k ≫ h) (V.map k.op v)
    (map_compat f k h hv) m hm]
  exact depProdGlueVal_restrict_eq B S hS hYt hR x hx hw h v hv (m ≫ k) (m ≫ (k ≫ h))
    (Category.assoc m k h).symm hm (V.map m.op (V.map k.op v))
    (by rw [← FunctorToTypes.map_comp_apply, ← op_comp])
    (depProdGlueFamily_compat B S hS x hw (k ≫ h) (V.map k.op v) (map_compat f k h hv) m hm)

/-- The glued value at `(h₀, v)` is the value of a section `p` at `(e, v)` as soon as the
restrictions of `p` along the `k ≫ e` are the members of the family `x` at the `k ≫ h₀`. -/
private theorem depProdGlueVal_eq_app_of_restrict {A₀ A' : BigFppfOver B S hS}
    (p : (depProdObj f Y).obj (op A₀)) (e : A' ⟶ A₀) (h₀ : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h₀.op w) (hv' : f.app (op A') v = W.map e.op p.1)
    (hp : ∀ {A₃ : BigFppfOver B S hS} (k : A₃ ⟶ A') (hk : R.arrows (k ≫ h₀)),
      (depProdObj f Y).map (k ≫ e).op p = x (k ≫ h₀) hk) :
    depProdGlueVal B S hS hYt hR x hx hw h₀ v hv = p.2.app e v hv' := by
  refine (hYt (R.pullback h₀)
    ((BigFppfOver.topology B S hS).pullback_stable h₀ hR)).isSeparatedFor.ext
      fun A₃ k hk => ?_
  rw [depProdGlueVal_spec B S hS hYt hR x hx hw h₀ v hv k hk, p.2.naturality k e v hv']
  exact (depProdValAtId_of_map_eq B S hS f Y p (k ≫ e) (x (k ≫ h₀) hk) (hp k hk)
    (V.map k.op v) (map_compat f k e hv')
    (depProdGlueFamily_compat B S hS x hw h₀ v hv k hk)).symm

include hYt hR hx hw in
/-- The glued value at an arrow factoring through the sieve is the value of the corresponding
member of the family. -/
theorem depProdGlueVal_eq_app {A'' A' : BigFppfOver B S hS} (g : A'' ⟶ A) (hg : R.arrows g)
    (h : A' ⟶ A'') (v : V.obj (op A')) (hv : f.app (op A') v = W.map (h ≫ g).op w)
    (hv' : f.app (op A') v = W.map h.op (x g hg).1) :
    depProdGlueVal B S hS hYt hR x hx hw (h ≫ g) v hv = (x g hg).2.app h v hv' := by
  have hxs : x.SieveCompatible := by
    rw [← Presieve.compatible_iff_sieveCompatible]
    exact hx
  exact depProdGlueVal_eq_app_of_restrict B S hS hYt hR x hx hw (x g hg) h (h ≫ g) v hv hv'
    fun k hk => (hxs g (k ≫ h) hg).symm.trans
      (depProdFamily_congr_arrow B S hS x (Category.assoc k h g)
        (R.downward_closed hg (k ≫ h)) hk)

end Glue

section GlueSection

variable {f : V ⟶ W} {Y : Over V} {A : BigFppfOver B S hS} {R : Sieve A}
  (hV : Presieve.IsSeparated (BigFppfOver.topology B S hS) V)
  (hYt : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.left)
  (hR : R ∈ BigFppfOver.topology B S hS A)
  (x : Presieve.FamilyOfElements (depProdObj f Y) R.arrows) (hx : x.Compatible)
  {w : W.obj (op A)}
  (hw : ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A) (hg : R.arrows g), (x g hg).1 = W.map g.op w)

include hV hYt hR hx hw in
/-- The glued value lies over the given section of `V`. -/
theorem depProdGlueVal_over {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    Y.hom.app (op A') (depProdGlueVal B S hS hYt hR x hx hw h v hv) = v := by
  refine (hV (R.pullback h)
    ((BigFppfOver.topology B S hS).pullback_stable h hR)).ext fun A'' k hk => ?_
  rw [← NatTrans.naturality_apply Y.hom k.op
      (depProdGlueVal B S hS hYt hR x hx hw h v hv),
    depProdGlueVal_spec B S hS hYt hR x hx hw h v hv k
      (mem_of_mem_pullback B S hS h hk),
    depProdValAtId_over]

include hV hYt hR hx hw in
/-- The glued section of the dependent product over `A`, lying over the glued base section. -/
def depProdGlueSection : DepProdSection f Y A w :=
  DepProdSection.mk' (fun h v hv => depProdGlueVal B S hS hYt hR x hx hw h v hv)
    (fun h v hv => depProdGlueVal_over B S hS hV hYt hR x hx hw h v hv)
    (fun k h v hv => depProdGlueVal_naturality B S hS hYt hR x hx hw k h v hv)

include hV hYt hR hx hw in
/-- The value of the glued section at `(h, v)` is the glued value
`AlgebraicGeometry.Space.depProdGlueVal`. -/
theorem depProdGlueSection_app {A' : BigFppfOver B S hS} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    (depProdGlueSection B S hS hV hYt hR x hx hw).app h v hv =
      depProdGlueVal B S hS hYt hR x hx hw h v hv :=
  DepProdSection.mk'_app _ _ _ h v hv

end GlueSection

/-! ### The sheaf condition -/

/-- **The dependent product of presheaves on the big fppf site is a sheaf**, when the target `W`
and the source `Y.left` are sheaves and `V` is separated. -/
theorem isSheaf_depProdObj_of_isSeparated (f : V ⟶ W) (Y : Over V)
    (hV : Presieve.IsSeparated (BigFppfOver.topology B S hS) V)
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (depProdObj f Y) := by
  have hWt : Presieve.IsSheaf (BigFppfOver.topology B S hS) W :=
    (isSheaf_iff_isSheaf_of_type _ W).1 hW
  have hYt : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.left :=
    (isSheaf_iff_isSheaf_of_type _ Y.left).1 hY
  rw [isSheaf_iff_isSheaf_of_type]
  intro A R hR x hx
  obtain ⟨w, hw⟩ : ∃ w : W.obj (op A), ∀ ⦃A' : BigFppfOver B S hS⦄ (g : A' ⟶ A)
      (hg : R.arrows g), (x g hg).1 = W.map g.op w :=
    ⟨(hWt R hR).amalgamate (depProdBaseFamily B S hS f Y x)
        (depProdBaseFamily_compatible B S hS f Y x hx),
      fun _ g hg => ((hWt R hR).isAmalgamation
        (depProdBaseFamily_compatible B S hS f Y x hx) g hg).symm⟩
  refine ⟨⟨w, depProdGlueSection B S hS hV hYt hR x hx hw⟩, ?_, ?_⟩
  · intro A'' g hg
    refine Eq.trans ?_ (depProdObj_eta B S hS f Y (x g hg))
    refine depProdMk_ext f (hw g hg).symm ?_
    intro A' h v hv hv'
    rw [DepProdSection.restrict_app, depProdGlueSection_app]
    exact depProdGlueVal_eq_app B S hS hYt hR x hx hw g hg h v (comp_compat f g h hv) hv'
  · rintro ⟨w', y'⟩ ht'
    have h1 : w' = w := by
      refine (hWt R hR).isSeparatedFor.ext fun A'' g hg => ?_
      have key := congrArg (fun p => p.1) (ht' g hg)
      rw [hw g hg] at key
      exact key
    refine depProdMk_ext f h1 ?_
    intro A' h v hv hv'
    rw [depProdGlueSection_app]
    exact (depProdGlueVal_eq_app_of_restrict B S hS hYt hR x hx hw
      (⟨w', y'⟩ : (depProdObj f Y).obj (op A)) h h v hv' hv fun k hk => ht' (k ≫ h) hk).symm

/-- **The dependent product of presheaves on the big fppf site is a sheaf**, when `V`, `W` and
`Y.left` are sheaves. -/
theorem isSheaf_depProdObj (f : V ⟶ W) (Y : Over V)
    (hV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V)
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (depProdObj f Y) :=
  isSheaf_depProdObj_of_isSeparated B S hS f Y
    ((isSheaf_iff_isSheaf_of_type _ V).1 hV).isSeparated hW hY

end AlgebraicGeometry.Space

end
