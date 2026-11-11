module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-! # Stacks in groupoids along a fully faithful functor over the base

Let `p : 𝒮 ⥤ 𝒞` be a category over a site `(𝒞, J)` and `b : 𝒳' ⥤ 𝒮` a fully faithful functor
such that every object of `𝒮` is the target of an isomorphism from an object `b.obj x'` lying over
an identity of `𝒞`. If `p` is a stack in groupoids (`CategoryTheory.Functor.IsStackInGroupoids`,
Stacks 02ZI) and `b ⋙ p` is fibred in groupoids, then `b ⋙ p` is a stack in groupoids.

This is the transport underlying Stacks 042X for the family-indexed rendering
`CategoryTheory.Functor.IsStackInGroupoids`: the quasi-inverse of an equivalence over `𝒞`, and the
equivalence itself, are functors of this kind. Every datum of `b ⋙ p` (restrictions, fibre
morphisms, canonical restrictions, descent data) is sent by `b` to the corresponding datum of `p`;
the `Isom` sheaf condition is pulled back along `b` because `b` is fully faithful, and an
effective descent of the image of a descent datum is moved into the image of `b` by the vertical
isomorphism, the restrictions of the descended object being read through the fibre isomorphisms of
the effectivity.

## Main definitions

* `CategoryTheory.Functor.Restriction.imageComp`: the `b`-image of a restriction for `b ⋙ p`.
* `CategoryTheory.Functor.DescentDatum.imageComp`: the `b`-image of a descent datum for `b ⋙ p`.

## Main results

* `CategoryTheory.Functor.Restriction.compTo_eq_of_isHomLift`: the canonical comparison of two
  restrictions is the unique morphism over the base morphism factoring one through the other.
* `CategoryTheory.Functor.isRestrictionOf_imageComp_iff`: canonical restrictions correspond
  under `b`.
* `CategoryTheory.Functor.IsStackInGroupoids.comp_of_full_of_faithful`: the transport itself.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- The canonical comparison `Restriction.compTo` lies over the base morphism it is taken
along. -/
theorem Restriction.isHomLift_eqToHom_compTo (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : 𝒮} {hx : p.obj x = U} (xr : Restriction p f x hx)
    (xrW : Restriction p h x hx) :
    p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo p g f hh xr xrW) :=
  have : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) = eqToHom xrW.hpt ≫ h ≫ eqToHom hx.symm := by
      subst hh; simp
    rw [e]; exact xrW.isHomLift
  Functor.IsStronglyCartesian.map_isHomLift p
    (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom rfl xrW.hom

/-- The canonical comparison of two restrictions of `x` is the only morphism lying over the base
morphism it is taken along which factors the second restriction through the first. -/
theorem Restriction.compTo_eq_of_isHomLift (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} {g : W ⟶ V} {f : V ⟶ U}
    {h : W ⟶ U} (hh : h = g ≫ f) {x : 𝒮} {hx : p.obj x = U} (xr : Restriction p f x hx)
    (xrW : Restriction p h x hx) (k : xrW.pt ⟶ xr.pt)
    (hk : p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) k)
    (hk' : k ≫ xr.hom = xrW.hom) : Restriction.compTo p g f hh xr xrW = k := by
  have := Restriction.isHomLift_eqToHom_compTo p g f hh xr xrW
  exact Functor.IsStronglyCartesian.ext p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
    (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) (by rw [Restriction.compTo_hom, hk'])

/-- The comparison from a restriction along `g` to a restriction along `𝟙` whose morphism is an
identity is the morphism of the former restriction. -/
theorem Restriction.compTo_eq_hom_of_hom_eq_id (p : 𝒮 ⥤ 𝒞) {W V : 𝒞} (g : W ⟶ V) {h : W ⟶ V}
    (hh : h = g ≫ 𝟙 V) {x : 𝒮} {hx : p.obj x = V} (xr : Restriction p (𝟙 V) x hx)
    (xrW : Restriction p h x hx) (hid : xr.pt = x) (hhom : xr.hom = eqToHom hid) :
    Restriction.compTo p g (𝟙 V) hh xr xrW = xrW.hom ≫ eqToHom hid.symm := by
  have := Restriction.compTo_hom p g (𝟙 V) hh xr xrW
  rw [hhom] at this
  rw [← this, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

section Image

variable {𝒳' : Type u₃} [Category.{v₃} 𝒳'] {p : 𝒮 ⥤ 𝒞} (b : 𝒳' ⥤ 𝒮)

/-- The image under `b` of a restriction for `b ⋙ p` is a restriction for `p`, when `p` is fibred
in groupoids (so that every lift is strongly cartesian). -/
@[simps, implicit_reducible]
def Restriction.imageComp (hp : p.IsFiberedInGroupoids) {V U : 𝒞} {f : V ⟶ U} {x : 𝒳'}
    {hx : (b ⋙ p).obj x = U} (xr : Restriction (b ⋙ p) f x hx) :
    Restriction p f (b.obj x) hx where
  pt := b.obj xr.pt
  hpt := xr.hpt
  hom := b.map xr.hom
  isHomLift := (isHomLift_comp_iff b p _ xr.hom).1 xr.isHomLift
  isCart :=
    haveI := (isHomLift_comp_iff b p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom).1
      xr.isHomLift
    hp.isStronglyCartesian_homLift _ _

/-- A morphism of a fibre of `b ⋙ p` is one of `p` after applying `b`, and conversely. -/
theorem fibreHom_comp_iff {U : 𝒞} {a c : 𝒳'} (ha : (b ⋙ p).obj a = U) (hc : (b ⋙ p).obj c = U)
    (φ : a ⟶ c) : FibreHom (b ⋙ p) a c ha hc φ ↔ FibreHom p (b.obj a) (b.obj c) ha hc (b.map φ) :=
  isHomLift_comp_iff b p _ φ

/-- `b` sends canonical comparisons of restrictions for `b ⋙ p` to those of their images. -/
theorem Restriction.map_compTo (hp : p.IsFiberedInGroupoids) {W V U : 𝒞} (g : W ⟶ V)
    (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f) {x : 𝒳'} {hx : (b ⋙ p).obj x = U}
    (xr : Restriction (b ⋙ p) f x hx) (xrW : Restriction (b ⋙ p) h x hx) :
    b.map (Restriction.compTo (b ⋙ p) g f hh xr xrW) =
      Restriction.compTo p g f hh (xr.imageComp b hp) (xrW.imageComp b hp) :=
  (Restriction.compTo_eq_of_isHomLift p hh (xr.imageComp b hp) (xrW.imageComp b hp)
    (b.map (Restriction.compTo (b ⋙ p) g f hh xr xrW))
    ((isHomLift_comp_iff b p _ _).1
      (Restriction.isHomLift_eqToHom_compTo (b ⋙ p) g f hh xr xrW))
    (by
      show b.map _ ≫ b.map xr.hom = b.map xrW.hom
      rw [← b.map_comp, Restriction.compTo_hom])).symm

/-- Canonical restrictions for `b ⋙ p` are sent by `b` to canonical restrictions for `p`. -/
theorem IsRestrictionOf.imageComp (hp : p.IsFiberedInGroupoids) {W V Ux Uy : 𝒞} {g : W ⟶ V}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy} {x y : 𝒳'} {hx : (b ⋙ p).obj x = Ux}
    {hy : (b ⋙ p).obj y = Uy} {xr : Restriction (b ⋙ p) fx x hx}
    {yr : Restriction (b ⋙ p) fy y hy} {xrW : Restriction (b ⋙ p) hx_ x hx}
    {yrW : Restriction (b ⋙ p) hy_ y hy} {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt}
    (h : IsRestrictionOf (b ⋙ p) g hfx hfy xr yr xrW yrW α β) :
    IsRestrictionOf p g hfx hfy (xr.imageComp b hp) (yr.imageComp b hp) (xrW.imageComp b hp)
      (yrW.imageComp b hp) (b.map α) (b.map β) := by
  unfold IsRestrictionOf at h ⊢
  rw [← Restriction.map_compTo, ← Restriction.map_compTo, ← b.map_comp, ← b.map_comp, h]

/-- For a faithful `b`, a morphism of `b ⋙ p` is a canonical restriction exactly when its image
under `b` is one for `p`. -/
theorem isRestrictionOf_imageComp_iff [b.Faithful] (hp : p.IsFiberedInGroupoids)
    {W V Ux Uy : 𝒞} {g : W ⟶ V} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy} {x y : 𝒳'} {hx : (b ⋙ p).obj x = Ux}
    {hy : (b ⋙ p).obj y = Uy} {xr : Restriction (b ⋙ p) fx x hx}
    {yr : Restriction (b ⋙ p) fy y hy} {xrW : Restriction (b ⋙ p) hx_ x hx}
    {yrW : Restriction (b ⋙ p) hy_ y hy} {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt} :
    IsRestrictionOf p g hfx hfy (xr.imageComp b hp) (yr.imageComp b hp) (xrW.imageComp b hp)
        (yrW.imageComp b hp) (b.map α) (b.map β) ↔
      IsRestrictionOf (b ⋙ p) g hfx hfy xr yr xrW yrW α β := by
  refine ⟨fun h => ?_, IsRestrictionOf.imageComp b hp⟩
  unfold IsRestrictionOf at h ⊢
  rw [← Restriction.map_compTo, ← Restriction.map_compTo, ← b.map_comp, ← b.map_comp] at h
  exact b.map_injective h

/-- The `Isom` sheaf condition for `p` at the images of two objects of `𝒳'` gives it for `b ⋙ p`,
when `b` is fully faithful. -/
theorem isomIsSheafFor_comp [b.Full] [b.Faithful] (hp : p.IsFiberedInGroupoids) {U : 𝒞}
    (x y : 𝒳') (hx : (b ⋙ p).obj x = U) (hy : (b ⋙ p).obj y = U) {I : Type w} (V : I → 𝒞)
    (f : ∀ i, V i ⟶ U) (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i)
    (pr₂ : ∀ i j, Vij i j ⟶ V j) (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction (b ⋙ p) (f i) x hx) (yr : ∀ i, Restriction (b ⋙ p) (f i) y hy)
    (xrij : ∀ i j, Restriction (b ⋙ p) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction (b ⋙ p) (pr₁ i j ≫ f i) y hy)
    (h : IsomIsSheafFor p (b.obj x) (b.obj y) hx hy V f Vij pr₁ pr₂ hVij
      (fun i => (xr i).imageComp b hp) (fun i => (yr i).imageComp b hp)
      (fun i j => (xrij i j).imageComp b hp) (fun i j => (yrij i j).imageComp b hp)) :
    IsomIsSheafFor (b ⋙ p) x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hφ hφiso hcompat
  obtain ⟨g, ⟨hgf, hgiso, hgeq⟩, hguniq⟩ := h (fun i => b.map (φ i))
    (fun i => (fibreHom_comp_iff b _ _ (φ i)).1 (hφ i))
    (fun i => by haveI := hφiso i; infer_instance)
    (fun i j => by
      obtain ⟨γ, hγ, h₁, h₂⟩ := hcompat i j
      exact ⟨b.map γ, (fibreHom_comp_iff b _ _ γ).1 hγ, IsRestrictionOf.imageComp b hp h₁,
        IsRestrictionOf.imageComp b hp h₂⟩)
  refine ⟨b.preimage g, ⟨?_, ?_, fun i => ?_⟩, fun g' ⟨hg'f, _, hg'eq⟩ => ?_⟩
  · rw [fibreHom_comp_iff, b.map_preimage]
    exact hgf
  · haveI := hgiso
    haveI : IsIso (b.map (b.preimage g)) := by rw [b.map_preimage]; infer_instance
    exact isIso_of_fully_faithful b _
  · apply b.map_injective
    rw [b.map_comp, b.map_comp, b.map_preimage]
    exact hgeq i
  · apply b.map_injective
    rw [b.map_preimage]
    refine hguniq _ ⟨(fibreHom_comp_iff b _ _ g').1 hg'f, inferInstance, fun i => ?_⟩
    have := congrArg b.map (hg'eq i)
    rw [b.map_comp, b.map_comp] at this
    exact this

variable {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → 𝒞}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- The image under `b` of a descent datum for `b ⋙ p`, a descent datum for `p` relative to the
same covering family. -/
@[simps, implicit_reducible]
def DescentDatum.imageComp (hp : p.IsFiberedInGroupoids)
    (D : DescentDatum (b ⋙ p) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x i := b.obj (D.x i)
  hx := D.hx
  xrij i j := (D.xrij i j).imageComp b hp
  xrji i j := (D.xrji i j).imageComp b hp
  φ i j := b.map (D.φ i j)
  φ_fibreHom i j := (fibreHom_comp_iff b _ _ _).1 (D.φ_fibreHom i j)
  φ_iso i j := by haveI := D.φ_iso i j; infer_instance
  wi i j k := (D.wi i j k).imageComp b hp
  wj i j k := (D.wj i j k).imageComp b hp
  wk i j k := (D.wk i j k).imageComp b hp
  αij i j k := b.map (D.αij i j k)
  αjk i j k := b.map (D.αjk i j k)
  αik i j k := b.map (D.αik i j k)
  αij_restr i j k := IsRestrictionOf.imageComp b hp (D.αij_restr i j k)
  αjk_restr i j k := IsRestrictionOf.imageComp b hp (D.αjk_restr i j k)
  s₁₃ := D.s₁₃
  hs₁₃₁ := D.hs₁₃₁
  hs₁₃₂ := D.hs₁₃₂
  αik_restr i j k := IsRestrictionOf.imageComp b hp (D.αik_restr i j k)
  cocycle i j k := by rw [D.cocycle, b.map_comp]

/-- The base image of a fibre morphism is a composite of `eqToHom`s. -/
private theorem map_eq_of_fibreHom {U : 𝒞} {a c : 𝒮} {ha : p.obj a = U} {hc : p.obj c = U}
    {φ : a ⟶ c} (h : FibreHom p a c ha hc φ) : p.map φ = eqToHom (ha.trans hc.symm) := by
  simpa using IsHomLift.fac' p (eqToHom ha ≫ eqToHom hc.symm) φ

/-- The base image of the morphism of a restriction is the base morphism it lies over. -/
private theorem map_restriction_hom {V U : 𝒞} {g : V ⟶ U} {x : 𝒮} {hx : p.obj x = U}
    (xr : Restriction p g x hx) : p.map xr.hom = eqToHom xr.hpt ≫ g ≫ eqToHom hx.symm := by
  simpa using IsHomLift.fac' p (eqToHom xr.hpt ≫ g ≫ eqToHom hx.symm) xr.hom

/-- Precomposing the morphism of a restriction with a fibre isomorphism and postcomposing it with
an isomorphism over an identity gives again a morphism over the same base morphism. -/
private theorem isHomLift_inv_comp_hom_comp {V U : 𝒞} {g : V ⟶ U} {x x₀ a : 𝒮}
    {hx : p.obj x = U} (hx₀ : p.obj x₀ = U) (xr : Restriction p g x hx) (ha : p.obj a = V)
    (ψ : xr.pt ⟶ a) [IsIso ψ] (hψ : FibreHom p xr.pt a xr.hpt ha ψ) (u : x₀ ≅ x)
    (hu : p.IsHomLift (𝟙 (p.obj x₀)) u.hom) :
    p.IsHomLift (eqToHom ha ≫ g ≫ eqToHom hx₀.symm) (CategoryTheory.inv ψ ≫ xr.hom ≫ u.inv) := by
  have hu' : p.map u.hom = eqToHom (hx₀.trans hx.symm) := by
    simpa using IsHomLift.fac' p (𝟙 (p.obj x₀)) u.hom
  have hu'' : p.map u.inv = eqToHom (hx.trans hx₀.symm) := by
    rw [← cancel_epi (p.map u.hom), ← p.map_comp, u.hom_inv_id, p.map_id, hu', eqToHom_trans,
      eqToHom_refl]
  have hψ' : p.map (CategoryTheory.inv ψ) = eqToHom (ha.trans xr.hpt.symm) := by
    rw [← cancel_epi (p.map ψ), ← p.map_comp, IsIso.hom_inv_id, p.map_id, map_eq_of_fibreHom hψ,
      eqToHom_trans, eqToHom_refl]
  refine IsHomLift.of_fac' p _ _ rfl rfl ?_
  rw [p.map_comp, p.map_comp, hψ', map_restriction_hom xr, hu'']
  simp

/-- An effective descent of the `b`-image of a descent datum for `b ⋙ p` gives one of the datum
itself, when `b` is fully faithful and every object of `𝒮` is isomorphic over an identity to an
object in the image of `b`. -/
theorem DescentDatum.isEffective_of_imageComp [b.Full] [b.Faithful]
    (hp : p.IsFiberedInGroupoids) (hr : (b ⋙ p).IsFiberedInGroupoids)
    (hess : ∀ x : 𝒮, ∃ (x' : 𝒳') (u : b.obj x' ≅ x), p.IsHomLift (𝟙 (p.obj (b.obj x'))) u.hom)
    (D : DescentDatum (b ⋙ p) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (hD : (D.imageComp b hp).IsEffective) : D.IsEffective := by
  obtain ⟨x, hx, xr, ψ, hψ, hψiso, hcompat⟩ := hD
  obtain ⟨x', u, hu⟩ := hess x
  have hx' : (b ⋙ p).obj x' = U := by
    haveI := hu
    exact (IsHomLift.codomain_eq p (𝟙 (p.obj (b.obj x'))) u.hom).symm.trans hx
  -- the restriction of `x'` along `f i` is `D.x i`, through the fibre isomorphism `ψ i`
  let xr' : ∀ i, Restriction (b ⋙ p) (f i) x' hx' := fun i =>
    haveI := hψiso i
    have hlift := isHomLift_inv_comp_hom_comp (x₀ := b.obj x') hx' (xr i) (D.hx i) (ψ i) (hψ i) u hu
    { pt := D.x i
      hpt := D.hx i
      hom := b.preimage (CategoryTheory.inv (ψ i) ≫ (xr i).hom ≫ u.inv)
      isHomLift := by
        rw [isHomLift_comp_iff, b.map_preimage]
        exact hlift
      isCart := by
        haveI : (b ⋙ p).IsHomLift (eqToHom (D.hx i) ≫ f i ≫ eqToHom hx'.symm)
            (b.preimage (CategoryTheory.inv (ψ i) ≫ (xr i).hom ≫ u.inv)) := by
          rw [isHomLift_comp_iff, b.map_preimage]
          exact hlift
        exact hr.isStronglyCartesian_homLift _ _ }
  have hxr'hom : ∀ i, b.map (xr' i).hom = CategoryTheory.inv (ψ i) ≫ (xr i).hom ≫ u.inv :=
    fun i => by
    haveI := hψiso i
    exact b.map_preimage _
  refine ⟨x', hx', xr', fun i => 𝟙 (D.x i), fun i => FibreHom.id _ _ _, fun i => inferInstance,
    fun i j => ?_⟩
  obtain ⟨xrij, ψir, ψjr, hψir, hψjr, hψiriso, hψjriso, hR₁, hR₂, heq⟩ := hcompat i j
  haveI := hψiso i
  haveI := hψiso j
  have hlift := isHomLift_inv_comp_hom_comp (x₀ := b.obj x') hx' xrij (D.xrij i j).hpt ψir hψir u hu
  have hlift' : (b ⋙ p).IsHomLift (eqToHom (D.xrij i j).hpt ≫ (pr₁ i j ≫ f i) ≫ eqToHom hx'.symm)
      (b.preimage (CategoryTheory.inv ψir ≫ xrij.hom ≫ u.inv)) := by
    rw [isHomLift_comp_iff, b.map_preimage]
    exact hlift
  let xrij' : Restriction (b ⋙ p) (pr₁ i j ≫ f i) x' hx' :=
    { pt := (D.xrij i j).pt
      hpt := (D.xrij i j).hpt
      hom := b.preimage (CategoryTheory.inv ψir ≫ xrij.hom ≫ u.inv)
      isHomLift := hlift'
      isCart := hr.isStronglyCartesian_homLift _ _ }
  have hxrij'hom : b.map xrij'.hom = CategoryTheory.inv ψir ≫ xrij.hom ≫ u.inv := b.map_preimage _
  -- the comparisons into the trivial restrictions of `D.x i`, `D.x j` are the morphisms of the
  -- restrictions `D.xrij i j`, `D.xrji i j`
  have hc₁ := Restriction.compTo_eq_hom_of_hom_eq_id p (pr₁ i j) (by simp)
    (Restriction.id p (b.obj (D.x i)) (D.hx i)) ((D.xrij i j).imageComp b hp) rfl rfl
  have hc₂ := Restriction.compTo_eq_hom_of_hom_eq_id p (pr₂ i j) (by simp)
    (Restriction.id p (b.obj (D.x j)) (D.hx j)) ((D.xrji i j).imageComp b hp) rfl rfl
  have hc₁' := Restriction.compTo_eq_hom_of_hom_eq_id p (pr₁ i j) (by simp)
    ((Restriction.id (b ⋙ p) (D.x i) (D.hx i)).imageComp b hp)
    ((D.xrij i j).imageComp b hp) rfl (by simp [Restriction.id])
  have hc₂' := Restriction.compTo_eq_hom_of_hom_eq_id p (pr₂ i j) (by simp)
    ((Restriction.id (b ⋙ p) (D.x j) (D.hx j)).imageComp b hp)
    ((D.xrji i j).imageComp b hp) rfl (by simp [Restriction.id])
  simp only [eqToHom_refl, Category.comp_id, Restriction.imageComp_hom] at hc₁ hc₂ hc₁' hc₂'
  replace hR₁ : ψir ≫ b.map (D.xrij i j).hom =
      Restriction.compTo p (pr₁ i j) (f i) rfl (xr i) xrij ≫ ψ i := by
    rw [← hc₁]
    exact hR₁
  replace hR₂ : ψjr ≫ b.map (D.xrji i j).hom =
      Restriction.compTo p (pr₂ i j) (f j) (hVij i j).w (xr j) xrij ≫ ψ j := by
    rw [← hc₂]
    exact hR₂
  have heq' : ψir ≫ b.map (D.φ i j) = ψjr := heq
  refine ⟨xrij', 𝟙 _, D.φ i j, FibreHom.id _ _ _, D.φ_fibreHom i j, inferInstance, D.φ_iso i j,
    ?_, ?_, by simp⟩
  · rw [← isRestrictionOf_imageComp_iff b hp]
    change b.map (𝟙 _) ≫ _ = _ ≫ b.map (𝟙 _)
    rw [b.map_id, b.map_id, Category.id_comp, Category.comp_id, hc₁']
    symm
    refine Restriction.compTo_eq_of_isHomLift p _ _ _ _ ?_ ?_
    · exact (isHomLift_comp_iff b p _ _).1 ((D.xrij i j).isHomLift)
    · change b.map (D.xrij i j).hom ≫ b.map (xr' i).hom = b.map xrij'.hom
      rw [hxr'hom, hxrij'hom, ← cancel_epi ψir, reassoc_of% hR₁]
      simp only [IsIso.hom_inv_id_assoc]
      rw [← Category.assoc, Restriction.compTo_hom]
  · rw [← isRestrictionOf_imageComp_iff b hp]
    change b.map (D.φ i j) ≫ _ = _ ≫ b.map (𝟙 _)
    rw [b.map_id, Category.comp_id, hc₂']
    symm
    refine Restriction.compTo_eq_of_isHomLift p _ _ _ _ ?_ ?_
    · refine IsHomLift.of_fac' p _ _ rfl rfl ?_
      have hm : p.map (b.map (D.xrji i j).hom) =
          eqToHom (D.xrji i j).hpt ≫ pr₂ i j ≫ eqToHom (D.hx j).symm :=
        map_restriction_hom ((D.xrji i j).imageComp b hp)
      rw [p.map_comp, map_eq_of_fibreHom ((fibreHom_comp_iff b _ _ _).1 (D.φ_fibreHom i j)), hm]
      simp
    · change (b.map (D.φ i j) ≫ b.map (D.xrji i j).hom) ≫ b.map (xr' j).hom = b.map xrij'.hom
      rw [hxr'hom, hxrij'hom, ← cancel_epi ψir]
      simp only [Category.assoc]
      rw [reassoc_of% heq', reassoc_of% hR₂]
      simp only [IsIso.hom_inv_id_assoc]
      rw [← Category.assoc, Restriction.compTo_hom]

end Image

/-- **Stacks in groupoids along a fully faithful functor.** Let `p : 𝒮 ⥤ 𝒞` be a stack in
groupoids over `(𝒞, J)` and `b : 𝒳' ⥤ 𝒮` a fully faithful functor such that every object of `𝒮`
is isomorphic, by an isomorphism over an identity, to an object in the image of `b`. If `b ⋙ p`
is fibred in groupoids, it is a stack in groupoids over `(𝒞, J)`. -/
theorem IsStackInGroupoids.comp_of_full_of_faithful {J : GrothendieckTopology 𝒞}
    {𝒳' : Type u₃} [Category.{v₃} 𝒳'] {p : 𝒮 ⥤ 𝒞} (b : 𝒳' ⥤ 𝒮) [b.Full] [b.Faithful]
    (hess : ∀ x : 𝒮, ∃ (x' : 𝒳') (u : b.obj x' ≅ x), p.IsHomLift (𝟙 (p.obj (b.obj x'))) u.hom)
    (hr : (b ⋙ p).IsFiberedInGroupoids) (h : p.IsStackInGroupoids.{w} J) :
    (b ⋙ p).IsStackInGroupoids.{w} J where
  isFiberedInGroupoids := hr
  isom_isSheaf := fun {U} x y hx hy {I} V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij =>
    isomIsSheafFor_comp b h.isFiberedInGroupoids x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij
      (h.isom_isSheaf _ _ hx hy V f hf Vij pr₁ pr₂ hVij _ _ _ _)
  effective_descent := fun V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D =>
    D.isEffective_of_imageComp b h.isFiberedInGroupoids hr hess
      (h.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃
        (D.imageComp b h.isFiberedInGroupoids))

end CategoryTheory.Functor
