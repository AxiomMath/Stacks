module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Scheme

/-!
# Divided power derivations of a structure sheaf, and `S`-derivations on `CRIS(X/S)`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`.  A *divided power derivation* of
`𝒪_T` into a sheaf `ℳ` of `𝒪_T`-modules is a map of sheaves of abelian groups
`D : 𝒪_T → ℳ` which, over every open `W ⊆ T` lying above an open `V ⊆ Y`, is a divided power
`Γ(V, 𝒪_V)`-derivation `Γ(W, 𝒪_T) → Γ(W, ℳ)` in the sense of
`Crystalline.DividedPowerDerivation`: it is additive, satisfies the Leibniz rule, kills every
section pulled back from `V`, and obeys the divided power chain rule
`D (δ_n x) = δ_{n-1} x · D x` on the divided power ideal.

In the global crystalline situation `(p, (S, I, γ), X)` the same local condition defines an
`S`-derivation of the structure presheaf of the big crystalline category `CRIS(X/S)`, the
big-site analogue of the `S`-derivations of [Stacks, Tag 07IX] (which live on the small site and
are `Crystalline.GlobalCrystallineSituation.SmallSite.SDerivation`): for an
object `(U, T, δ)` and *any* open `V ⊆ S` through which the structure morphism `T → S` factors,
the map on sections `Γ(T, 𝒪_T) → Γ(T, ℱ)` is a divided power `Γ(V, 𝒪_V)`-derivation.  The open
`V` stays universally quantified, as in the source: the condition is imposed for every open of
`S` that receives `T`, not for one chosen such open.

## Main definitions

* `Crystalline.DividedPowerSchemeDerivation` — a divided power derivation of the structure sheaf
  of a divided power scheme `T` over a scheme `Y`, into a sheaf of `𝒪_T`-modules.
* `Crystalline.DividedPowerSchemeDerivation.IsUniversal` — such a derivation through which every
  other one factors uniquely.
* `Crystalline.GlobalCrystallineSituation.ambient` — the functor `CRIS(X/S) ⥤ Sch` remembering
  the ambient divided power scheme `T` of an object `(U, T, δ)`.
* `Crystalline.GlobalCrystallineSituation.structureRingPresheaf` — the presheaf of rings
  `(U, T, δ) ↦ Γ(T, 𝒪_T)` on `CRIS(X/S)`, and `structureRingCatPresheaf` its `RingCat`-valued
  form.
* `Crystalline.GlobalCrystallineSituation.SDerivation` — an `S`-derivation of that structure
  presheaf into a presheaf of modules over it, and
  `Crystalline.GlobalCrystallineSituation.SDerivation.IsUniversal` the corresponding universal
  property.

## Main results

* `Crystalline.DividedPowerSchemeDerivation.ext` and
  `Crystalline.GlobalCrystallineSituation.SDerivation.ext` — a derivation is determined by its
  maps on sections.
* `Crystalline.DividedPowerSchemeDerivation.app_add`, `app_zero`, `leibniz`, `app_appLE` and
  `app_dpow` — additivity, the Leibniz rule, vanishing on sections pulled back from the base and
  the divided power chain rule, read off on sections.
* `Crystalline.GlobalCrystallineSituation.SDerivation.app_add` and `app_zero` — the same for
  `S`-derivations on `CRIS(X/S)`.
* `Crystalline.DividedPowerSchemeDerivation.IsUniversal.hom_ext` and
  `Crystalline.GlobalCrystallineSituation.SDerivation.IsUniversal.hom_ext` — two maps out of a
  universal derivation agreeing on it are equal.

## Implementation notes

The `S`-derivation condition of [Stacks, Tag 07IX] is stated here over the big crystalline
category `CRIS(X/S)` of [Stacks, Tag 07I6], whose objects are the same divided power thickenings
`(U, T, δ)` as those of the small site `Cris(X/S)` of [Stacks, Tag 07IG].  The structure presheaf
`(U, T, δ) ↦ Γ(T, 𝒪_T)` is built directly as `structureRingPresheaf`, as the composite of the
functor `ambient` remembering `T` with the global sections functor on schemes, and the
coefficients are a `PresheafOfModules` over it.  No part of the definition refers to the
topology.  The structure presheaf is a sheaf for the crystalline Zariski topology
(`Crystalline.GlobalCrystallineSituation.crystallineStructureSheaf`).  The definition of the
source, on the small site, is `Crystalline.GlobalCrystallineSituation.SmallSite.SDerivation`
(applied to a sheaf of `𝒪_{X/S}`-modules), in `SmallSite/CrystallineDifferentialsSheaf.lean`,
where the tag is registered and which is used for the sheaf `Ω_{X/S}`.

A derivation is presented by its family of maps on sections `app W` together with, for each pair
`W ≤ f ⁻¹ᵁ V`, the witnessing `Crystalline.DividedPowerDerivation` and the statement that its
underlying function is `app W`.  The witness is carried as data rather than asserted to exist, so
nothing is extracted from an existence statement; it is nevertheless determined by `app`, which
is what makes `ext` true.  Taking `V = ⊤`, which is always legitimate, the divided power
derivation axioms transfer to `app` unconditionally.

The module structure on sections needed to state the condition is the one of the ambient scheme,
transported to the divided power ring of sections by `moduleSections`; the two rings of sections
are the same ring, but the divided power ring is a bundled object, so the instance has to be
supplied by name.

## References

* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07HR](https://stacks.math.columbia.edu/tag/07HR)
* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07IB](https://stacks.math.columbia.edu/tag/07IB)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### Divided power derivations of the structure sheaf of a divided power scheme -/

/-- Every open of the source lies over the whole of the target, so a morphism of schemes always
factors through the open `⊤`. -/
theorem le_preimage_top {X Y : Scheme.{u}} (g : X ⟶ Y) (W : X.Opens) :
    W ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := by
  simp

/-- The sections of a sheaf of `𝒪_T`-modules over an open `W` as a module over the divided power
ring of sections of `T` over `W`. -/
instance DividedPowerScheme.moduleSections (T : DividedPowerScheme.{u}) (W : T.scheme.Opens)
    (M : T.scheme.Modules) :
    Module ↥(T.dividedPowers.toDividedPowerRing (op W)) Γ(M, W) :=
  inferInstanceAs (Module Γ(T.scheme, W) Γ(M, W))

/-- **A divided power derivation of the structure sheaf of a divided power scheme.**  For a
divided power scheme `T` over a scheme `Y` along `f` and a sheaf `M` of `𝒪_T`-modules, this is a
map of sheaves of abelian groups `𝒪_T → M` which over every open `W` of `T` lying above an open
`V` of `Y` is a divided power `Γ(V, 𝒪_Y)`-derivation on sections. -/
structure DividedPowerSchemeDerivation (T : DividedPowerScheme.{u}) (Y : Scheme.{u})
    (f : T.scheme ⟶ Y) (M : T.scheme.Modules) where
  /-- The map on sections over an open subset of the ambient scheme. -/
  app (W : T.scheme.Opens) : Γ(T.scheme, W) → Γ(M, W)
  /-- The maps on sections commute with restriction, so they form a map of sheaves. -/
  naturality {W W' : T.scheme.Opens} (i : W' ⟶ W) (x : Γ(T.scheme, W)) :
    M.presheaf.map i.op (app W x) = app W' (T.scheme.presheaf.map i.op x)
  /-- Over an open `W` of `T` lying above an open `V` of `Y`, the map on sections is a divided
  power `Γ(V, 𝒪_Y)`-derivation. -/
  dividedPowerDerivation (W : T.scheme.Opens) (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(Y, V) (T.dividedPowers.toDividedPowerRing (op W))
      (f.appLE V W h).hom Γ(M, W)
  /-- The divided power derivation over `W` above `V` is the map on sections over `W`. -/
  dividedPowerDerivation_apply (W : T.scheme.Opens) (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (x : Γ(T.scheme, W)) :
    (dividedPowerDerivation W V h).toDerivation x = app W x

namespace DividedPowerSchemeDerivation

variable {T : DividedPowerScheme.{u}} {Y : Scheme.{u}} {f : T.scheme ⟶ Y} {M : T.scheme.Modules}

/-- A divided power derivation of a structure sheaf is determined by its maps on sections. -/
@[ext]
theorem ext {D E : DividedPowerSchemeDerivation T Y f M}
    (h : ∀ W x, D.app W x = E.app W x) : D = E := by
  obtain ⟨appD, _, derD, hD⟩ := D
  obtain ⟨appE, _, derE, hE⟩ := E
  have happ : appD = appE := funext fun W ↦ funext fun x ↦ h W x
  subst happ
  have hder : derD = derE := by
    funext W V hWV
    exact DividedPowerDerivation.ext fun x ↦ (hD W V hWV x).trans (hE W V hWV x).symm
  subst hder
  rfl

/-- The map on sections over `W` is the divided power derivation above the open `⊤` of `Y`. -/
private theorem coe_dividedPowerDerivation_top (D : DividedPowerSchemeDerivation T Y f M)
    (W : T.scheme.Opens) :
    ⇑(D.dividedPowerDerivation W ⊤ (le_preimage_top f W)).toDerivation = D.app W :=
  funext (D.dividedPowerDerivation_apply W ⊤ (le_preimage_top f W))

/-- A divided power derivation is additive on sections. -/
@[simp]
theorem app_add (D : DividedPowerSchemeDerivation T Y f M) (W : T.scheme.Opens)
    (x y : Γ(T.scheme, W)) : D.app W (x + y) = D.app W x + D.app W y := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation W ⊤ (le_preimage_top f W)).map_add x y

/-- A divided power derivation sends the zero section to zero. -/
@[simp]
theorem app_zero (D : DividedPowerSchemeDerivation T Y f M) (W : T.scheme.Opens) :
    D.app W 0 = 0 := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation W ⊤ (le_preimage_top f W)).map_zero

/-- The Leibniz rule for a divided power derivation, on sections. -/
theorem leibniz (D : DividedPowerSchemeDerivation T Y f M) (W : T.scheme.Opens)
    (x y : Γ(T.scheme, W)) : D.app W (x * y) = x • D.app W y + y • D.app W x := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation W ⊤ (le_preimage_top f W)).leibniz x y

/-- A divided power derivation kills every section pulled back from the base. -/
@[simp]
theorem app_appLE (D : DividedPowerSchemeDerivation T Y f M) (W : T.scheme.Opens) (V : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) : D.app W (f.appLE V W h a) = 0 := by
  rw [← D.dividedPowerDerivation_apply W V h]
  exact (D.dividedPowerDerivation W V h).map_ringHom a

/-- The divided power chain rule for a divided power derivation, on sections: the derivation of
the `n`-th divided power of a section of the divided power ideal is the `(n-1)`-st divided power
times the derivation of the section. -/
theorem app_dpow (D : DividedPowerSchemeDerivation T Y f M) (W : T.scheme.Opens) (n : ℕ)
    (hn : 0 < n) (x : Γ(T.scheme, W)) (hx : x ∈ T.ideal.obj (op W)) :
    D.app W ((T.dividedPowers.toDividedPowerRing (op W)).dividedPowers.dpow n x) =
      (T.dividedPowers.toDividedPowerRing (op W)).dividedPowers.dpow (n - 1) x • D.app W x := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation W ⊤ (le_preimage_top f W)).map_dpow n hn x hx

/-- **A universal divided power derivation.**  Every divided power derivation of `𝒪_T` over `Y`
is obtained from it by a unique map of sheaves of `𝒪_T`-modules. -/
def IsUniversal (D : DividedPowerSchemeDerivation T Y f M) : Prop :=
  ∀ (N : T.scheme.Modules) (E : DividedPowerSchemeDerivation T Y f N),
    ∃! φ : M ⟶ N, ∀ (W : T.scheme.Opens) (x : Γ(T.scheme, W)),
      φ.app W (D.app W x) = E.app W x

/-- Two maps out of a universal divided power derivation inducing the same derivation are
equal. -/
theorem IsUniversal.hom_ext {D : DividedPowerSchemeDerivation T Y f M} (hD : D.IsUniversal)
    {N : T.scheme.Modules} {E : DividedPowerSchemeDerivation T Y f N} {φ ψ : M ⟶ N}
    (hφ : ∀ (W : T.scheme.Opens) (x : Γ(T.scheme, W)), φ.app W (D.app W x) = E.app W x)
    (hψ : ∀ (W : T.scheme.Opens) (x : Γ(T.scheme, W)), ψ.app W (D.app W x) = E.app W x) :
    φ = ψ :=
  (hD N E).unique hφ hψ

end DividedPowerSchemeDerivation

/-! ### `S`-derivations on the big crystalline category -/

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- The ambient divided power scheme of an object `(U, T, δ)` of `CRIS(X/S)`, as a functor to
schemes. -/
def ambient : Thickening S ⥤ Scheme.{u} where
  obj A := A.thickening.target.scheme
  map g := g.targetHom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The ambient functor sends `(U, T, δ)` to the scheme `T`. -/
@[simp]
theorem ambient_obj (A : Thickening S) :
    (ambient S).obj A = A.thickening.target.scheme := rfl

/-- The ambient functor sends a morphism to its underlying morphism of ambient schemes. -/
@[simp]
theorem ambient_map {A B : Thickening S} (g : A ⟶ B) :
    (ambient S).map g = g.targetHom.hom := rfl

/-- **The structure presheaf of rings of `CRIS(X/S)`**, sending an object `(U, T, δ)` to the ring
`Γ(T, 𝒪_T)` of global sections of the ambient divided power scheme. -/
def structureRingPresheaf : (Thickening S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (ambient S).op ⋙ Scheme.Γ

/-- The structure presheaf sends `(U, T, δ)` to the ring of global sections of `T`. -/
@[simp]
theorem structureRingPresheaf_obj (A : Thickening S) :
    (structureRingPresheaf S).obj (op A) = Γ(A.thickening.target.scheme, ⊤) := rfl

/-- The structure presheaf sends a morphism `g` to the map on global sections induced by the
underlying morphism of ambient schemes. -/
@[simp]
theorem structureRingPresheaf_map {A B : Thickening S} (g : A ⟶ B) :
    (structureRingPresheaf S).map g.op = g.targetHom.hom.appTop := rfl

/-- The structure presheaf of `CRIS(X/S)` regarded as a presheaf of (not necessarily commutative)
rings, which is the shape a presheaf of modules is indexed by. -/
abbrev structureRingCatPresheaf : (Thickening S)ᵒᵖ ⥤ RingCat.{u} :=
  structureRingPresheaf S ⋙ forget₂ CommRingCat RingCat

/-- The sections of a presheaf of modules over the structure presheaf as a module over the divided
power ring of global sections of the ambient divided power scheme. -/
instance moduleGlobalSections (F : PresheafOfModules.{u} (structureRingCatPresheaf S))
    (A : Thickening S) :
    Module ↥(A.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.thickening.target.scheme.Opens))) (F.obj (op A)) :=
  inferInstanceAs (Module ((structureRingPresheaf S).obj (op A)) (F.obj (op A)))

/-- **An `S`-derivation on the big crystalline category.**  For a presheaf `F` of modules over
the structure presheaf of `CRIS(X/S)`, this is a map of presheaves of abelian groups
`𝒪_{X/S} → F` such that for every object `(U, T, δ)` and *every* open `V ⊆ S` through which the
structure morphism `T → S` factors, the induced map `Γ(T, 𝒪_T) → Γ(T, F)` is a divided power
`Γ(V, 𝒪_V)`-derivation.  This is the big-site analogue of [Stacks, Tag 07IX]; the definition of
the source, on the small site `Cris(X/S)` with coefficients in a sheaf `ℱ` of
`𝒪_{X/S}`-modules, is `Crystalline.GlobalCrystallineSituation.SmallSite.SDerivation` applied to
`ℱ`. -/
structure SDerivation (F : PresheafOfModules.{u} (structureRingCatPresheaf S)) where
  /-- The map on the global sections of the ambient divided power scheme of an object. -/
  app (A : Thickening S) : Γ(A.thickening.target.scheme, ⊤) → F.obj (op A)
  /-- The maps on sections commute with the restriction maps of `CRIS(X/S)`. -/
  naturality {A B : Thickening S} (g : A ⟶ B) (x : Γ(B.thickening.target.scheme, ⊤)) :
    F.map g.op (app B x) = app A ((structureRingPresheaf S).map g.op x)
  /-- For every open `V` of the divided power base through which `T → S` factors, the map on
  sections is a divided power `Γ(V, 𝒪_V)`-derivation. -/
  dividedPowerDerivation (A : Thickening S) (V : S.S.scheme.Opens)
      (h : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(S.S.scheme, V)
      (A.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.thickening.target.scheme.Opens)))
      (A.toBase.hom.appLE V ⊤ h).hom (F.obj (op A))
  /-- The divided power derivation at `(U, T, δ)` above `V` is the map on sections there. -/
  dividedPowerDerivation_apply (A : Thickening S) (V : S.S.scheme.Opens)
      (h : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V)
      (x : Γ(A.thickening.target.scheme, ⊤)) :
    (dividedPowerDerivation A V h).toDerivation x = app A x

namespace SDerivation

variable {S} {F : PresheafOfModules.{u} (structureRingCatPresheaf S)}

/-- An `S`-derivation is determined by its maps on sections. -/
@[ext]
theorem ext {D E : SDerivation S F} (h : ∀ A x, D.app A x = E.app A x) : D = E := by
  obtain ⟨appD, _, derD, hD⟩ := D
  obtain ⟨appE, _, derE, hE⟩ := E
  have happ : appD = appE := funext fun A ↦ funext fun x ↦ h A x
  subst happ
  have hder : derD = derE := by
    funext A V hAV
    exact DividedPowerDerivation.ext fun x ↦ (hD A V hAV x).trans (hE A V hAV x).symm
  subst hder
  rfl

/-- The map on sections at `A` is the divided power derivation above the open `⊤` of `S`. -/
private theorem coe_dividedPowerDerivation_top (D : SDerivation S F) (A : Thickening S) :
    ⇑(D.dividedPowerDerivation A ⊤ (le_preimage_top A.toBase.hom ⊤)).toDerivation = D.app A :=
  funext (D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.toBase.hom ⊤))

/-- An `S`-derivation is additive on sections. -/
@[simp]
theorem app_add (D : SDerivation S F) (A : Thickening S)
    (x y : Γ(A.thickening.target.scheme, ⊤)) :
    D.app A (x + y) = D.app A x + D.app A y := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation A ⊤ (le_preimage_top A.toBase.hom ⊤)).map_add x y

/-- An `S`-derivation sends the zero section to zero. -/
@[simp]
theorem app_zero (D : SDerivation S F) (A : Thickening S) : D.app A 0 = 0 := by
  rw [← coe_dividedPowerDerivation_top]
  exact (D.dividedPowerDerivation A ⊤ (le_preimage_top A.toBase.hom ⊤)).map_zero

/-- **A universal `S`-derivation.**  Every `S`-derivation of the structure presheaf of `CRIS(X/S)`
is obtained from it by a unique map of presheaves of modules. -/
def IsUniversal (D : SDerivation S F) : Prop :=
  ∀ (G : PresheafOfModules.{u} (structureRingCatPresheaf S)) (E : SDerivation S G),
    ∃! φ : F ⟶ G, ∀ (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)),
      φ.app (op A) (D.app A x) = E.app A x

/-- Two maps out of a universal `S`-derivation inducing the same `S`-derivation are equal. -/
theorem IsUniversal.hom_ext {D : SDerivation S F} (hD : D.IsUniversal)
    {G : PresheafOfModules.{u} (structureRingCatPresheaf S)} {E : SDerivation S G} {φ ψ : F ⟶ G}
    (hφ : ∀ (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)),
      φ.app (op A) (D.app A x) = E.app A x)
    (hψ : ∀ (A : Thickening S) (x : Γ(A.thickening.target.scheme, ⊤)),
      ψ.app (op A) (D.app A x) = E.app A x) :
    φ = ψ :=
  (hD G E).unique hφ hψ

end SDerivation

end GlobalCrystallineSituation

end Crystalline

end
