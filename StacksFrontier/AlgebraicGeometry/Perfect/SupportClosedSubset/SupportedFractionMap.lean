module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData

/-!
# The cohomology class of a section divided by the product of the equations

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions cutting out the closed
subscheme `Z ⊆ X`, and let `ℱ` be an `𝒪_X`-module.  A local section `s` of `ℱ` determines the
local section `s / (f₁ ⋯ f_c)` of `ℱ_{1…c}`, the direct image of `ℱ` from the open where the
product of the equations is invertible, and the class of that fraction in the cokernel of the
last differential of the extended alternating Čech complex of Tag 0G7I depends only on `s`
modulo the image of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`.  The resulting map

`Coker((f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ) ⟶ Coker(⨁ᵢ ℱ_{1…î…c} ⟶ ℱ_{1…c})`

is the map `c_{f₁,…,f_c}` of Tag 0G7Q pushed forward along the closed immersion `i : Z → X`:
the source is `i_* i^*ℱ`, the target is `i_* ℋ^c_Z(ℱ)` by Tag 0G7M, and `i_*` is fully faithful.

## Main definitions

* `globalSmul`: multiplication by a global section of the structure sheaf, as an endomorphism of
  an `𝒪_X`-module.
* `equationsMultiplication`: the map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, whose cokernel is `i_* i^*ℱ`.
* `fractionCochain` and `fractionHom`: the fraction `s / (f_{i₀} ⋯ f_{i_p})` on each
  principal-open intersection, and the morphism of `𝒪_X`-modules it defines.
* `signedFaceProjector`: the signed projector onto the component indexed by a tuple omitting
  one index.
* `lastDif`: the last differential of the extended alternating Čech complex.
* `supportedFractionClass`: the class of the fraction `s / (f₁ ⋯ f_c)`, as a morphism
  `Coker((f₁, …, f_c)) ⟶ Coker(⨁ᵢ ℱ_{1…î…c} ⟶ ℱ_{1…c})`.

## Main results

* `restrictedModuleSection_smul` and `restrictedModuleSection_restrict`: the sectionwise
  identification of a direct image of a restriction is semilinear for the restriction of
  scalars, and compatible with restriction of the ambient open.
* `fractionHom_secIso`: `fractionHom` is the fraction with numerator the given section and
  denominator the product of the equations; `fractionHom_naturality`: it is natural in the
  coefficient module.
* `globalSmul_comp_fractionHom_one`, `globalSmul_comp_fractionHom_succ` and
  `globalSmul_comp_fractionHom_comp_π`: the fraction with numerator `fᵢ s` is the image of a
  cochain under the last differential, which is what makes the class of `s / (f₁ ⋯ f_c)` depend
  only on `s` modulo the equations.
* `supportedFractionClass_mk`: the value of the class map on the class of a section `s` is the
  class of the fraction `s / (f₁ ⋯ f_c)`.

## Implementation notes

The family is written `f : Fin (d + 1) → Γ(X, ⊤)` wherever the last differential is needed: the
empty family has none, and for the empty family the extended alternating Čech complex is the
coefficient module itself, so the class map would be the identity.

The fraction divides by the product of the equations through `Ring.inverse`, a function on the
ring of sections rather than a choice of inverse: on the principal-open intersection the product
is invertible and the inverse of an element of a monoid is unique, so nothing is chosen.  The
resulting morphism of modules is assembled from its action on sections by
`Stacks.AlgebraicGeometry.ModuleLimits.homOfSections`, which needs that action to be additive,
homogeneous and compatible with restriction; the latter two are `secIso_smul` and
`secIso_restrict`, proved from the corresponding statements for
`Stacks.Perfect.ExtendedAlternatingCech.restrictedModuleSection`.

That the numerator only matters modulo the equations is proved by exhibiting the fraction with
numerator `fᵢ s` as the image under the last differential of the cochain whose only nonzero
component is `± s / (f₁ ⋯ f̂ᵢ ⋯ f_c)` in the `i`-th face.  That component is cut out of the whole
fraction cochain by `signedFaceProjector`, so the cochain is a morphism of modules and no
glueing is needed; for a single equation the face is the empty intersection and the cochain is
the section itself.  The denominators are compared through the factorisation
`f₁ ⋯ f_c = fᵢ ⋅ (f₁ ⋯ f̂ᵢ ⋯ f_c)`.

The two modules between which the class map goes are the ones Tag 0G7Q displays.  The
identification of `Coker((f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ)` with `i_* i^*ℱ`, and the descent of the
map along the fully faithful `i_*` to the map `i^*ℱ ⟶ ℋ^c_Z(ℱ)` of Tag 0G7Q, are not carried
out here.  Functoriality in the coefficient module is proved for the fraction morphism
(`fractionHom_naturality`); the induced square for the class map between the two cokernels is
not assembled.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)
open Stacks.AlgebraicGeometry.RelativeMayerVietoris (pushRestrict)
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance] Classical.propDecidable

variable {X : Scheme.{u}}

/-! ### Restrictions of sections of the structure sheaf -/

/-- Two successive restrictions of a section of the structure sheaf compose. -/
public theorem ringMap_map_apply {W₁ W₂ W₃ : X.Opens} (g : W₂ ⟶ W₁) (h : W₃ ⟶ W₂)
    (r : Γ(X, W₁)) :
    X.presheaf.map h.op (X.presheaf.map g.op r) = X.presheaf.map (h ≫ g).op r := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]

/-- A composite of two restrictions of a section of the structure sheaf is the canonical
restriction. -/
public theorem ringMap_collapse {W₀ W₁ W₂ : X.Opens} (g₁ : W₁ ⟶ W₀) (g₂ : W₂ ⟶ W₁)
    (g : W₂ ⟶ W₀) (r : Γ(X, W₀)) :
    X.presheaf.map g₂.op (X.presheaf.map g₁.op r) = X.presheaf.map g.op r := by
  rw [ringMap_map_apply, Subsingleton.elim (g₂ ≫ g₁) g]

/-- A restriction map of the structure sheaf carries the inverse of a unit to the inverse of
its image: the inverse of an element of a monoid is unique. -/
public theorem map_ringInverse {W₁ W₂ : X.Opens} (g : W₂ ⟶ W₁) {r : Γ(X, W₁)}
    (h : IsUnit r) :
    X.presheaf.map g.op (Ring.inverse r) = Ring.inverse (X.presheaf.map g.op r) := by
  obtain ⟨v, rfl⟩ := h
  rw [Ring.inverse_unit]
  have himage : X.presheaf.map g.op (v : Γ(X, W₁)) =
      ((Units.map ((X.presheaf.map g.op).hom : Γ(X, W₁) →* Γ(X, W₂)) v :
        Γ(X, W₂)ˣ) : Γ(X, W₂)) := rfl
  rw [himage, Ring.inverse_unit]
  rfl

/-! ### Multiplication by a global section -/

/-- Multiplication by a global section of the structure sheaf, as an endomorphism of a sheaf of
modules: on sections over an open `V` it multiplies by the restriction of the global section. -/
public def globalSmul (r : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  homOfSections (fun V z => X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r • z)
    (fun _ _ _ => smul_add _ _ _)
    (fun _ ρ z => by rw [smul_smul, smul_smul, mul_comm])
    (fun U V h m => by
      rw [Scheme.Modules.map_smul M (homOfLE h)]
      congr 1
      exact (ringMap_collapse (homOfLE (show V ≤ ⊤ from le_top)) (homOfLE h)
        (homOfLE (show U ≤ ⊤ from le_top)) r).symm)

/-- On sections over an open `V`, `globalSmul r M` multiplies by the restriction of `r` to `V`. -/
@[simp]
public theorem globalSmul_app (r : Γ(X, ⊤)) (M : X.Modules) (V : X.Opens) (z : Γ(M, V)) :
    (globalSmul r M).app V z =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r • z :=
  rfl

/-! ### Elementary facts about inverses and signs -/

/-- Multiplying by a unit undoes multiplication by its inverse. -/
public theorem smul_ringInverse_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {r : R} (h : IsUnit r) (x : M) :
    r • (Ring.inverse r • x) = x := by
  rw [smul_smul, Ring.mul_inverse_cancel r h, one_smul]

/-- Dividing by a unit undoes multiplication by it. -/
public theorem ringInverse_smul_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {r : R} (h : IsUnit r) (x : M) :
    Ring.inverse r • (r • x) = x := by
  rw [smul_smul, Ring.inverse_mul_cancel r h, one_smul]

/-- If a unit `b` is a factor of a unit `v = a * b`, then the inverse of `b` is `a` times the
inverse of `v`. -/
public theorem ringInverse_eq_mul {R : Type*} [CommRing R] {a b v : R}
    (hb : IsUnit b) (hv : IsUnit v) (h : v = a * b) :
    Ring.inverse b = Ring.inverse v * a := by
  refine hb.mul_left_injective ?_
  calc Ring.inverse b * b = 1 := Ring.inverse_mul_cancel b hb
    _ = v * Ring.inverse v := (Ring.mul_inverse_cancel v hv).symm
    _ = Ring.inverse v * a * b := by rw [h]; ring

/-- The square of a Čech sign acts trivially. -/
public theorem sign_smul_sign {M : Type*} [AddCommGroup M] (n : ℕ) (x : M) :
    ((-1 : ℤ) ^ n) • (((-1 : ℤ) ^ n) • x) = x := by
  rw [← mul_zsmul]
  have h : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
    rw [← pow_add, show n + n = 2 * n from (two_mul n).symm, pow_mul]
    norm_num
  rw [h, one_zsmul]

/-! ### Units from principal opens -/

/-- A global function is invertible on every open contained in its principal open. -/
public theorem isUnit_res_of_le_basicOpen {V : X.Opens} (r : Γ(X, ⊤))
    (hV : V ≤ X.basicOpen r) :
    IsUnit (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r) := by
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (show X.basicOpen r ≤ ⊤ from le_top)).op r) :=
    X.toRingedSpace.isUnit_res_basicOpen r
  have hmap := hunit.map (X.presheaf.map (homOfLE hV).op).hom
  convert hmap using 1
  exact (ringMap_collapse (homOfLE (show X.basicOpen r ≤ ⊤ from le_top)) (homOfLE hV)
    (homOfLE (show V ≤ ⊤ from le_top)) r).symm

variable {c : ℕ}

/-- On the intersection of an open with the principal opens of an increasing tuple, the product
of the corresponding equations is invertible. -/
public theorem isUnit_prodEquations (f : Fin c → Γ(X, ⊤)) (V : X.Opens) (p : ℕ)
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    IsUnit (X.presheaf.map (homOfLE (show
      CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top)).op
        (∏ k, f (q.1 k))) := by
  rw [map_prod, IsUnit.prod_univ_iff]
  intro k
  exact isUnit_res_of_le_basicOpen (f (q.1 k)) ((iInf_le _ k).trans inf_le_right)

/-- Shrinking the ambient open shrinks the principal-open intersection. -/
public theorem interMonoOpen (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    (q : CechCochains.OrdIndex (I := Fin c) p) {W V : X.Opens} (hWV : W ≤ V) :
    CechCochains.inter (fun i => W ⊓ X.basicOpen (f i)) q.1 ≤
      CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 := by
  simpa only [CechCochains.inter] using
    iInf_mono fun _ : Fin (p + 1) => inf_le_inf hWV (le_refl _)

/-! ### The sectionwise identification is semilinear and restricts -/

/-- The `Γ(X, V)`-action on the sections over `V` of the direct image of a restriction is the
action of the restriction of the scalar to the intersection. -/
private theorem pushRestrict_smul (U : X.Opens) (F : X.Modules) (V : X.Opens)
    (ρ : Γ(X, V)) (w : Γ(pushRestrict F U, V))
    (a : Γ(F, U.ι ''ᵁ (U.ι ⁻¹ᵁ V)))
    (ha : a = (ρ • w : Γ(pushRestrict F U, V))) :
    a = X.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op ρ •
      (show Γ(F, U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) from w) := by
  have h₁ := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι F (U.ι ⁻¹ᵁ V)
    (U.ι.app V ρ) w
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Scheme.Opens.ι_appIso,
    Iso.refl_inv] at h₁
  rw [ha]
  exact h₁

/-- The image under the inclusion of an open of the preimage of an open is monotone in the
latter. -/
private theorem imagePreimageMono (U : X.Opens) {V W : X.Opens} (h : W ≤ V) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ V) :=
  U.ι.image_mono fun _ hx => h hx

/-- Restriction of sections of the direct image of a restriction is restriction of sections of
the module. -/
private theorem pushRestrict_map (U : X.Opens) (F : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (w : Γ(pushRestrict F U, V)) (a : Γ(F, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)))
    (ha : a = (pushRestrict F U).presheaf.map (homOfLE h).op w) :
    a = F.presheaf.map (homOfLE (imagePreimageMono U h)).op
      (show Γ(F, U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) from w) := by
  rw [ha]
  rfl

/-- The sectionwise identification of a direct image of a restriction is semilinear: a scalar
on the ambient open passes through it as its restriction to the principal-open
intersection. -/
public theorem restrictedModuleSection_smul (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (q : CechCochains.OrdIndex (I := Fin c) p) (V : X.Opens) (ρ : Γ(X, V))
    (z : Γ(restrictedModule f F p q, V)) :
    restrictedModuleSection f F p q V (ρ • z) =
      X.presheaf.map (homOfLE (interLe f p q V)).op ρ •
        restrictedModuleSection f F p q V z := by
  rw [restrictedModuleSection_apply, restrictedModuleSection_apply,
    show (toRPinv f F p q).app V (ρ • z) = ρ • (toRPinv f F p q).app V z from
      Scheme.Modules.Hom.app_smul _ _ _,
    pushRestrict_smul (equationsOpen f p q) F V ρ ((toRPinv f F p q).app V z) _ rfl,
    Scheme.Modules.map_smul F (eqToHom (himage f p q V).symm)]
  congr 1
  exact ringMap_collapse (homOfLE ((equationsOpen f p q).ι.image_preimage_le V))
    (eqToHom (himage f p q V).symm) (homOfLE (interLe f p q V)) ρ

/-- The sectionwise identification of a direct image of a restriction commutes with restriction
of the ambient open. -/
public theorem restrictedModuleSection_restrict (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (q : CechCochains.OrdIndex (I := Fin c) p) {W V : X.Opens} (hWV : W ≤ V)
    (z : Γ(restrictedModule f F p q, V)) :
    restrictedModuleSection f F p q W
        ((restrictedModule f F p q).presheaf.map (homOfLE hWV).op z) =
      F.presheaf.map (homOfLE (interMonoOpen f p q hWV)).op
        (restrictedModuleSection f F p q V z) := by
  rw [restrictedModuleSection_apply, restrictedModuleSection_apply,
    show (toRPinv f F p q).app W ((restrictedModule f F p q).presheaf.map (homOfLE hWV).op z) =
        (pushRestrict F (equationsOpen f p q)).presheaf.map (homOfLE hWV).op
          ((toRPinv f F p q).app V z) from
      (app_naturality (toRPinv f F p q) (homOfLE hWV) z).symm,
    pushRestrict_map (equationsOpen f p q) F hWV ((toRPinv f F p q).app V z) _ rfl]
  exact collapse2_eq F _ _ _ _ _

/-! ### The same statements for the sections of a positive-degree term -/

/-- The sections of a positive-degree term of the extended alternating Čech complex are
identified with the ordered Čech cochains semilinearly. -/
public theorem secIso_smul (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ) (V : X.Opens)
    (ρ : Γ(X, V)) (x : Γ(prodTerm f F p, V)) (q : CechCochains.OrdIndex (I := Fin c) p) :
    secIso f F p V (ρ • x) q =
      X.presheaf.map (homOfLE (interLe f p q V)).op ρ • secIso f F p V x q := by
  rw [secIso_apply, secIso_apply,
    show (Pi.π (fun t : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p t)
        q).app V (ρ • x) =
      ρ • (Pi.π (fun t : CechCochains.OrdIndex (I := Fin c) p =>
        restrictedModule f F p t) q).app V x from Scheme.Modules.Hom.app_smul _ _ _,
    restrictedModuleSection_smul]

/-- The identification of the sections of a positive-degree term with the ordered Čech cochains
commutes with restriction. -/
public theorem secIso_restrict (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {W V : X.Opens} (hWV : W ≤ V) (x : Γ(prodTerm f F p, V))
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    secIso f F p W ((prodTerm f F p).presheaf.map (homOfLE hWV).op x) q =
      F.presheaf.map (homOfLE (interMonoOpen f p q hWV)).op (secIso f F p V x q) := by
  rw [secIso_apply, secIso_apply,
    show (Pi.π (fun t : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p t)
          q).app W ((prodTerm f F p).presheaf.map (homOfLE hWV).op x) =
        (restrictedModule f F p q).presheaf.map (homOfLE hWV).op
          ((Pi.π (fun t : CechCochains.OrdIndex (I := Fin c) p =>
            restrictedModule f F p t) q).app V x) from
      (app_naturality (Pi.π (fun t : CechCochains.OrdIndex (I := Fin c) p =>
        restrictedModule f F p t) q) (homOfLE hWV) x).symm,
    restrictedModuleSection_restrict]

/-! ### The fraction cochain -/

/-- The ordered Čech cochain of fractions `s / (f_{i₀} ⋯ f_{i_p})`: on the intersection of the
ambient open with the principal opens of an increasing tuple, the product of the corresponding
equations is invertible, and the cochain divides the restriction of the numerator by it. -/
public def fractionCochain (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ) (V : X.Opens)
    (s : Γ(F, V)) :
    CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p :=
  fun q => Ring.inverse (X.presheaf.map (homOfLE (show
      CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top)).op
        (∏ k, f (q.1 k))) • F.presheaf.map (homOfLE (interLe f p q V)).op s

/-- The fraction cochain, unfolded. -/
public theorem fractionCochain_apply (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (V : X.Opens) (s : Γ(F, V)) (q : CechCochains.OrdIndex (I := Fin c) p) :
    fractionCochain f F p V s q =
      Ring.inverse (X.presheaf.map (homOfLE (show
        CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top)).op
          (∏ k, f (q.1 k))) • F.presheaf.map (homOfLE (interLe f p q V)).op s := rfl

/-- Multiplying the fraction by the product of the equations recovers the numerator. -/
public theorem prodEquations_smul_fractionCochain (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (p : ℕ) (V : X.Opens) (s : Γ(F, V)) (q : CechCochains.OrdIndex (I := Fin c) p) :
    X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top)).op
        (∏ k, f (q.1 k)) • fractionCochain f F p V s q =
      F.presheaf.map (homOfLE (interLe f p q V)).op s :=
  smul_ringInverse_smul (isUnit_prodEquations f V p q) _

/-- The fraction cochain is additive in its numerator. -/
public theorem fractionCochain_add (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (V : X.Opens) (s t : Γ(F, V)) :
    fractionCochain f F p V (s + t) =
      fractionCochain f F p V s + fractionCochain f F p V t := by
  funext q
  rw [CechCochains.OrdCochain.add_apply, fractionCochain_apply, fractionCochain_apply,
    fractionCochain_apply, map_add, smul_add]

/-- The fraction cochain is homogeneous in its numerator. -/
public theorem fractionCochain_smul (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (V : X.Opens) (ρ : Γ(X, V)) (s : Γ(F, V))
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    fractionCochain f F p V (ρ • s) q =
      X.presheaf.map (homOfLE (interLe f p q V)).op ρ • fractionCochain f F p V s q := by
  rw [fractionCochain_apply, fractionCochain_apply,
    Scheme.Modules.map_smul F (homOfLE (interLe f p q V)), smul_smul, smul_smul, mul_comm]

/-- The fraction cochain commutes with restriction of the ambient open. -/
public theorem fractionCochain_restrict (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {W V : X.Opens} (hWV : W ≤ V) (s : Γ(F, V))
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    fractionCochain f F p W (F.presheaf.map (homOfLE hWV).op s) q =
      F.presheaf.map (homOfLE (interMonoOpen f p q hWV)).op
        (fractionCochain f F p V s q) := by
  rw [fractionCochain_apply, fractionCochain_apply,
    Scheme.Modules.map_smul F (homOfLE (interMonoOpen f p q hWV)),
    map_ringInverse (homOfLE (interMonoOpen f p q hWV)) (isUnit_prodEquations f V p q),
    ringMap_collapse (homOfLE (show
        CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top))
      (homOfLE (interMonoOpen f p q hWV)) (homOfLE (show
        CechCochains.inter (fun i => W ⊓ X.basicOpen (f i)) q.1 ≤ ⊤ from le_top))]
  congr 1
  exact (collapse2_eq F (homOfLE (interLe f p q V)) (homOfLE (interMonoOpen f p q hWV))
    (homOfLE hWV) (homOfLE (interLe f p q W)) s).symm

/-- Two morphisms of `𝒪_X`-modules agreeing on all sections are equal. -/
private theorem hom_ext_app {F G : X.Modules} {φ ψ : F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app V s = ψ.app V s) : φ = ψ :=
  Scheme.Modules.hom_ext _ _ fun V => AddCommGrpCat.hom_ext (AddMonoidHom.ext (h V))

/-! ### The fraction as a morphism of modules -/

/-- The morphism of `𝒪_X`-modules carrying a section `s` to the cochain of fractions
`s / (f_{i₀} ⋯ f_{i_p})`. -/
public def fractionHom (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ) :
    F ⟶ prodTerm f F p :=
  homOfSections (fun V s => (secIso f F p V).symm (fractionCochain f F p V s))
    (fun _ s t => by rw [fractionCochain_add, map_add])
    (fun V ρ s => by
      refine (secIso f F p V).injective ?_
      rw [(secIso f F p V).apply_symm_apply]
      funext q
      rw [secIso_smul, (secIso f F p V).apply_symm_apply, fractionCochain_smul])
    (fun U V h s => by
      refine (secIso f F p U).injective ?_
      rw [(secIso f F p U).apply_symm_apply]
      funext q
      rw [secIso_restrict, (secIso f F p V).apply_symm_apply, fractionCochain_restrict])

/-- The sections of `fractionHom` are the fraction cochain. -/
@[simp]
public theorem fractionHom_secIso (f : Fin c → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (V : X.Opens) (s : Γ(F, V)) (q : CechCochains.OrdIndex (I := Fin c) p) :
    secIso f F p V ((fractionHom f F p).app V s) q = fractionCochain f F p V s q := by
  rw [fractionHom, homOfSections_app, (secIso f F p V).apply_symm_apply]

/-- The fraction morphism is natural in the coefficient module: dividing by the product of the
equations commutes with a morphism of coefficient modules. -/
public theorem fractionHom_naturality (f : Fin c → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G)
    (p : ℕ) :
    fractionHom f F p ≫ prodMap f φ p = φ ≫ fractionHom f G p := by
  refine hom_ext_app fun V s => ?_
  show (prodMap f φ p).app V ((fractionHom f F p).app V s) =
    (fractionHom f G p).app V (φ.app V s)
  refine (secIso f G p V).injective ?_
  funext q
  rw [prodMap_section, fractionHom_secIso, fractionHom_secIso, fractionCochain_apply,
    fractionCochain_apply, Scheme.Modules.Hom.app_smul, app_naturality]

/-! ### The top and face index tuples -/

/-- The unique strictly increasing `(n + 1)`-tuple in `Fin (n + 1)`. -/
public def topIndex (n : ℕ) : CechCochains.OrdIndex (I := Fin (n + 1)) n :=
  ⟨id, strictMono_id⟩

/-- There is only one strictly increasing `(n + 1)`-tuple in `Fin (n + 1)`. -/
public theorem topIndex_unique {n : ℕ} (q : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    q = topIndex n := by
  have hsurj : Function.Surjective q.1 := Finite.injective_iff_surjective.mp q.2.injective
  refine Subtype.ext (q.2.eq_of_range_eq (strictMono_id (α := Fin (n + 1))) ?_)
  rw [hsurj.range_eq]
  simp [topIndex]

/-- The strictly increasing `(n + 1)`-tuple in `Fin (n + 2)` omitting the index `i`. -/
public def faceIndex (n : ℕ) (i : Fin (n + 2)) :
    CechCochains.OrdIndex (I := Fin (n + 2)) n :=
  ⟨i.succAbove, Fin.strictMono_succAbove i⟩

/-- Distinct omitted indices give distinct tuples. -/
public theorem faceIndex_injective {n : ℕ} : Function.Injective (faceIndex n) := fun _ _ h =>
  Fin.succAbove_left_injective (congrArg Subtype.val h)

/-- On the intersection belonging to the full tuple every equation is invertible. -/
public theorem isUnit_equation_interTop {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (V : X.Opens)
    (i : Fin (n + 1)) :
    IsUnit (X.presheaf.map (homOfLE (show
      CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex n).1 ≤ ⊤ from le_top)).op
        (f i)) :=
  isUnit_res_of_le_basicOpen (f i) ((iInf_le _ i).trans inf_le_right)

/-- On the intersection belonging to the full tuple every product of equations is
invertible. -/
public theorem isUnit_prod_interTop {n m : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (V : X.Opens)
    (g : Fin m → Fin (n + 1)) :
    IsUnit (X.presheaf.map (homOfLE (show
      CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex n).1 ≤ ⊤ from le_top)).op
        (∏ k, f (g k))) := by
  rw [map_prod, IsUnit.prod_univ_iff]
  intro k
  exact isUnit_equation_interTop f V (g k)

/-! ### Keeping one signed component of a positive-degree term -/

/-- The endomorphism of a positive-degree term of the extended alternating Čech complex keeping
the component indexed by the tuple that omits the index `i`, with the Čech sign of `i`, and
killing the other components. -/
public def signedFaceProjector {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤)) (F : X.Modules)
    (i : Fin (e + 2)) :
    prodTerm f F e ⟶ prodTerm f F e :=
  Pi.lift fun q => if q = faceIndex e i then
      ((-1 : ℤ) ^ (i : ℕ)) •
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin (e + 2)) e => restrictedModule f F e t) q
    else 0

/-- The signed projector keeps the signed component indexed by the tuple omitting `i` and kills
the others. -/
public theorem secIso_signedFaceProjector {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤)) (F : X.Modules)
    (i : Fin (e + 2)) (V : X.Opens) (x : Γ(prodTerm f F e, V))
    (q : CechCochains.OrdIndex (I := Fin (e + 2)) e) :
    secIso f F e V ((signedFaceProjector f F i).app V x) q =
      if q = faceIndex e i then ((-1 : ℤ) ^ (i : ℕ)) • secIso f F e V x q else 0 := by
  have hπ : (Pi.π (fun t : CechCochains.OrdIndex (I := Fin (e + 2)) e =>
        restrictedModule f F e t) q).app V ((signedFaceProjector f F i).app V x) =
      (appApplyHom V x) (signedFaceProjector f F i ≫
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin (e + 2)) e =>
          restrictedModule f F e t) q) := rfl
  have h₁ : signedFaceProjector f F i ≫
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin (e + 2)) e =>
          restrictedModule f F e t) q =
      if q = faceIndex e i then
          ((-1 : ℤ) ^ (i : ℕ)) •
            Pi.π (fun t : CechCochains.OrdIndex (I := Fin (e + 2)) e =>
              restrictedModule f F e t) q
        else 0 :=
    Pi.lift_π _ q
  rw [secIso_apply, hπ, h₁]
  by_cases hq : q = faceIndex e i
  · rw [ite_eq_left hq, ite_eq_left hq, map_zsmul, map_zsmul, secIso_apply]
    rfl
  · rw [ite_eq_right hq, ite_eq_right hq, map_zero, map_zero]

/-! ### Denominators of the full tuple and of its faces -/

section Denominators

variable {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤)) (V : X.Opens)

/-- The intersection belonging to the full tuple is contained in the intersection belonging to
the tuple omitting one index. -/
public theorem interTop_le_interFace (i : Fin (e + 2)) :
    CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤
      CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (faceIndex e i).1 :=
  CechCochains.inter_le_omit (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 i

/-- The product of all the equations is the `i`-th equation times the product of the others. -/
public theorem prodEquations_top_eq (i : Fin (e + 2)) :
    X.presheaf.map (homOfLE (show
          CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤ ⊤ from
            le_top)).op (∏ k, f ((topIndex (e + 1)).1 k)) =
      X.presheaf.map (homOfLE (show
          CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤ ⊤ from
            le_top)).op (f i) *
        X.presheaf.map (homOfLE (show
          CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤ ⊤ from
            le_top)).op (∏ k, f ((faceIndex e i).1 k)) := by
  rw [← map_mul]
  congr 1
  show (∏ k, f k) = f i * ∏ k, f (i.succAbove k)
  exact Fin.prod_univ_succAbove f i

end Denominators


/-! ### The last differential -/

/-- The last differential of the extended alternating Čech complex of `c = d + 1` equations,
from degree `d` to the top degree `d + 1`. -/
public def lastDif {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) :
    term f F d ⟶ prodTerm f F d :=
  dif f F d

/-- `lastDif` is the last differential of the extended alternating Čech complex. -/
public theorem cplx_d_lastDif {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) :
    (cplx f F).d d (d + 1) = lastDif f F :=
  CochainComplex.of_d (term f F) (dif f F) d

/-- For a single equation the last differential is the augmentation. -/
public theorem lastDif_zero (f : Fin 1 → Γ(X, ⊤)) (F : X.Modules) :
    lastDif f F = difZero f F := rfl

/-- For at least two equations the last differential is the signed alternating restriction
map. -/
public theorem lastDif_succ {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤)) (F : X.Modules) :
    lastDif f F = difSucc f F e := rfl

/-! ### The fraction with numerator one equation is a boundary -/

/-- The restriction to the full principal-open intersection of the fraction belonging to the
tuple omitting `i` is the fraction belonging to the full tuple with numerator `fᵢ s`. -/
public theorem fractionCochain_face {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (s : Γ(F, V)) (i : Fin (e + 2)) :
    F.presheaf.map (homOfLE (interTop_le_interFace f V i)).op
        (fractionCochain f F e V s (faceIndex e i)) =
      fractionCochain f F (e + 1) V
        (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (f i) • s)
        (topIndex (e + 1)) := by
  have hA : X.presheaf.map (homOfLE (interLe f (e + 1) (topIndex (e + 1)) V)).op
        (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (f i)) =
      X.presheaf.map (homOfLE (show
        CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤ ⊤ from
          le_top)).op (f i) :=
    ringMap_collapse _ _ _ (f i)
  have hS : F.presheaf.map (homOfLE (interTop_le_interFace f V i)).op
        (F.presheaf.map (homOfLE (interLe f e (faceIndex e i) V)).op s) =
      F.presheaf.map (homOfLE (interLe f (e + 1) (topIndex (e + 1)) V)).op s :=
    collapse2 F (homOfLE (interLe f e (faceIndex e i) V))
      (homOfLE (interTop_le_interFace f V i))
      (homOfLE (interLe f (e + 1) (topIndex (e + 1)) V)) s
  rw [fractionCochain_apply, fractionCochain_apply,
    Scheme.Modules.map_smul F (homOfLE (interTop_le_interFace f V i)),
    map_ringInverse (homOfLE (interTop_le_interFace f V i))
      (isUnit_prodEquations f V e (faceIndex e i)),
    ringMap_collapse (homOfLE (show
        CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (faceIndex e i).1 ≤ ⊤ from le_top))
      (homOfLE (interTop_le_interFace f V i)) (homOfLE (show
        CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex (e + 1)).1 ≤ ⊤ from
          le_top)),
    ringInverse_eq_mul (isUnit_prod_interTop f V (faceIndex e i).1)
      (isUnit_prodEquations f V (e + 1) (topIndex (e + 1))) (prodEquations_top_eq f V i),
    Scheme.Modules.map_smul F (homOfLE (interLe f (e + 1) (topIndex (e + 1)) V)),
    hA, hS, smul_smul]

/-- For a single equation the fraction with numerator `f₀ s` is the restriction of `s`. -/
public theorem fractionCochain_one (f : Fin 1 → Γ(X, ⊤)) (F : X.Modules) (V : X.Opens)
    (s : Γ(F, V)) (i : Fin 1) :
    fractionCochain f F 0 V
        (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (f i) • s) (topIndex 0) =
      F.presheaf.map (homOfLE (interLe f 0 (topIndex 0) V)).op s := by
  have hprod : (∏ k, f ((topIndex 0).1 k)) = f i := by
    rw [Fin.prod_univ_one]
    exact congrArg f (Subsingleton.elim _ _)
  rw [fractionCochain_apply, Scheme.Modules.map_smul F (homOfLE (interLe f 0 (topIndex 0) V)),
    hprod, ringMap_collapse (homOfLE (show V ≤ ⊤ from le_top))
      (homOfLE (interLe f 0 (topIndex 0) V)) (homOfLE (show
        CechCochains.inter (fun k => V ⊓ X.basicOpen (f k)) (topIndex 0).1 ≤ ⊤ from le_top))
      (f i)]
  exact ringInverse_smul_smul (isUnit_equation_interTop f V i) _

/-- For a single equation the fraction with numerator `f₀ s` is the image of `s` under the
augmentation of the extended alternating Čech complex. -/
public theorem globalSmul_comp_fractionHom_one (f : Fin 1 → Γ(X, ⊤)) (F : X.Modules)
    (i : Fin 1) :
    globalSmul (f i) F ≫ fractionHom f F 0 = lastDif f F := by
  refine hom_ext_app fun V s => ?_
  show (fractionHom f F 0).app V ((globalSmul (f i) F).app V s) = (difZero f F).app V s
  refine (secIso f F 0 V).injective ?_
  funext q
  obtain rfl := topIndex_unique q
  exact (fractionHom_secIso f F 0 V ((globalSmul (f i) F).app V s) (topIndex 0)).trans
    ((fractionCochain_one f F V s i).trans (secIso_difZero f F V s (topIndex 0)).symm)

/-- For at least two equations the fraction with numerator `fᵢ s` is the image under the last
differential of the cochain whose only nonzero component is `± s / (f₁ ⋯ f̂ᵢ ⋯ f_c)` in the
`i`-th face. -/
public theorem globalSmul_comp_fractionHom_succ {e : ℕ} (f : Fin (e + 2) → Γ(X, ⊤))
    (F : X.Modules) (i : Fin (e + 2)) :
    globalSmul (f i) F ≫ fractionHom f F (e + 1) =
      (fractionHom f F e ≫ signedFaceProjector f F i) ≫ lastDif f F := by
  refine hom_ext_app fun V s => ?_
  show (fractionHom f F (e + 1)).app V ((globalSmul (f i) F).app V s) =
    (difSucc f F e).app V
      ((signedFaceProjector f F i).app V ((fractionHom f F e).app V s))
  refine (secIso f F (e + 1) V).injective ?_
  funext t
  obtain rfl := topIndex_unique t
  have hidx : ∀ j : Fin (e + 2),
      (⟨(topIndex (e + 1)).1 ∘ j.succAbove,
        CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩ :
          CechCochains.OrdIndex (I := Fin (e + 2)) e) = faceIndex e j := fun _ => rfl
  have hcc : ∀ j : Fin (e + 2),
      secIso f F e V ((signedFaceProjector f F i).app V ((fractionHom f F e).app V s))
          (⟨(topIndex (e + 1)).1 ∘ j.succAbove,
            CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩ :
              CechCochains.OrdIndex (I := Fin (e + 2)) e) =
        if j = i then ((-1 : ℤ) ^ (i : ℕ)) • fractionCochain f F e V s
            (⟨(topIndex (e + 1)).1 ∘ j.succAbove,
              CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩ :
                CechCochains.OrdIndex (I := Fin (e + 2)) e)
          else 0 := by
    intro j
    rw [secIso_signedFaceProjector, fractionHom_secIso]
    by_cases hj : j = i
    · rw [ite_eq_left ((hidx j).trans (congrArg (faceIndex e) hj)), ite_eq_left hj]
    · rw [ite_eq_right fun h => hj (faceIndex_injective ((hidx j).symm.trans h)),
        ite_eq_right hj]
  have h₁ : secIso f F (e + 1) V ((difSucc f F e).app V
          ((signedFaceProjector f F i).app V ((fractionHom f F e).app V s)))
        (topIndex (e + 1)) =
      CechCochains.ordD (fun k => V ⊓ X.basicOpen (f k)) (Scheme.Modules.presheaf F) e
        (secIso f F e V ((signedFaceProjector f F i).app V ((fractionHom f F e).app V s)))
        (topIndex (e + 1)) :=
    congrFun (secIso_difSucc f F e V _) (topIndex (e + 1))
  have h₂ : CechCochains.ordD (fun k => V ⊓ X.basicOpen (f k))
          (Scheme.Modules.presheaf F) e
          (secIso f F e V ((signedFaceProjector f F i).app V ((fractionHom f F e).app V s)))
          (topIndex (e + 1)) =
      F.presheaf.map (homOfLE (interTop_le_interFace f V i)).op
        (fractionCochain f F e V s (faceIndex e i)) := by
    rw [ordD_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun b _ hb => by rw [hcc b, ite_eq_right hb, map_zero, smul_zero]),
      hcc i, ite_eq_left (rfl : i = i), map_zsmul, sign_smul_sign, restr_eq]
    rfl
  exact (fractionHom_secIso f F (e + 1) V ((globalSmul (f i) F).app V s)
      (topIndex (e + 1))).trans
    ((fractionCochain_face f F V s i).symm.trans (h₂.symm.trans h₁.symm))

/-! ### The class of the fraction -/

/-- A composite that factors through a morphism is killed by the projection to its
cokernel. -/
private theorem comp_cokernelπ_eq_zero {A B C D : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ C)
    (δ : D ⟶ C) (Y : A ⟶ D) (h : φ ≫ ψ = Y ≫ δ) :
    φ ≫ ψ ≫ cokernel.π δ = 0 := by
  rw [← Category.assoc, h, Category.assoc, cokernel.condition, comp_zero]

/-- The class of the fraction `s / (f₁ ⋯ f_c)` in the cokernel of the last differential of the
extended alternating Čech complex is killed by multiplication by each equation. -/
public theorem globalSmul_comp_fractionHom_comp_π {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) (i : Fin (d + 1)) :
    globalSmul (f i) F ≫ fractionHom f F d ≫ cokernel.π (lastDif f F) = 0 := by
  cases d with
  | zero =>
      rw [← Category.assoc, globalSmul_comp_fractionHom_one f F i]
      exact cokernel.condition _
  | succ e =>
      exact comp_cokernelπ_eq_zero _ _ (lastDif f F)
        (fractionHom f F e ≫ signedFaceProjector f F i)
        (globalSmul_comp_fractionHom_succ f F i)

/-- The map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` given by multiplication by the equations.  Its cokernel
is `i_* i^*ℱ` for the closed immersion `i : Z → X` cut out by the equations. -/
public def equationsMultiplication (f : Fin c → Γ(X, ⊤)) (F : X.Modules) :
    (∐ fun _ : Fin c => F) ⟶ F :=
  Sigma.desc fun i => globalSmul (f i) F

/-- A morphism out of `ℱ` killing multiplication by each equation kills
`equationsMultiplication`. -/
public theorem equationsMultiplication_comp (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    {M : X.Modules} (ψ : F ⟶ M) (h : ∀ i, globalSmul (f i) F ≫ ψ = 0) :
    equationsMultiplication f F ≫ ψ = 0 := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, equationsMultiplication, Sigma.ι_desc, h i, comp_zero]

/-- **Stacks Project, Tag 0G7Q**, the class of the fraction `s / (f₁ ⋯ f_c)`.  With `X`,
`f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `ℱ` as in Tag 0G7I, this is the map

`Coker((f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ) ⟶ Coker(⨁ᵢ ℱ_{1…î…c} ⟶ ℱ_{1…c})`

carrying the class of a local section `s` of `ℱ` to the class of the fraction
`s / (f₁ ⋯ f_c)`, by `supportedFractionClass_mk`.  It is the direct image along the closed
immersion `i : Z → X` of the map `c_{f₁,…,f_c} : i^*ℱ ⟶ ℋ^c_Z(ℱ)` of the remark: its source is
`i_* i^*ℱ`, presented as the cokernel of `(f₁, …, f_c)` as the remark does, and its target is
`i_* ℋ^c_Z(ℱ)`, presented as the cokernel of the last differential of the extended alternating
Čech complex as the remark does, the two being identified by Tag 0G7M. -/
@[stacks 0G7Q "i_* of the remark's map c_{f₁,…,f_c}, between its two presentations; no descent"]
public def supportedFractionClass {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) :
    cokernel (equationsMultiplication f F) ⟶ cokernel (lastDif f F) :=
  cokernel.desc (equationsMultiplication f F)
    (fractionHom f F d ≫ cokernel.π (lastDif f F))
    (equationsMultiplication_comp f F _ (globalSmul_comp_fractionHom_comp_π f F))

/-- **Stacks Project, Tag 0G7Q.**  The class map sends the class of a local section `s` of `ℱ`
to the class of the fraction `s / (f₁ ⋯ f_c)` in the cokernel of the last differential of the
extended alternating Čech complex. -/
@[stacks 0G7Q "the value of the class map on the class of a section"]
public theorem supportedFractionClass_mk {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) :
    (supportedFractionClass f F).app V
        ((cokernel.π (equationsMultiplication f F)).app V s) =
      (cokernel.π (lastDif f F)).app V ((fractionHom f F d).app V s) := by
  have h : cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F =
      fractionHom f F d ≫ cokernel.π (lastDif f F) :=
    cokernel.π_desc _ _ _
  exact congrArg (fun φ : F ⟶ cokernel (lastDif f F) => φ.app V s) h

end Stacks.Perfect.SupportedFraction

end
