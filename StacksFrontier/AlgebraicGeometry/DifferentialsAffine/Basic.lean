module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Derivations of the structure sheaf on an affine open

Let `X` be a scheme, let `M` be an `𝒪_X`-module and let `U` be an affine open of `X`, so that
`A := Γ(X, U)` is the coordinate ring of `U`. A *derivation of the structure sheaf over `U`* is a
family of additive maps `Γ(X, W) → Γ(M, W)`, one for each open `W ⊆ U`, which satisfies the
Leibniz rule and commutes with the restriction maps. This file proves that such a family is the
same thing as a single additive Leibniz map `A → Γ(M, U)`: the family is determined by its value
on `U`, and every Leibniz map on `U` extends to a family.

This is the affine computation underlying the construction of the sheaf of relative differentials
of a morphism of schemes: once one knows that derivations of `𝒪_X` over an affine open are ring
derivations of its coordinate ring, the sections of `Ω_{X/S}` over an affine open can be computed.

## Main results

* `existsUnique_restrictions` is the bijection: a Leibniz additive map `Γ(X, U) → Γ(M, U)` is
  the value on `U` of a unique Leibniz, restriction-compatible family on the opens contained
  in `U`.
* `eq_of_eq_on_affineOpen` is its uniqueness half, stated separately because it is what one
  needs to recognise a derivation of sheaves from its effect on an affine open.
* `exists_restrictions` is its existence half.
* `restrictions_apply_eq_zero` records that the family annihilates the restrictions of whatever
  the given map on `U` annihilates, so the correspondence matches derivations relative to a base
  with ring derivations relative to a base.
* `addMonoidHom_eq_of_isLocalization` and `exists_addMonoidHom_of_isLocalization` are the
  ring-theoretic input: a derivation into a module over a localization is uniquely determined
  by, and can be freely prescribed on, the base ring.

## Implementation notes

The family of maps is handled as an unbundled datum: a function
`∀ W : X.Opens, W ≤ U → (Γ(X, W) →+ Γ(M, W))` together with the Leibniz rule and the restriction
compatibility as separate hypotheses. No new structure is introduced, so the results apply
verbatim to the component maps of any of the existing notions of a derivation of presheaves of
modules.

The existence half is a gluing argument over the basic opens of `U`, which form a basis of the
topology of `U`. On a basic open `D(g)` the sections of the structure sheaf are the localization
`A_g`, so extending the given map amounts to extending a derivation along a localization; this is
obtained from the universal property of the localization applied to the trivial square-zero
extension `TrivSqZeroExt Γ(X, D(g)) Γ(M, D(g))`, whose unit group sees only the first coordinate.
Prescribing a derivation is the same as prescribing a ring section of the projection of that
extension, and a ring map out of a localization is prescribed by its restriction to the base.

The uniqueness half is the Leibniz rule read on a localization: `g` acts invertibly on
`Γ(M, D(g))`, so `g^n • d (a / g^n)` is a combination of values on `A`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TrivSqZeroExt

universe u

namespace Stacks.AlgebraicGeometry.DifferentialsAffine

/-! ### Derivations into a module over a localization -/

/-- An additive map out of a localization `S` of `A` satisfying the Leibniz rule with respect to
a ring map `θ : S →+* B` and a `B`-module `N` is determined by its restriction along
`algebraMap A S`: the localized elements act invertibly on `N`. -/
theorem addMonoidHom_eq_of_isLocalization
    {A S B : Type*} [CommRing A] [CommRing S] [CommRing B] [Algebra A S] (P : Submonoid A)
    [IsLocalization P S] {N : Type*} [AddCommGroup N] [Module B N] (θ : S →+* B)
    (d d' : S →+ N)
    (hd : ∀ x y : S, d (x * y) = θ x • d y + θ y • d x)
    (hd' : ∀ x y : S, d' (x * y) = θ x • d' y + θ y • d' x)
    (h : ∀ a : A, d (algebraMap A S a) = d' (algebraMap A S a)) :
    d = d' := by
  ext x
  obtain ⟨⟨a, m⟩, hx⟩ := IsLocalization.surj P x
  dsimp only at hx
  have e1 := hd x (algebraMap A S (m : A))
  have e2 := hd' x (algebraMap A S (m : A))
  rw [hx] at e1 e2
  rw [h a, h (m : A), e2] at e1
  exact ((IsLocalization.map_units S m).map θ).smul_left_cancel.mp (add_left_cancel e1).symm

/-- A derivation of `A` with values in a module over a localization `S` of `A` extends to a
derivation of `S`. -/
theorem exists_addMonoidHom_of_isLocalization
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] (P : Submonoid A)
    [IsLocalization P S] {N : Type*} [AddCommGroup N] [Module S N]
    (D : A →+ N) (hD : ∀ a b : A, D (a * b) = algebraMap A S a • D b + algebraMap A S b • D a) :
    ∃ E : S →+ N, (∀ x y : S, E (x * y) = x • E y + y • E x) ∧
      ∀ a : A, E (algebraMap A S a) = D a := by
  let _ : Module Sᵐᵒᵖ N :=
    Module.compHom N
      ({ toFun := MulOpposite.unop, map_one' := rfl, map_mul' := fun _ _ => mul_comm _ _,
          map_zero' := rfl, map_add' := fun _ _ => rfl } : Sᵐᵒᵖ →+* S)
  let _ : IsCentralScalar S N := ⟨fun _ _ => rfl⟩
  have hD1 : D 1 = 0 := by simpa using hD 1 1
  let ψ : A →+* TrivSqZeroExt S N :=
    { toFun := fun a => (⟨algebraMap A S a, D a⟩ : TrivSqZeroExt S N)
      map_one' := Prod.ext (by rw [map_one]; rfl) hD1
      map_mul' := fun a b => Prod.ext (by rw [map_mul]; rfl) (hD a b)
      map_zero' := Prod.ext (by rw [map_zero]; rfl) (map_zero D)
      map_add' := fun a b => Prod.ext (by rw [map_add]; rfl) (map_add D a b) }
  have hψ : ∀ y : P, IsUnit (ψ (y : A)) := fun y =>
    isUnit_iff_isUnit_fst.mpr (IsLocalization.map_units S y)
  let L : S →+* TrivSqZeroExt S N := IsLocalization.lift (S := S) (M := P) (g := ψ) hψ
  let F : TrivSqZeroExt S N →+* S :=
    { toFun := TrivSqZeroExt.fst, map_one' := fst_one, map_mul' := fst_mul,
      map_zero' := fst_zero, map_add' := fst_add }
  have hfst : ∀ x : S, (L x).fst = x := by
    have h : F.comp L = RingHom.id S := by
      apply IsLocalization.ringHom_ext P
      ext a
      change (L (algebraMap A S a)).fst = _
      rw [IsLocalization.lift_eq]
      rfl
    exact RingHom.congr_fun h
  refine ⟨AddMonoidHom.mk' (fun x => (L x).snd)
      (fun x y => congrArg TrivSqZeroExt.snd (map_add L x y)), ?_, ?_⟩
  · intro x y
    have h := congrArg TrivSqZeroExt.snd (map_mul L x y)
    rw [snd_mul] at h
    change (L (x * y)).snd = _
    rw [h, hfst, hfst]
    rfl
  · intro a
    change (L (algebraMap A S a)).snd = _
    rw [IsLocalization.lift_eq]
    rfl

/-! ### Restriction maps -/

section Restrict

variable {X : Scheme.{u}}

/-- Restricting sections of the structure sheaf twice is restricting once. -/
theorem presheaf_restrict_restrict {W₁ W₂ W₃ : X.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (a : Γ(X, W₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op a) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Restricting sections of an `𝒪_X`-module twice is restricting once. -/
theorem module_restrict_restrict (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (h₁ : W₂ ≤ W₁)
    (h₂ : W₃ ≤ W₂) (a : Γ(M, W₁)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op a) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

end Restrict

/-! ### Locality over an affine open -/

section Locality

variable {X : Scheme.{u}} {M : X.Modules}

/-- The basic opens of an affine open `U` that are contained in an open `W ⊆ U` cover `W`. -/
theorem le_iSup_basicOpen {U W : X.Opens} (hU : IsAffineOpen U) (hW : W ≤ U) :
    W ≤ ⨆ i : {f : Γ(X, U) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro x hx
  obtain ⟨f, hf1, hf2⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hW hx)
  exact Opens.mem_iSup.mpr ⟨⟨f, hf1⟩, hf2⟩

/-- Sections of an `𝒪_X`-module over an open contained in an affine open are determined by their
restrictions to the basic opens contained in that open. -/
theorem eq_of_eq_on_basicOpens {U W : X.Opens} (hU : IsAffineOpen U) (hW : W ≤ U)
    (t t' : Γ(M, W))
    (h : ∀ (f : Γ(X, U)) (hf : X.basicOpen f ≤ W),
      M.presheaf.map (homOfLE hf).op t = M.presheaf.map (homOfLE hf).op t') :
    t = t' :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, U) // X.basicOpen f ≤ W} => X.basicOpen i.1) W (fun i => homOfLE i.2)
    (le_iSup_basicOpen hU hW) t t' (fun i => h i.1 i.2)

end Locality

/-! ### The correspondence -/

section Correspondence

variable {X : Scheme.{u}} {M : X.Modules}

/-- A Leibniz, restriction-compatible family of additive maps on the opens contained in an
affine open `U` is determined by its value on `U`. This is the uniqueness half of Stacks 01UO,
for an affine open of an arbitrary scheme and without a base-ring condition. -/
theorem eq_of_eq_on_affineOpen {U : X.Opens} (hU : IsAffineOpen U)
    (d d' : ∀ W : X.Opens, W ≤ U → (Γ(X, W) →+ Γ(M, W)))
    (hmul : ∀ (W : X.Opens) (hW : W ≤ U) (a b : Γ(X, W)),
      d W hW (a * b) = a • d W hW b + b • d W hW a)
    (hmul' : ∀ (W : X.Opens) (hW : W ≤ U) (a b : Γ(X, W)),
      d' W hW (a * b) = a • d' W hW b + b • d' W hW a)
    (hres : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)),
      d W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
        M.presheaf.map (homOfLE h).op (d W hW a))
    (hres' : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)),
      d' W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
        M.presheaf.map (homOfLE h).op (d' W hW a))
    (hU' : d U le_rfl = d' U le_rfl) :
    d = d' := by
  have hbasic : ∀ g : Γ(X, U),
      d (X.basicOpen g) (X.basicOpen_le g) = d' (X.basicOpen g) (X.basicOpen_le g) := by
    intro g
    have := hU.isLocalization_basicOpen g
    refine addMonoidHom_eq_of_isLocalization (Submonoid.powers g) (RingHom.id _) _ _
      (fun x y => hmul _ _ x y) (fun x y => hmul' _ _ x y) (fun a => ?_)
    change d (X.basicOpen g) (X.basicOpen_le g)
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) =
        d' (X.basicOpen g) (X.basicOpen_le g)
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a)
    rw [hres U _ le_rfl (X.basicOpen_le g), hres' U _ le_rfl (X.basicOpen_le g), hU']
  funext W hW
  ext s
  refine eq_of_eq_on_basicOpens hU hW _ _ (fun f hf => ?_)
  rw [← hres W _ hW hf, ← hres' W _ hW hf, hbasic f]

/-- Restricting a Leibniz identity for an additive map `Γ(X, V) →+ Γ(M, V)` to an open `W ≤ V`. -/
private theorem map_leibniz {V W : X.Opens} (h : W ≤ V) (d : Γ(X, V) →+ Γ(M, V))
    (hd : ∀ a b : Γ(X, V), d (a * b) = a • d b + b • d a) (a b : Γ(X, V)) :
    M.presheaf.map (homOfLE h).op (d (a * b)) =
      X.presheaf.map (homOfLE h).op a • M.presheaf.map (homOfLE h).op (d b) +
        X.presheaf.map (homOfLE h).op b • M.presheaf.map (homOfLE h).op (d a) := by
  rw [hd, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul]

/-- A Leibniz additive map on an affine open extends to a basic open. -/
theorem exists_extension_basicOpen {U : X.Opens} (hU : IsAffineOpen U)
    (D : Γ(X, U) →+ Γ(M, U))
    (hD : ∀ a b : Γ(X, U), D (a * b) = a • D b + b • D a) (g : Γ(X, U)) :
    ∃ E : Γ(X, X.basicOpen g) →+ Γ(M, X.basicOpen g),
      (∀ x y : Γ(X, X.basicOpen g), E (x * y) = x • E y + y • E x) ∧
      ∀ a : Γ(X, U), E (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) =
        M.presheaf.map (homOfLE (X.basicOpen_le g)).op (D a) := by
  have := hU.isLocalization_basicOpen g
  exact exists_addMonoidHom_of_isLocalization (Submonoid.powers g)
    (AddMonoidHom.mk' (fun a => M.presheaf.map (homOfLE (X.basicOpen_le g)).op (D a))
      (fun a b => by simp))
    (map_leibniz (X.basicOpen_le g) D hD)

section Family

variable {U : X.Opens} (hU : IsAffineOpen U) (D : Γ(X, U) →+ Γ(M, U))
  (E : ∀ g : Γ(X, U), Γ(X, X.basicOpen g) →+ Γ(M, X.basicOpen g))
  (hE1 : ∀ (g : Γ(X, U)) (x y : Γ(X, X.basicOpen g)), E g (x * y) = x • E g y + y • E g x)
  (hE2 : ∀ (g : Γ(X, U)) (a : Γ(X, U)),
    E g (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) =
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op (D a))

include hU hE1 hE2

/-- A family of extensions to the basic opens of an affine open is compatible with the
restriction maps between the basic opens. -/
theorem restrict_extension_basicOpen (g h : Γ(X, U)) (hle : X.basicOpen h ≤ X.basicOpen g)
    (x : Γ(X, X.basicOpen g)) :
    M.presheaf.map (homOfLE hle).op (E g x) = E h (X.presheaf.map (homOfLE hle).op x) := by
  have := hU.isLocalization_basicOpen g
  have key := addMonoidHom_eq_of_isLocalization (A := Γ(X, U)) (Submonoid.powers g)
    (X.presheaf.map (homOfLE hle).op).hom
    (AddMonoidHom.mk' (fun z => M.presheaf.map (homOfLE hle).op (E g z)) (fun z w => by simp))
    ((E h).comp (X.presheaf.map (homOfLE hle).op).hom.toAddMonoidHom)
    (fun z w => by
      exact map_leibniz hle (E g) (hE1 g) z w)
    (fun z w => by
      change E h (X.presheaf.map (homOfLE hle).op (z * w)) = _
      rw [map_mul, hE1 h]
      rfl)
    (fun a => by
      change M.presheaf.map (homOfLE hle).op
          (E g (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a)) =
        E h (X.presheaf.map (homOfLE hle).op
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a))
      rw [hE2 g a, module_restrict_restrict, presheaf_restrict_restrict, hE2 h a])
  exact DFunLike.congr_fun key x

/-- Two members of a family of extensions to the basic opens of an affine open agree on any
common open on which the sections they are applied to agree. -/
theorem restrict_extension_eq {V : X.Opens} (hVU : V ≤ U) (g h : Γ(X, U))
    (hVg : V ≤ X.basicOpen g) (hVh : V ≤ X.basicOpen h)
    (x : Γ(X, X.basicOpen g)) (y : Γ(X, X.basicOpen h))
    (hxy : X.presheaf.map (homOfLE hVg).op x = X.presheaf.map (homOfLE hVh).op y) :
    M.presheaf.map (homOfLE hVg).op (E g x) = M.presheaf.map (homOfLE hVh).op (E h y) := by
  refine eq_of_eq_on_basicOpens hU hVU _ _ (fun f hf => ?_)
  have hres : X.presheaf.map (homOfLE (hf.trans hVg)).op x =
      X.presheaf.map (homOfLE (hf.trans hVh)).op y := by
    rw [← presheaf_restrict_restrict hVg hf, ← presheaf_restrict_restrict hVh hf, hxy]
  rw [module_restrict_restrict, module_restrict_restrict,
    restrict_extension_basicOpen hU D E hE1 hE2 g f (hf.trans hVg) x,
    restrict_extension_basicOpen hU D E hE1 hE2 h f (hf.trans hVh) y, hres]

/-- The values of a family of extensions to the basic opens glue to a section over any open
contained in the affine open. -/
theorem exists_gluing {W : X.Opens} (hW : W ≤ U) (s : Γ(X, W)) :
    ∃ t : Γ(M, W), ∀ (f : Γ(X, U)) (hf : X.basicOpen f ≤ W),
      M.presheaf.map (homOfLE hf).op t = E f (X.presheaf.map (homOfLE hf).op s) := by
  have hcompat : TopCat.Presheaf.IsCompatible
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X).obj
      (fun i : {f : Γ(X, U) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      (fun i => E i.1 (X.presheaf.map (homOfLE i.2).op s)) := by
    intro i j
    have hxy : X.presheaf.map (homOfLE (inf_le_left :
          X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen i.1)).op
            (X.presheaf.map (homOfLE i.2).op s) =
        X.presheaf.map (homOfLE (inf_le_right :
          X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen j.1)).op
            (X.presheaf.map (homOfLE j.2).op s) := by
      rw [presheaf_restrict_restrict, presheaf_restrict_restrict]
    exact restrict_extension_eq hU D E hE1 hE2
      (le_trans (inf_le_left.trans i.2) hW) i.1 j.1 inf_le_left inf_le_right _ _ hxy
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, U) // X.basicOpen f ≤ W} => X.basicOpen i.1) W (fun i => homOfLE i.2)
    (le_iSup_basicOpen hU hW) _ hcompat
  exact ⟨t, fun f hf => ht ⟨f, hf⟩⟩

end Family

/-- A Leibniz additive map on an affine open `U` is the value on `U` of a Leibniz,
restriction-compatible family of additive maps on the opens contained in `U`. This is the
existence half of Stacks 01UO, for an affine open of an arbitrary scheme and without a
base-ring condition. -/
theorem exists_restrictions {U : X.Opens} (hU : IsAffineOpen U)
    (D : Γ(X, U) →+ Γ(M, U))
    (hD : ∀ a b : Γ(X, U), D (a * b) = a • D b + b • D a) :
    ∃ d : ∀ W : X.Opens, W ≤ U → (Γ(X, W) →+ Γ(M, W)),
      (∀ (W : X.Opens) (hW : W ≤ U) (a b : Γ(X, W)),
          d W hW (a * b) = a • d W hW b + b • d W hW a) ∧
        (∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)),
            d W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
              M.presheaf.map (homOfLE h).op (d W hW a)) ∧
          d U le_rfl = D := by
  choose E hE1 hE2 using exists_extension_basicOpen hU D hD
  choose T hT using fun (W : X.Opens) (hW : W ≤ U) (s : Γ(X, W)) =>
    exists_gluing hU D E hE1 hE2 hW s
  have hadd : ∀ (W : X.Opens) (hW : W ≤ U) (s s' : Γ(X, W)),
      T W hW (s + s') = T W hW s + T W hW s' := fun W hW s s' =>
    eq_of_eq_on_basicOpens hU hW _ _ fun f hf => by simp only [hT, map_add]
  have hleib : ∀ (W : X.Opens) (hW : W ≤ U) (s s' : Γ(X, W)),
      T W hW (s * s') = s • T W hW s' + s' • T W hW s := fun W hW s s' =>
    eq_of_eq_on_basicOpens hU hW _ _ fun f hf => by
      simp only [hT, map_mul, hE1, map_add, Scheme.Modules.map_smul]
  have hrc : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (s : Γ(X, W)),
      T W' (h.trans hW) (X.presheaf.map (homOfLE h).op s) =
        M.presheaf.map (homOfLE h).op (T W hW s) := fun W W' hW h s =>
    eq_of_eq_on_basicOpens hU (h.trans hW) _ _ fun f hf => by
      simp only [hT, presheaf_restrict_restrict, module_restrict_restrict]
  refine ⟨fun W hW => AddMonoidHom.mk' (T W hW) (hadd W hW), hleib, hrc, ?_⟩
  ext s
  refine eq_of_eq_on_basicOpens hU le_rfl _ _ (fun f hf => ?_)
  change M.presheaf.map (homOfLE hf).op (T U le_rfl s) = _
  exact (hT U le_rfl s f hf).trans (hE2 f s)

/-- **Stacks 01UO, affine-open form.** On the opens contained in an affine open `U` of a scheme
`X`, a Leibniz, restriction-compatible family of additive maps into an `𝒪_X`-module `M` is the
same thing as a single Leibniz additive map `Γ(X, U) → Γ(M, U)`. -/
theorem existsUnique_restrictions {U : X.Opens} (hU : IsAffineOpen U)
    (D : Γ(X, U) →+ Γ(M, U))
    (hD : ∀ a b : Γ(X, U), D (a * b) = a • D b + b • D a) :
    ∃! d : ∀ W : X.Opens, W ≤ U → (Γ(X, W) →+ Γ(M, W)),
      (∀ (W : X.Opens) (hW : W ≤ U) (a b : Γ(X, W)),
          d W hW (a * b) = a • d W hW b + b • d W hW a) ∧
        (∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)),
            d W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
              M.presheaf.map (homOfLE h).op (d W hW a)) ∧
          d U le_rfl = D := by
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_restrictions hU D hD
  exact ⟨d, ⟨hd1, hd2, hd3⟩, fun d' ⟨hd'1, hd'2, hd'3⟩ =>
    eq_of_eq_on_affineOpen hU d' d hd'1 hd1 hd'2 hd2 (hd'3.trans hd3.symm)⟩

/-- The family of maps produced on the opens contained in an affine open annihilates the
restriction of every section annihilated by the given map on the affine open. In particular a
family that is a derivation relative to a base ring corresponds to a ring derivation relative
to that base ring. -/
theorem restrictions_apply_eq_zero {U : X.Opens}
    (d : ∀ W : X.Opens, W ≤ U → (Γ(X, W) →+ Γ(M, W)))
    (hres : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)),
      d W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
        M.presheaf.map (homOfLE h).op (d W hW a))
    {W : X.Opens} (hW : W ≤ U) {a : Γ(X, U)} (ha : d U le_rfl a = 0) :
    d W hW (X.presheaf.map (homOfLE hW).op a) = 0 := by
  rw [hres U W le_rfl hW a, ha, map_zero]

end Correspondence

end Stacks.AlgebraicGeometry.DifferentialsAffine

end
