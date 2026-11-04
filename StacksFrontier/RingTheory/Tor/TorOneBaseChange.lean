module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for `Tor₁` via an explicit presentation
-/

/-!
# Base change for `Tor₁`

Let `R → R' → R''` be a chain of commutative unital ring homomorphisms, so that `R'` is an
`R`-algebra and `R''` is both an `R'`-algebra and, by composition, an `R`-algebra. Let `M` be
an `R`-module.

For an `R`-module `N`, `Tor₁ᴿ(M, N)` is the first left-derived functor of `M ⊗ᴿ (-)`,
equivalently of `(-) ⊗ᴿ N`, computed as `H₁(F• ⊗ᴿ N)` for a projective resolution
`F• → M` over `R`. Since `R''` is an `R'`-algebra and `Tor₁ᴿ(M, R')` is an `R'`-module,
there is a natural base-change ("change of rings") homomorphism

  `Φ : Tor₁ᴿ(M, R') ⊗_{R'} R'' → Tor₁ᴿ(M, R'')`

induced by the canonical isomorphism `(Fᵢ ⊗ᴿ R') ⊗_{R'} R'' ≅ Fᵢ ⊗ᴿ R''` together with the
comparison map on the homology of the base-changed complex. The main theorem is that if the
`R'`-module `M ⊗ᴿ R'` is flat over `R'`, then `Φ` is surjective.

## Formalization notes

Two things must be pinned down: the object called `Tor₁ᴿ(M, S)` has to be the derived functor
carrying its genuine `S`-module structure, so that the tensor product `⊗_{R'} R''` in the
source of `Φ` means what it should; and `Φ` has to be the *natural* base-change map rather
than an arbitrary one. Accordingly the base-change map is given both an abstract categorical
home and an explicit description via `cancelBaseChange`.

* For a ring map `R → S`, base change is the functor
  `extendScalars (R → S) = S ⊗ᴿ (-) : ModuleCat R ⥤ ModuleCat S`, and
  `catTor S M := ((extendScalars (algebraMap R S)).leftDerived 1).obj M` is `Tor₁ᴿ(M, S)`
  by definition. It lives in `ModuleCat S`, hence carries the correct `S`-module structure.
* Writing `G = extendScalars (R' → R'') = R'' ⊗_{R'} (-)`, the object `G.obj (catTor R' M)`
  is the source of `Φ` and `catTor R'' M` its target, so the natural base-change map is a
  morphism `bc : G.obj (catTor R' M) ⟶ catTor R'' M` of `ModuleCat R''`, i.e. an
  `R''`-linear map `R'' ⊗_{R'} Tor₁ᴿ(M, R') → Tor₁ᴿ(M, R'')`.
* Concretely, fixing a projective resolution `P` of `M` over `R` with differentials
  `dₙ = P.complex.d n (n-1)`, the first homology of the base-changed complex is the
  `S`-module `Tor1 S := ker(d₁ ⊗ S) / im(d₂ ⊗ S)`, a subquotient of `S ⊗ᴿ F₁`. The explicit
  map `phi : R'' ⊗_{R'} Tor1 R' → Tor1 R''` is built from the canonical comparison
  isomorphism `cancelBaseChange : R'' ⊗_{R'} (R' ⊗ᴿ Fᵢ) ≅ R'' ⊗ᴿ Fᵢ` and is `R''`-linear.
* `Tor1_iso_catTor` gives `Nonempty (Tor1 S ≃ₗ[S] catTor S M)`, so the concrete model is
  abstractly the derived functor with its `S`-module structure, but no *specific*
  identification is fixed; and `phi_apply_mk` describes `phi` on generators as the map
  induced by `cancelBaseChange`.
* `exists_baseChange_eq_phi` is a formal transport square only: its `bc` is built from
  `phi` across the extend/restrict adjunction, and `e'`, `e''` are arbitrary. It does
  **not** certify that `phi` is the canonical derived base-change map, and 00MM is
  proved here for the resolution model `H₁(P ⊗ᴿ -)`.

All rings are commutative with unit. The flatness hypothesis is written
`Module.Flat R' (R' ⊗[R] M)`, using the standard Mathlib orientation with `R'` on the left.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Stacks.TorOneBaseChange

universe u

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
  {R'' : Type u} [CommRing R''] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']

/-- The base-change functor `extendScalars (R → S) = S ⊗ᴿ (-)` is additive. -/
noncomputable instance extendScalars_additive {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u, u, u} f).Additive := by
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (ModuleCat.extendScalars.{u, u, u} f) := inferInstance
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} f)

/-! ## The derived functor `Tor₁ᴿ(M, S)` as an `S`-module -/

/-- `Tor₁ᴿ(M, S)` as the genuine first left-derived functor of base change
`extendScalars (R → S) = S ⊗ᴿ (-)`, evaluated at `M`.  This lives in `ModuleCat S`,
so it carries the correct `S`-module structure. -/
noncomputable def catTor (S : Type u) [CommRing S] [Algebra R S] (M : ModuleCat.{u} R) :
    ModuleCat.{u} S :=
  ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).leftDerived 1).obj M

variable {F2 F1 F0 : Type u} [AddCommGroup F2] [Module R F2] [AddCommGroup F1] [Module R F1]
  [AddCommGroup F0] [Module R F0]

/-- The cycles `ker(d₁ ⊗ S)` of the base-changed complex, as an `S`-submodule of
`S ⊗ᴿ F₁`. -/
noncomputable abbrev cycles (S : Type u) [CommRing S] [Algebra R S]
    (d1 : F1 →ₗ[R] F0) : Submodule S (S ⊗[R] F1) :=
  (LinearMap.baseChange S d1).ker

/-- The boundaries `im(d₂ ⊗ S)` of the base-changed complex, as an `S`-submodule of
`S ⊗ᴿ F₁`. -/
noncomputable abbrev boundaries (S : Type u) [CommRing S] [Algebra R S]
    (d2 : F2 →ₗ[R] F1) : Submodule S (S ⊗[R] F1) :=
  (LinearMap.baseChange S d2).range

/-- `Tor₁ˢ(M, S) = ker(d₁ ⊗ S) / im(d₂ ⊗ S)`, the first homology of the base-changed
complex, as an `S`-module.  Here `d₂, d₁` are the relevant differentials of a chosen
free/projective resolution of `M` over `R`. -/
noncomputable abbrev Tor1 (S : Type u) [CommRing S] [Algebra R S]
    (d2 : F2 →ₗ[R] F1) (d1 : F1 →ₗ[R] F0) : Type u :=
  (cycles S d1) ⧸ ((boundaries S d2).comap (cycles S d1).subtype)

/-- The canonical comparison map `R'' ⊗_{R'} (R' ⊗ᴿ F i) → R'' ⊗ᴿ F i`, an `R''`-linear
isomorphism (we keep only the underlying linear map). -/
noncomputable def cmpMap (Fi : Type u) [AddCommGroup Fi] [Module R Fi] :
    (R'' ⊗[R'] (R' ⊗[R] Fi)) →ₗ[R''] (R'' ⊗[R] Fi) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R'' R'' Fi).toLinearMap

/-- Naturality of the comparison map with respect to a differential `d`. -/
theorem cmpMap_natural (d : F1 →ₗ[R] F0) :
    (LinearMap.baseChange R'' d).comp (cmpMap (R := R) (R' := R') (R'' := R'') F1)
      = (cmpMap (R := R) (R' := R') (R'' := R'') F0).comp
          (LinearMap.baseChange R'' (LinearMap.baseChange R' d)) := by
  ext x
  simp [cmpMap]

/-- The bilinear map `R'' × (R' ⊗ᴿ F₁) → R'' ⊗ᴿ F₁`, `(r'', x) ↦ cmp (r'' ⊗ x)`, which is
`R''`-linear in `r''` and `R'`-linear in `x`. -/
noncomputable def cmpBil :
    R'' →ₗ[R''] (R' ⊗[R] F1) →ₗ[R'] (R'' ⊗[R] F1) where
  toFun r'' :=
    { toFun := fun x => (cmpMap (R := R) (R' := R') (R'' := R'') F1) (r'' ⊗ₜ[R'] x)
      map_add' := fun x y => by simp [TensorProduct.tmul_add]
      map_smul' := fun c x => by simp [TensorProduct.tmul_smul] }
  map_add' := fun r s => by
    ext x
    simp [TensorProduct.add_tmul]
  map_smul' := by
    intro c r
    refine LinearMap.ext fun x => ?_
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show (c • r) ⊗ₜ[R'] x = c • (r ⊗ₜ[R'] x) from by rw [TensorProduct.smul_tmul'],
      map_smul]

/-- Naturality of `cmpBil` with respect to a differential `d`. -/
private theorem baseChange_cmpBil (d : F1 →ₗ[R] F0) (r'' : R'') (x : R' ⊗[R] F1) :
    LinearMap.baseChange R'' d (cmpBil (R := R) (R' := R') (R'' := R'') r'' x)
      = cmpBil (R := R) (R' := R') (R'' := R'') r'' (LinearMap.baseChange R' d x) := by
  have := LinearMap.congr_fun (cmpMap_natural (R := R) (R' := R') (R'' := R'') d) (r'' ⊗ₜ[R'] x)
  simpa [cmpBil] using this

/-- For a cycle `k ∈ ker(d₁ ⊗ R')` and `r'' : R''`, the element `cmp (r'' ⊗ k)` is a
cycle of the `R''`-base-changed complex. -/
theorem cmpBil_mem_cycles (d1 : F1 →ₗ[R] F0)
    (k : R' ⊗[R] F1) (hk : k ∈ cycles R' d1) (r'' : R'') :
    cmpBil (R := R) (R' := R') (R'' := R'') r'' k ∈ cycles R'' d1 := by
  rw [cycles, LinearMap.mem_ker, baseChange_cmpBil, LinearMap.mem_ker.mp hk, map_zero]

/-- For a boundary `b ∈ im(d₂ ⊗ R')` and `r'' : R''`, the element `cmp (r'' ⊗ b)` is a
boundary of the `R''`-base-changed complex. -/
theorem cmpBil_mem_boundaries (d2 : F2 →ₗ[R] F1)
    (b : R' ⊗[R] F1) (hb : b ∈ boundaries R' d2) (r'' : R'') :
    cmpBil (R := R) (R' := R') (R'' := R'') r'' b ∈ boundaries R'' d2 := by
  obtain ⟨y, rfl⟩ := hb
  exact ⟨_, baseChange_cmpBil d2 r'' y⟩

/-- The map `R'' → ker(d₁ ⊗ R') →ₗ ker(d₁ ⊗ R'')` underlying `Φ`, valued in cycles;
`R''`-linear in the `R''`-argument, `R'`-linear in the cycle. -/
noncomputable def cyclesMap (d1 : F1 →ₗ[R] F0) :
    R'' →ₗ[R''] (cycles R' d1) →ₗ[R'] (cycles R'' d1) where
  toFun r'' :=
    { toFun := fun k => ⟨cmpBil (R := R) (R' := R') (R'' := R'') r'' k.val,
        cmpBil_mem_cycles d1 k.val k.property r''⟩
      map_add' := by intro k l; ext; simp
      map_smul' := by intro c k; ext; simp }
  map_add' := by intro r s; ext k; simp
  map_smul' := by
    intro c r
    refine LinearMap.ext fun k => ?_
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      SetLike.mk_smul_mk, Subtype.ext_iff]
    rw [map_smul]
    rfl

/-- The `R''`-linear, `R'`-bilinear map `R'' × Tor₁ᴿ(M, R') → Tor₁ᴿ(M, R'')` underlying
the base-change map `Φ`. -/
noncomputable def phiBil (d2 : F2 →ₗ[R] F1) (d1 : F1 →ₗ[R] F0) :
    R'' →ₗ[R''] (Tor1 R' d2 d1) →ₗ[R'] (Tor1 R'' d2 d1) where
  toFun r'' :=
    Submodule.liftQ _
      (LinearMap.comp
        (((boundaries R'' d2).comap (cycles R'' d1).subtype).mkQ.restrictScalars R')
        (cyclesMap (R := R) (R' := R') (R'' := R'') d1 r'')) <| by
      intro x hx
      rw [Submodule.mem_comap] at hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact cmpBil_mem_boundaries d2 x.val hx r''
  map_add' := by
    intro r s
    refine Submodule.linearMap_qext _ ?_
    ext k
    simp only [Submodule.liftQ_mkQ, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, map_add]
    rfl
  map_smul' := by
    intro c r
    refine Submodule.linearMap_qext _ ?_
    ext k
    simp only [Submodule.liftQ_mkQ, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, map_smul, RingHom.id_apply]
    rfl

/-- The base-change (change of rings) homomorphism, in the standard Mathlib orientation
`R'' ⊗_{R'} Tor₁ᴿ(M, R')` (canonically `R''`-isomorphic to `Tor₁ᴿ(M, R') ⊗_{R'} R''`):

  `Φ : R'' ⊗_{R'} Tor₁ᴿ(M, R') → Tor₁ᴿ(M, R'')`.

It is genuinely `R''`-linear. -/
noncomputable def phi (d2 : F2 →ₗ[R] F1) (d1 : F1 →ₗ[R] F0) :
    (R'' ⊗[R'] (Tor1 R' d2 d1)) →ₗ[R''] (Tor1 R'' d2 d1) :=
  TensorProduct.AlgebraTensorModule.lift (phiBil (R := R) (R' := R') (R'' := R'') d2 d1)

/-- **Correctness of `Φ` (explicit characterization on generators).**

`Φ` is exactly the natural base-change map induced by `cancelBaseChange`: on a
generator `r'' ⊗ ⟦k⟧` (with `k` a cycle of the `R'`-base-changed complex), it is the
class of `cmp (r'' ⊗ k)`, where `cmp = cancelBaseChange` is the canonical isomorphism
`R'' ⊗_{R'} (R' ⊗ᴿ F₁) ≅ R'' ⊗ᴿ F₁`.  This pins `Φ` down uniquely
as the map induced by that canonical comparison on homology. -/
theorem phi_apply_mk (d2 : F2 →ₗ[R] F1) (d1 : F1 →ₗ[R] F0)
    (r'' : R'') (k : cycles R' d1) :
    phi (R := R) (R' := R') (R'' := R'') d2 d1
        (r'' ⊗ₜ[R'] (Submodule.Quotient.mk k))
      = Submodule.Quotient.mk
          (⟨cmpBil (R := R) (R' := R') (R'' := R'') r'' k.1,
            cmpBil_mem_cycles d1 k.1 k.2 r''⟩ : cycles R'' d1) :=
  rfl

/-- The `R`-linear identity between the ambient `R`-module structure on `S` (via
`Algebra R S`) and the one used by `ModuleCat.extendScalars (algebraMap R S)` (via
`restrictScalars`).  These structures agree propositionally (`Algebra.smul_def`) but are
distinct instances, so we record the transport explicitly. -/
noncomputable def restrictScalarsSelfEquiv (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    (S) ≃ₗ[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) : Type u) where
  toFun := id; invFun := id; left_inv := fun _ => rfl; right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by intro r s; change (r • s : S) = _; rw [Algebra.smul_def]; rfl

/-- The induced `R`-linear transport on tensor products. -/
noncomputable def tensorRestrictScalarsEquiv (S : Type u) [CommRing S] [Algebra R S]
    (A : ModuleCat.{u} R) :
    (S ⊗[R] (A : Type u)) ≃ₗ[R]
      (((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) : Type u) ⊗[R] (A :
          Type u)) :=
  TensorProduct.congr (restrictScalarsSelfEquiv R S) (LinearEquiv.refl R (A : Type u))

-- needed: the structure fields of `tensorEquivExtendScalars` are only definitionally the
-- required maps once `restrictScalars`/`extendScalars` are unfolded past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- The `S`-linear transport `S ⊗[R] A ≃ₗ[S] (extendScalars (algebraMap R S)).obj A`,
identifying the ambient base change with the genuine functorial one. -/
noncomputable def tensorEquivExtendScalars (S : Type u) [CommRing S] [Algebra R S]
    (A : ModuleCat.{u} R) :
    (S ⊗[R] (A : Type u)) ≃ₗ[S] ((ModuleCat.extendScalars (algebraMap R S)).obj A : Type u) where
  toFun := tensorRestrictScalarsEquiv S A; invFun := (tensorRestrictScalarsEquiv S A).symm
  left_inv := (tensorRestrictScalarsEquiv S A).left_inv
  right_inv := (tensorRestrictScalarsEquiv S A).right_inv
  map_add' := (tensorRestrictScalarsEquiv S A).map_add'
  map_smul' := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
        rw [TensorProduct.smul_tmul']
        change tensorRestrictScalarsEquiv S A ((c * s) ⊗ₜ[R] a)
          = c • tensorRestrictScalarsEquiv S A (s ⊗ₜ[R] a)
        simp only [tensorRestrictScalarsEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
          restrictScalarsSelfEquiv, LinearEquiv.coe_mk]
        rw [TensorProduct.smul_tmul']; rfl
    | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, smul_add]

/-- Naturality of the transport with respect to a differential. -/
theorem tensorEquivExtendScalars_natural (S : Type u) [CommRing S] [Algebra R S]
    {A1 A0 : ModuleCat.{u} R} (h : A1 ⟶ A0) :
    (tensorEquivExtendScalars S A0).toLinearMap.comp (LinearMap.baseChange S h.hom)
      = (((ModuleCat.extendScalars (algebraMap R S)).map h).hom).comp (tensorEquivExtendScalars S
          A1).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
      show tensorRestrictScalarsEquiv S A0 (s ⊗ₜ[R] h.hom a)
        = ((ModuleCat.extendScalars (algebraMap R S)).map h).hom
            (tensorRestrictScalarsEquiv S A1 (s ⊗ₜ[R] a))
      simp only [tensorRestrictScalarsEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        restrictScalarsSelfEquiv]
      rfl
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]

/-- The concrete short complex `(S ⊗ F₂) → (S ⊗ F₁) → (S ⊗ F₀)` whose homology is `Tor1 S`. -/
noncomputable def baseChangeShortComplex (S : Type u) [CommRing S] [Algebra R S]
    {G2 G1 G0 : Type u} [AddCommGroup G2] [Module R G2] [AddCommGroup G1] [Module R G1]
    [AddCommGroup G0] [Module R G0]
    (d2 : G2 →ₗ[R] G1) (d1 : G1 →ₗ[R] G0) (hzero : d1.comp d2 = 0) :
    ShortComplex (ModuleCat S) where
  X₁ := ModuleCat.of S (S ⊗[R] G2)
  X₂ := ModuleCat.of S (S ⊗[R] G1)
  X₃ := ModuleCat.of S (S ⊗[R] G0)
  f := ModuleCat.ofHom (LinearMap.baseChange S d2)
  g := ModuleCat.ofHom (LinearMap.baseChange S d1)
  zero := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
      ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero]

/-- **Correctness of `Tor1` (`S`-linear identification with the derived functor).**

The concrete first homology `Tor1 S` of the base-changed projective resolution agrees,
**`S`-linearly**, with Mathlib's genuine first `Tor` group `Tor₁ᴿ(M, S) = catTor S M`,
computed as the first left-derived functor of base change `extendScalars (R → S)`.
This certifies that `Tor1 S` is the actual derived functor *together with its correct
`S`-module structure* (the equivalence is `S`-linear, not merely `R`-linear). -/
theorem Tor1_iso_catTor
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (S : Type u) [CommRing S] [Algebra R S] :
    Nonempty
      (Tor1 S (P.complex.d 2 1).hom (P.complex.d 1 0).hom
        ≃ₗ[S] catTor S M) := by
  -- `catTor S M` is the degree-1 homology of the base-changed complex `S ⊗ᴿ F•`,
  -- which we identify `S`-linearly with the concrete model `Tor1 S` by comparing the
  -- ambient base change with the functorial one (`tensorEquivExtendScalars`) on the short
  -- complex at 1.
  have hzero : (P.complex.d 1 0).hom.comp (P.complex.d 2 1).hom = 0 := by
    rw [← ModuleCat.hom_comp, P.complex.d_comp_d 2 1 0, ModuleCat.hom_zero]
  set F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  set C : HomologicalComplex (ModuleCat S) (ComplexShape.down ℕ) :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  set SC := baseChangeShortComplex S (P.complex.d 2 1).hom (P.complex.d 1 0).hom hzero
  have ph : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 2 1 by simp)
  have nh : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 by simp)
  -- the short complex isomorphism `SC ≅ C.sc' 2 1 0`
  let e1 : SC.X₁ ≅ (C.sc' 2 1 0).X₁ := (tensorEquivExtendScalars S (P.complex.X 2)).toModuleIso
  let e2 : SC.X₂ ≅ (C.sc' 2 1 0).X₂ := (tensorEquivExtendScalars S (P.complex.X 1)).toModuleIso
  let e3 : SC.X₃ ≅ (C.sc' 2 1 0).X₃ := (tensorEquivExtendScalars S (P.complex.X 0)).toModuleIso
  have scIso : SC ≅ C.sc' 2 1 0 := by
    refine ShortComplex.isoMk e1 e2 e3 ?_ ?_ <;> apply ModuleCat.hom_ext <;>
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    exacts [(tensorEquivExtendScalars_natural S (P.complex.d 2 1)).symm,
      (tensorEquivExtendScalars_natural S (P.complex.d 1 0)).symm]
  -- bottom equivalence: `Tor1 S ≃ₗ[S] SC.moduleCatLeftHomologyData.H`
  have hsub : ((boundaries S (P.complex.d 2 1).hom).comap (cycles S (P.complex.d 1 0).hom).subtype)
      = (SC.moduleCatToCycles.range) := by
    ext x
    simp only [ShortComplex.moduleCatToCycles, LinearMap.mem_range, Submodule.mem_comap]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ => ⟨y, hy ▸ rfl⟩⟩
  let eBot : (Tor1 S (P.complex.d 2 1).hom (P.complex.d 1 0).hom) ≃ₗ[S]
      (SC.moduleCatLeftHomologyData.H : Type u) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl S _) ((Submodule.map_id _).trans hsub)
  -- chain of `ModuleCat S` isomorphisms up to the genuine derived functor
  let i1 : (SC.moduleCatLeftHomologyData.H) ≅ SC.homology := SC.moduleCatHomologyIso.symm
  let i2 : SC.homology ≅ (C.sc' 2 1 0).homology := ShortComplex.homologyMapIso scIso
  let i3 : (C.sc' 2 1 0).homology ≅ (C.sc 1).homology :=
    ShortComplex.homologyMapIso (C.isoSc' 2 1 0 ph nh).symm
  let i4 := (P.isoLeftDerivedObj F 1).symm
  exact ⟨eBot.trans (((i1.trans i2).trans (i3.trans i4)).toLinearEquiv)⟩

-- needed: `exists_baseChange_eq_phi` compares homology maps through `Tor1_iso_catTor`,
-- whose rewrites require defeq to unfold the derived-functor identifications past the default
-- transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Compatibility of the genuine categorical base-change map with `Φ`.**

Let `e' : Tor1 R' ≃ₗ[R'] catTor R' M` and `e'' : Tor1 R'' ≃ₗ[R''] catTor R'' M` be the
`S`-linear identifications of `Tor1_iso_catTor` (for `S = R'` and `S = R''`).  Writing
`G = extendScalars (R' → R'') = R'' ⊗_{R'} (-)`, the genuine base-change map is a
morphism in `ModuleCat R''`

  `bc : G.obj (catTor R' M) ⟶ catTor R'' M`,

i.e. an `R''`-linear map `R'' ⊗_{R'} Tor₁ᴿ(M, R') → Tor₁ᴿ(M, R'')` between the genuine
derived `Tor` modules.  This correctness statement asserts that there is a
`bc` whose value, transported across the identifications `e'`, `e''` (using `G.map e'`
on the source — i.e. `R'' ⊗_{R'} e'`), equals the explicit map `Φ`.

**Caveat: this does not pin `Φ` down.** `bc` is existentially quantified and is
*constructed from* `Φ` itself, by currying `y ↦ e'' (Φ (1 ⊗ e'.symm y))` across the
`extendRestrictScalarsAdj` adjunction. The same proof goes through verbatim with `Φ`
replaced by any `R''`-linear map out of `R'' ⊗_{R'} -`, and `e'`, `e''` are arbitrary
linear equivalences rather than canonical identifications (`Tor1_iso_catTor` only
provides `Nonempty`). So this statement carries no information about `Φ` being *the*
natural base-change map; it is a formal transport lemma. Establishing the genuine
identification would require a canonically defined comparison (for instance via
`NatTrans.leftDerived` together with the extend/restrict adjunction) and a proof that
`Φ` agrees with *that* map. -/
theorem exists_baseChange_eq_phi
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (e' : Tor1 R' (P.complex.d 2 1).hom (P.complex.d 1 0).hom ≃ₗ[R'] catTor R' M)
    (e'' : Tor1 R'' (P.complex.d 2 1).hom (P.complex.d 1 0).hom ≃ₗ[R''] catTor R'' M) :
    ∃ bc : (ModuleCat.extendScalars.{u, u, u} (algebraMap R' R'')).obj (catTor R' M)
        ⟶ catTor R'' M,
      ∀ (r'' : R'') (t : Tor1 R' (P.complex.d 2 1).hom (P.complex.d 1 0).hom),
        bc.hom (r'' ⊗ₜ[R'] (e' t))
          = e'' (phi (R := R) (R' := R') (R'' := R'')
              (P.complex.d 2 1).hom (P.complex.d 1 0).hom (r'' ⊗ₜ[R'] t)) := by
  -- Construction of `bc` and of the compatibility square.  The map `bc` is the image,
  -- under the extend/restrict-scalars adjunction
  -- `ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')`, of the R'-linear map
  -- `φ : catTor R' M → (restrictScalars (algebraMap R' R'')).obj (catTor R'' M)` defined
  -- by `φ y = e'' (phi (1 ⊗ e'.symm y))`.  This is the standard "currying" of the
  -- desired R''-linear map across the adjunction `(R'' ⊗_{R'} -) ⊣ restrictScalars`.
  --   • φ.map_add' : `simp [map_add, TensorProduct.tmul_add]`.
  --   • φ.map_smul' (R'-linearity, the delicate step): for `c : R'`,
  --       `e'.symm (c • y) = c • e'.symm y`, and
  --       `c • (1 ⊗ x) = (algebraMap R' R'' c) • (1 ⊗ x)` (via `TensorProduct.smul_tmul'`,
  --       `Algebra.smul_def`, `mul_one`), then `map_smul` of `phi` and `e''`.
  --     (Note: the codomain is `(restrictScalars _).obj _`; obtain the `Module R'`
  --     instance on it via `ModuleCat.restrictScalars` / `RestrictScalars` API, or build
  --     `φ` as a `ModuleCat.ofHom` of a `LinearMap` over the restricted scalars — i.e.
  --     state `φ` directly with the right `Module R' ((restrictScalars _).obj _)`
  --     instance in scope, which is `RestrictScalars.module R' R'' _` /
  --     `Module.compHom`.)
  -- Then set `bc := ((extendRestrictScalarsAdj (algebraMap R' R'')).homEquiv _ _).symm
  --   (ModuleCat.ofHom φ)` and verify the square: after
  --   `rw [Adjunction.homEquiv_symm_apply, ModuleCat.hom_comp, LinearMap.comp_apply]`,
  --   the goal unfolds the adjunction counit on `extendScalars`; reduce
  --   `(extendScalars _).map (ofHom φ)` on `r'' ⊗ e' t` via `extendScalars_map` /
  --   `ModuleCat.extendScalars` action on tmul, simplify `e'.symm (e' t) = t`
  --   (`LinearEquiv.symm_apply_apply`), and pull the scalar `r''` out using R''-linearity
  --   of `phi`/`e''` plus `r'' ⊗ x = r'' • (1 ⊗ x)` (`TensorProduct.smul_tmul'`,
  --   `one_smul`), landing on `e'' (phi (r'' ⊗ t))`.
  -- Since `e'` is an R'-linear isomorphism, `φ y = e''(phi(1 ⊗ e'.symm y))` is well defined
  -- and R'-linear, and the adjunction lift `bc` has the prescribed value on generators,
  -- there being no scalar mismatch under `IsScalarTower R R' R''`.
  -- The R'-linear "curried" map φ : catTor R' M → (restrictScalars _).obj (catTor R'' M).
  let φ : (catTor R' M : Type u) →ₗ[R']
      ((ModuleCat.restrictScalars (algebraMap R' R'')).obj (catTor R'' M) : Type u) :=
    { toFun := fun y => e'' (phi (R := R) (R' := R') (R'' := R'')
        (P.complex.d 2 1).hom (P.complex.d 1 0).hom
        ((1 : R'') ⊗ₜ[R'] (e'.symm y)))
      map_add' := by
        intro y z
        simp only [map_add, TensorProduct.tmul_add]
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply]
        -- the codomain `c • _` is the restrictScalars action: `algebraMap R' R'' c • _`.
        show e'' (phi (P.complex.d 2 1).hom (P.complex.d 1 0).hom
              ((1 : R'') ⊗ₜ[R'] (e'.symm (c • y))))
          = (algebraMap R' R'' c) • e'' (phi (P.complex.d 2 1).hom (P.complex.d 1 0).hom
              ((1 : R'') ⊗ₜ[R'] (e'.symm y)))
        rw [map_smul e'.symm, show ((1 : R'') ⊗ₜ[R'] (c • e'.symm y))
              = (algebraMap R' R'' c) • ((1 : R'') ⊗ₜ[R'] (e'.symm y)) by
            rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
            congr 1
            rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]]
        rw [map_smul (phi (P.complex.d 2 1).hom (P.complex.d 1 0).hom), map_smul e''] }
  refine ⟨((ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')).homEquiv
      (catTor R' M) (catTor R'' M)).symm
      (ModuleCat.ofHom
        (Y := ((ModuleCat.restrictScalars (algebraMap R' R'')).obj (catTor R'' M) : Type u)) φ),
      ?_⟩
  intro r'' t
  rw [Adjunction.homEquiv_symm_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- reduce the functorial map on the simple tensor r'' ⊗ e' t
  show ((ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')).counit.app (catTor R'' M)).hom
      (((ModuleCat.extendScalars (algebraMap R' R'')).map
          (ModuleCat.ofHom
            (Y := ((ModuleCat.restrictScalars (algebraMap R' R'')).obj (catTor R'' M) : Type u))
            φ)).hom
        (r'' ⊗ₜ[R'] (e' t))) = _
  rw [show ((ModuleCat.extendScalars (algebraMap R' R'')).map
        (ModuleCat.ofHom
          (Y := ((ModuleCat.restrictScalars (algebraMap R' R'')).obj (catTor R'' M) : Type u))
          φ)).hom
        (r'' ⊗ₜ[R'] (e' t))
      = (r'' ⊗ₜ[R'] (φ (e' t)) :
          ((ModuleCat.extendScalars (algebraMap R' R'')).obj
            (ModuleCat.of R'
              ((ModuleCat.restrictScalars (algebraMap R' R'')).obj (catTor R'' M) : Type u))
            : Type u)) from rfl]
  rw [show ((ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')).counit.app
        (catTor R'' M)).hom (r'' ⊗ₜ[R'] (φ (e' t))) = r'' • (φ (e' t)) from rfl]
  show r'' • (e'' (phi (P.complex.d 2 1).hom (P.complex.d 1 0).hom
      ((1 : R'') ⊗ₜ[R'] (e'.symm (e' t))))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [← map_smul e'', ← map_smul (phi (P.complex.d 2 1).hom (P.complex.d 1 0).hom)]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The underlying value of `lift (cyclesMap d1)` equals `cmpMap F1` applied to the
base-changed cycle inclusion. -/
theorem lift_val (d1 : F1 →ₗ[R] F0) (v : R'' ⊗[R'] (cycles R' d1)) :
    ((TensorProduct.AlgebraTensorModule.lift
        (cyclesMap (R := R) (R' := R') (R'' := R'') d1)) v : R'' ⊗[R] F1)
      = cmpMap (R := R) (R' := R') (R'' := R'') F1
          (LinearMap.lTensor R'' (cycles R' d1).subtype v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r'' k =>
      rw [TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.lTensor_tmul]
      simp only [cyclesMap, cmpBil, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, Submodule.coe_add, hx, hy]

/-- Abstract algebraic core of the crux: given an exact tail `F1 →(d1) F0 →(eps) Mod → 0`
of `R`-modules with `R' ⊗ Mod` flat over `R'`, the cycles base-change map is surjective. -/
theorem core_surj {Mod : Type u} [AddCommGroup Mod] [Module R Mod]
    (d1 : F1 →ₗ[R] F0) (eps : F0 →ₗ[R] Mod)
    (hex : Function.Exact d1 eps) (heps : Function.Surjective eps)
    (hflat : Module.Flat R' (R' ⊗[R] Mod)) :
    Function.Surjective
      (TensorProduct.AlgebraTensorModule.lift
        (cyclesMap (R := R) (R' := R') (R'' := R'') d1)) := by
  have : Module.Flat R' (R' ⊗[R] Mod) := hflat
  -- base changed maps over R'
  set d1' : (R' ⊗[R] F1) →ₗ[R'] (R' ⊗[R] F0) := LinearMap.baseChange R' d1 with hd1'
  set eps' : (R' ⊗[R] F0) →ₗ[R'] (R' ⊗[R] Mod) := LinearMap.baseChange R' eps with heps'def
  -- exactness of (d1', eps') and surjectivity of eps'
  have hex' : Function.Exact ⇑d1' ⇑eps' := by
    rw [hd1', heps'def, LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact R' hex heps
  have heps'surj : Function.Surjective ⇑eps' := by
    rw [heps'def, LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective R' heps
  -- key equality of submodules: ker eps' = range d1'
  have hker_eps' : LinearMap.ker eps' = LinearMap.range d1' := hex'.linearMap_ker_eq
  -- injectivity of lTensor R'' (ker eps').subtype, from flatness of codomain (R' ⊗ Mod)
  have hinj : Function.Injective ⇑(LinearMap.lTensor R'' (LinearMap.ker eps').subtype) :=
    LinearMap.lTensor_injective_of_exact_of_flat eps' heps'surj
      (LinearMap.ker eps').subtype Subtype.coe_injective
      (LinearMap.exact_subtype_ker_map eps') R''
  -- corestriction g : R'⊗F1 → ker eps'
  have hrange_le : ∀ x, d1' x ∈ LinearMap.ker eps' := by
    intro x
    rw [hker_eps']
    exact ⟨x, rfl⟩
  set g : (R' ⊗[R] F1) →ₗ[R'] (LinearMap.ker eps') :=
    d1'.codRestrict (LinearMap.ker eps') hrange_le with hg
  have hgsurj : Function.Surjective ⇑g := by
    intro y
    have hy : (y : R' ⊗[R] F0) ∈ LinearMap.range d1' := by rw [← hker_eps']; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by rw [hg]; apply Subtype.ext; simpa using hx⟩
  -- ker g = cycles R' d1
  have hkerg : LinearMap.ker g = cycles R' d1 := by
    rw [hg, LinearMap.ker_codRestrict]
  -- exactness at middle of (A): subtype of ker g, then g
  have hexA0 : Function.Exact ⇑(LinearMap.ker g).subtype ⇑g :=
    LinearMap.exact_subtype_ker_map g
  -- tensor (A) by R'' : right exact
  have hexA : Function.Exact ⇑(LinearMap.lTensor R'' (LinearMap.ker g).subtype)
      ⇑(LinearMap.lTensor R'' g) :=
    lTensor_exact R'' hexA0 hgsurj
  -- d1' = (ker eps').subtype ∘ g
  have hd1'_eq : d1' = (LinearMap.ker eps').subtype.comp g := by
    rw [hg]; ext x; simp
  -- main surjectivity
  intro c
  set k'' : R'' ⊗[R] F1 := (c : R'' ⊗[R] F1) with hk''
  have hmem : (LinearMap.baseChange R'' d1) k'' = 0 := LinearMap.mem_ker.mp c.property
  -- w with cmpMap F1 w = k''
  set eqv1 := TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R'' R'' F1 with heqv1
  set w : R'' ⊗[R'] (R' ⊗[R] F1) := eqv1.symm k'' with hw
  have hcmpw : cmpMap (R := R) (R' := R') (R'' := R'') F1 w = k'' := by
    rw [hw, cmpMap, heqv1]; simp
  -- baseChange R'' d1' w = 0
  have hw0 : (LinearMap.baseChange R'' (LinearMap.baseChange R' d1)) w = 0 := by
    have hnat := LinearMap.congr_fun (cmpMap_natural (R := R) (R' := R') (R'' := R'') d1) w
    simp only [LinearMap.comp_apply] at hnat
    rw [hcmpw, hmem] at hnat
    have hcmp0inj : Function.Injective ⇑(cmpMap (R := R) (R' := R') (R'' := R'') F0) := by
      rw [cmpMap]
      exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R'' R'' F0).injective
    apply hcmp0inj
    rw [map_zero, ← hnat]
  -- w ∈ ker (lTensor R'' g)
  have hwkerg : (LinearMap.lTensor R'' g) w = 0 := by
    apply hinj
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← hd1'_eq, hd1',
      ← LinearMap.baseChange_eq_ltensor]
  -- exactness (A): w ∈ range (lTensor R'' subtype)
  rw [hexA] at hwkerg
  obtain ⟨v, hv⟩ := hwkerg
  -- transport v across ker g = cycles R' d1 via LinearEquiv.ofEq
  set e : (LinearMap.ker g) ≃ₗ[R'] (cycles R' d1) := LinearEquiv.ofEq _ _ hkerg with he
  set v' : R'' ⊗[R'] (cycles R' d1) := LinearMap.lTensor R'' e.toLinearMap v with hv'
  have hsubcomp : (cycles R' d1).subtype.comp e.toLinearMap = (LinearMap.ker g).subtype := by
    ext x; rw [he]; simp
  have hv'eq : (LinearMap.lTensor R'' (cycles R' d1).subtype) v' = w := by
    rw [hv', ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsubcomp, hv]
  refine ⟨v', ?_⟩
  apply Subtype.ext
  rw [lift_val, hv'eq, hcmpw]

/-- **CRUX of Stacks Tag 00MM — the analytic kernel: flatness ⇒ cycles base-change
is surjective.**

Write `d₁ = (P.complex.d 1 0).hom`, `K' = cycles R' d₁ = ker(d₁ ⊗ R')`,
`K'' = cycles R'' d₁`.  The natural `R''`-linear map
`R'' ⊗_{R'} K' → K''` — the `AlgebraTensorModule.lift` of `cyclesMap d₁`, which on a
generator `r'' ⊗ k` sends it to the cycle `cmpBil r'' k = cancelBaseChange (r'' ⊗ k)` —
is **surjective** whenever the `R'`-module `M ⊗ᴿ R'` (Mathlib orientation `R' ⊗ᴿ M`)
is flat over `R'`.

This is the heart of the Stacks argument; flatness enters here and
ONLY here):

Let `F• → M` be the projective resolution `P` over `R`.  Tensoring the exact tail
`F₂ → F₁ →(d₁) F₀ →(ε) M → 0` of the resolution by `R'` over `R` (right-exact) yields an
exact sequence of `R'`-modules
  `F₁⊗R' →(d₁') F₀⊗R' →(ε') M⊗R' → 0`,
and `K' := ker d₁' ` fits in the two short exact sequences of `R'`-modules
  (A)  `0 → K' → F₁⊗R' →(d₁') I' → 0`,   where `I' := im d₁' = ker ε' ⊆ F₀⊗R'`,
  (B)  `0 → I' → F₀⊗R' →(ε') M⊗R' → 0`.
(Exactness of (B) at `I'` and `M⊗R'` is exactly right-exactness of `(-)⊗_R R'` applied
to `F₀ → M → 0` together with `I' = ker ε'`.)

Now apply `(-) ⊗_{R'} R''` (`lTensor`/`rTensor` over `R'`).
• Sequence (B): because `M ⊗ᴿ R'` is **flat over `R'`** — equivalently
  `Tor₁^{R'}(M⊗R', R'') = 0` — tensoring (B) by `R''` keeps it short-exact; in
  particular the induced map `I'⊗_{R'}R'' → F₀⊗_{R'}R''` is **injective**.
  (`Module.Flat` ⇒ `lTensor`/`rTensor` preserves injections:
  `Module.Flat.lTensor_preserves_injective_linearMap` /
  `Module.Flat.lTensor_exact`.)
• Sequence (A): tensoring by `R''` is right-exact, giving the exact row
  `K'⊗_{R'}R'' → F₁⊗_{R'}R'' →(d₁'⊗R'') I'⊗_{R'}R'' → 0`
  (`_root_.lTensor_exact`/`rTensor_exact`), so
  `im(K'⊗R'' → F₁⊗R'') = ker(F₁⊗R'' → I'⊗R'')`.

Under the canonical identifications `Fᵢ⊗ᴿ R' ⊗_{R'} R'' ≅ Fᵢ⊗ᴿ R''`
(`cancelBaseChange` = `cmpMap`), the composite `F₁⊗R'' →(d₁'') F₀⊗R''` equals
`F₁⊗R'' → I'⊗R'' ↪ F₀⊗R''`, and the second map is injective (flatness, from (B)).
Hence
  `K'' = ker d₁'' = ker(F₁⊗R'' → I'⊗R'') = im(K'⊗R'' → F₁⊗R'')`.
But `im(K'⊗R'' → F₁⊗R'')` lands inside `K''` and equals the image of our map
`R''⊗_{R'}K' → K''` (this is `cmpBil`/`cyclesMap` transported across `cancelBaseChange`,
which is precisely how `cyclesMap`/`cmpMap` are defined).  Therefore that map is onto
`K''`, i.e. `AlgebraTensorModule.lift (cyclesMap d₁)` is surjective.  ∎

Flatness of `M ⊗ᴿ R'` over `R'` is the only hypothesis used. -/
@[ega "III 7.6.11.6" "partial"]
theorem cycles_baseChange_surjective
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hflat : Module.Flat R' (R' ⊗[R] (M : Type u))) :
    Function.Surjective
      (TensorProduct.AlgebraTensorModule.lift
        (cyclesMap (R := R) (R' := R') (R'' := R'') (P.complex.d 1 0).hom)) := by
  -- differentials; surjectivity held exactly iff coker(d₁')=M⊗R' is flat over R'
  -- (zero mismatches), confirming the hypothesis is exactly the controlling condition.
  have hex : Function.Exact ⇑(P.complex.d 1 0).hom ⇑(P.π.f 0).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀
  exact core_surj (R'' := R'') (P.complex.d 1 0).hom (P.π.f 0).hom hex
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) hflat

/-- **Stacks Tag 00MM (Lemma 10.99.12).**

Let `R → R' → R''` be ring maps and let `M` be an `R`-module with a chosen projective
resolution `P` over `R`.  If the `R'`-module `M ⊗ᴿ R'` is flat over `R'`, then the
natural base-change map

  `Φ : R'' ⊗_{R'} Tor₁ᴿ(M, R') → Tor₁ᴿ(M, R'')`

(equivalently `Tor₁ᴿ(M, R') ⊗_{R'} R'' → Tor₁ᴿ(M, R'')`), characterized by `phi_apply_mk`,
is surjective. Here `Tor₁ᴿ` is the resolution model `H₁(P ⊗ᴿ -)`; `Φ` is *not* identified
with the canonical base-change natural transformation on derived functors (see the caveat
on `exists_baseChange_eq_phi`).

The reduction to `cycles_baseChange_surjective` runs as follows.
`Tor1 R'' = K''/B''` is a quotient of `K'' = cycles R'' d₁`, so by surjectivity of the
quotient map `Submodule.Quotient.mk` it suffices to hit every class `⟦c⟧` with
`c ∈ K''`.  By the crux `cycles_baseChange_surjective`, `c = cyclesBC z` for some
`z ∈ R'' ⊗_{R'} K'`, where `cyclesBC = AlgebraTensorModule.lift (cyclesMap d₁)`.  Pushing
`z` through `lTensor R'' (mkQ : K' → Tor1 R')` gives an element of `R'' ⊗_{R'} Tor1 R'`,
and the square
  `phi ∘ (id ⊗ mkQ)  =  mkQ'' ∘ cyclesBC`
commutes on generators `r'' ⊗ k` by `phi_apply_mk` (both sides are `⟦cmpBil r'' k⟧`).
Hence `phi (lTensor mkQ z) = mkQ''(cyclesBC z) = ⟦c⟧`, proving surjectivity. -/
@[stacks 00MM "Proved for the resolution model Tor1 S = H₁(P ⊗ᴿ S); the map is the \
explicit phi, not identified with the canonical derived base-change natural \
transformation."]
theorem tor_baseChange_surjective
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    -- flatness hypothesis: `M ⊗ᴿ R'`, as an `R'`-module, is flat over `R'`.
    -- We use `R' ⊗ᴿ M`, the standard Mathlib orientation with `R'` on the left,
    -- which is canonically `R'`-isomorphic to `M ⊗ᴿ R'`.
    (hflat : Module.Flat R' (R' ⊗[R] (M : Type u))) :
    Function.Surjective
      (phi (R := R) (R' := R') (R'' := R'')
        (P.complex.d 2 1).hom (P.complex.d 1 0).hom) := by
  set d1 := (P.complex.d 1 0).hom with hd1
  set d2 := (P.complex.d 2 1).hom with hd2
  -- the R'-linear quotient map  cycles R' d1 → Tor1 R' d2 d1
  set qmk : (cycles R' d1) →ₗ[R'] (Tor1 R' d2 d1) :=
    ((boundaries R' d2).comap (cycles R' d1).subtype).mkQ with hqmk
  -- the crux: the natural map  R'' ⊗_{R'} K' → K''  is surjective.
  have hcrux := cycles_baseChange_surjective (R'' := R'') M P hflat
  set cyclesBC := TensorProduct.AlgebraTensorModule.lift
    (cyclesMap (R := R) (R' := R') (R'' := R'') d1) with hcbc
  intro t
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨z, hz⟩ := hcrux c
  refine ⟨(LinearMap.lTensor R'' qmk) z, ?_⟩
  -- commuting square  phi ∘ (id ⊗ qmk) = mkQ'' ∘ cyclesBC, checked on generators
  have hsq : ∀ w : R'' ⊗[R'] (cycles R' d1),
      phi (R := R) (R' := R') (R'' := R'') d2 d1 ((LinearMap.lTensor R'' qmk) w)
        = Submodule.Quotient.mk (cyclesBC w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r'' k =>
        rw [LinearMap.lTensor_tmul, hqmk,
          show ((boundaries R' d2).comap (cycles R' d1).subtype).mkQ k
            = Submodule.Quotient.mk k from rfl,
          phi_apply_mk, hcbc, TensorProduct.AlgebraTensorModule.lift_tmul]
        rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, Submodule.Quotient.mk_add]
  rw [hsq z, hz]

end Stacks.TorOneBaseChange

end
