module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.IdealAnnihilator
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension

/-!
# Quasi-coherence of the sections annihilated by an ideal sheaf

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals of finite type — recorded as a
quasi-coherent module `I` together with a monomorphism `i : I ⟶ 𝒪_X` — and let `F` be a
quasi-coherent `𝒪_X`-module. `AlgebraicGeometry.annihilatorSubsheaf` is the subsheaf of `F`
whose sections are annihilated by `I`. This file proves that it is again quasi-coherent, that on
an affine open its sections are tested by the sections of `I` over that open alone, and that its
stalk at a point is the submodule of the stalk of `F` annihilated by the stalk of `I`.

## Main results

* `AlgebraicGeometry.annihilatorSubsheaf_isQuasicoherent`: the annihilator subsheaf is
  quasi-coherent.
* `AlgebraicGeometry.mem_annihilatorSubsheaf_iff_of_isAffine`: on an affine open, a section lies
  in the annihilator subsheaf as soon as it is killed by the sections of `I` over that open.
* `AlgebraicGeometry.mem_range_stalk_annihilatorSubsheaf_iff`: the image of the stalk of the
  annihilator subsheaf in the stalk of `F` consists of the germs killed by the ideal.

## Implementation notes

The three statements are affine-local, and on an affine open `U` the module `Γ(I, U)` is finite
over `Γ(X, U)`, by `Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`. Choosing finitely
many generators `a₁, …, aₙ` turns the annihilator of the whole ideal into the common kernel of
the `n` multiplication endomorphisms, which is built here as the iterated kernel
`smulKernelTower`. Each stage is quasi-coherent by
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, so quasi-coherence follows from
affine-locality, `AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen`.

That the annihilation condition only has to be tested on an affine open itself, rather than on
all smaller opens, uses that sections of a quasi-coherent module on a principal open are a
localization, `AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs`: a section of
`I` over a principal open becomes, after multiplication by a unit, the restriction of a section
over the ambient affine open.

Rewriting underneath the scalar action is avoided throughout: the coefficient of `•` is a
section of `X.ringCatSheaf`, which the presheaf of modules sees through a coercion that the
keyed matching of `rw` does not look through, so each identity is stated as a `have` at the
spelling the goal uses and composed with `congrArg` or inside a `calc`.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I F : X.Modules) (i : I ⟶ SheafOfModules.unit X.ringCatSheaf)
  [Mono i]

/-! ### Multiplication by a global section -/

omit [Mono i] in
/-- Multiplication by a global section of the structure sheaf, as an endomorphism of a module
on a scheme. -/
private noncomputable def smulEndomorphism {Y : Scheme.{u}} (G : Y.Modules) (a : Γ(Y, ⊤)) :
    G ⟶ G :=
  ⟨{ app := fun U =>
        letI : CommSemiring (Y.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommSemiring (Y.presheaf.obj U))
        ModuleCat.ofHom (LinearMap.lsmul _ (G.val.obj U)
          (show ↑(Y.ringCatSheaf.obj.obj U) from
            Y.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a))
     naturality := by
        intro U V f
        have hcoeff : Y.presheaf.map f (Y.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) =
            Y.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op a := by
          rw [← Y.presheaf.map_comp_apply, show f = f.unop.op from rfl, ← op_comp,
            show f.unop ≫ homOfLE (le_top : U.unop ≤ ⊤) = homOfLE (le_top : V.unop ≤ ⊤) from
              Subsingleton.elim _ _]
        ext x
        change (show ↑(Y.ringCatSheaf.obj.obj V) from
            Y.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op a) • G.val.map f x =
          G.val.map f ((show ↑(Y.ringCatSheaf.obj.obj U) from
            Y.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) • x)
        rw [G.val.map_smul]
        exact congrArg (· • G.val.map f x) hcoeff.symm }⟩

omit [Mono i] in
private lemma smulEndomorphism_app {Y : Scheme.{u}} (G : Y.Modules) (a : Γ(Y, ⊤))
    (U : Y.Opens) (s : Γ(G, U)) :
    (smulEndomorphism G a).app U s =
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • s :=
  rfl

omit [Mono i] in
private lemma smulEndomorphism_naturality {Y : Scheme.{u}} {G H : Y.Modules} (φ : G ⟶ H)
    (a : Γ(Y, ⊤)) :
    smulEndomorphism G a ≫ φ = φ ≫ smulEndomorphism H a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change φ.app U (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • s) =
    Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • φ.app U s
  exact Scheme.Modules.Hom.app_smul φ _ _

/-! ### The common kernel of finitely many multiplications -/

omit [Mono i] in
/-- The iterated kernel of the first `n` multiplication endomorphisms of a sequence of global
sections. -/
private noncomputable def smulKernelTower {Y : Scheme.{u}} (G : Y.Modules) (a : ℕ → Γ(Y, ⊤)) :
    ℕ → Y.Modules
  | 0 => G
  | n + 1 => kernel (smulEndomorphism (smulKernelTower G a n) (a n))

omit [Mono i] in
/-- The canonical monomorphism from the `n`-th stage of `smulKernelTower` into the module. -/
private noncomputable def smulKernelTowerι {Y : Scheme.{u}} (G : Y.Modules) (a : ℕ → Γ(Y, ⊤)) :
    ∀ n, smulKernelTower G a n ⟶ G
  | 0 => 𝟙 G
  | n + 1 => kernel.ι (smulEndomorphism (smulKernelTower G a n) (a n)) ≫ smulKernelTowerι G a n

omit [Mono i] in
private instance smulKernelTower_isQuasicoherent {Y : Scheme.{u}} (G : Y.Modules)
    (a : ℕ → Γ(Y, ⊤)) [G.IsQuasicoherent] (n : ℕ) : (smulKernelTower G a n).IsQuasicoherent := by
  induction n with
  | zero => exact inferInstanceAs G.IsQuasicoherent
  | succ n ih =>
      let : (smulKernelTower G a n).IsQuasicoherent := ih
      exact inferInstanceAs (kernel (smulEndomorphism (smulKernelTower G a n) (a n))
        ).IsQuasicoherent

omit [Mono i] in
private instance smulKernelTowerι_mono {Y : Scheme.{u}} (G : Y.Modules) (a : ℕ → Γ(Y, ⊤))
    (n : ℕ) : Mono (smulKernelTowerι G a n) := by
  induction n with
  | zero => exact inferInstanceAs (Mono (𝟙 G))
  | succ n ih =>
      let := ih
      exact inferInstanceAs (Mono (kernel.ι _ ≫ smulKernelTowerι G a n))

omit [Mono i] in
private lemma smulKernelTowerι_comp_smulEndomorphism {Y : Scheme.{u}} (G : Y.Modules)
    (a : ℕ → Γ(Y, ⊤)) (n : ℕ) (k : ℕ) (hk : k < n) :
    smulKernelTowerι G a n ≫ smulEndomorphism G (a k) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      change (kernel.ι (smulEndomorphism (smulKernelTower G a n) (a n)) ≫
        smulKernelTowerι G a n) ≫ smulEndomorphism G (a k) = 0
      rw [Category.assoc]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | rfl
      · rw [ih hkn, comp_zero]
      · rw [← smulEndomorphism_naturality (smulKernelTowerι G a k) (a k), ← Category.assoc,
          kernel.condition, zero_comp]

omit [Mono i] in
private lemma exists_lift_smulKernelTower {Y : Scheme.{u}} {G H : Y.Modules} (a : ℕ → Γ(Y, ⊤))
    (n : ℕ) (j : H ⟶ G) (hj : ∀ k, k < n → j ≫ smulEndomorphism G (a k) = 0) :
    ∃ l : H ⟶ smulKernelTower G a n, l ≫ smulKernelTowerι G a n = j := by
  induction n with
  | zero => exact ⟨j, Category.comp_id _⟩
  | succ n ih =>
      obtain ⟨l, hl⟩ := ih fun k hk => hj k (by omega)
      have hz : l ≫ smulEndomorphism (smulKernelTower G a n) (a n) = 0 := by
        apply (cancel_mono (smulKernelTowerι G a n)).mp
        rw [Category.assoc, smulEndomorphism_naturality, ← Category.assoc, hl,
          hj n (by omega), zero_comp]
      refine ⟨kernel.lift _ l hz, ?_⟩
      change kernel.lift _ l hz ≫ kernel.ι (smulEndomorphism (smulKernelTower G a n) (a n)) ≫
        smulKernelTowerι G a n = j
      rw [← Category.assoc, kernel.lift_ι, hl]

/-! ### Testing the annihilation condition on finitely many generators -/

omit [Mono i] in
/-- For a finite module `J` over `R` and an `R`-linear map `φ : J →ₗ[R] R`, the sections of `M`
killed by all of `φ '' J` are those killed by the images of finitely many generators. -/
private lemma forall_smul_eq_zero_iff_of_finite {R M J : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup J] [Module R J] [Module.Finite R J] (φ : J →ₗ[R] R) (s : M)
    (n : ℕ) (q : (Fin n → R) →ₗ[R] J) (hq : Function.Surjective q) :
    (∀ r : J, φ r • s = 0) ↔ ∀ k : Fin n, φ (q (Pi.single k 1)) • s = 0 := by
  classical
  refine ⟨fun h k => h _, fun h r => ?_⟩
  obtain ⟨v, rfl⟩ := hq r
  have hsingle (k : Fin n) : Pi.single k (v k) = v k • Pi.single k 1 := by
    ext l
    by_cases hl : l = k <;> simp [hl]
  have hφ : φ (q v) = ∑ k, v k * φ (q (Pi.single k 1)) := by
    calc φ (q v) = φ (q (∑ k, Pi.single k (v k))) := by rw [Finset.univ_sum_single]
      _ = ∑ k, φ (q (Pi.single k (v k))) := by rw [map_sum, map_sum]
      _ = ∑ k, v k * φ (q (Pi.single k 1)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsingle, q.map_smul, φ.map_smul, smul_eq_mul]
  rw [hφ, Finset.sum_smul]
  exact Finset.sum_eq_zero fun k _ => by rw [mul_smul, h k, smul_zero]

/-- The sections of the ideal over an affine open, as a linear form on `Γ(X, U)`. -/
private noncomputable def idealSectionsLinearMap (U : X.Opens) : Γ(I, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun r := show Γ(X, U) from i.app U r
  map_add' r t := map_add (ConcreteCategory.hom (i.app U)) r t
  map_smul' a r := Scheme.Modules.Hom.app_smul i a r

/-- The map `i` commutes with restriction of sections. -/
private lemma app_map_eq {X : Scheme.{u}} (I : X.Modules)
    (i : I ⟶ SheafOfModules.unit X.ringCatSheaf) {U V : X.Opens} (v : V ⟶ U) (r : Γ(I, U)) :
    (show Γ(X, V) from i.app V (I.presheaf.map v.op r)) =
      X.presheaf.map v.op (show Γ(X, U) from i.app U r) :=
  congrArg (fun q => (show Γ(X, V) from q r)) (i.mapPresheaf.naturality v.op)

omit [Mono i] in
/-- On an open `V` inside an affine open `U`, a section of `F` killed by the images of finitely
many generators of `Γ(I, U)` is killed by all of `Γ(I, U)`. -/
private lemma forall_restrict_smul_eq_zero (U V : X.Opens) (v : V ⟶ U) (s : Γ(F, V))
    [Module.Finite Γ(X, U) Γ(I, U)] (n : ℕ) (q : (Fin n → Γ(X, U)) →ₗ[Γ(X, U)] Γ(I, U))
    (hq : Function.Surjective q)
    (hs : ∀ k : Fin n,
      X.presheaf.map v.op (show Γ(X, U) from i.app U (q (Pi.single k 1))) • s = 0) :
    ∀ a : Γ(I, U), X.presheaf.map v.op (show Γ(X, U) from i.app U a) • s = 0 := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map v.op).hom.toAlgebra
  let : Module Γ(X, U) Γ(F, V) := Module.compHom Γ(F, V) (X.presheaf.map v.op).hom
  let : IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key : ∀ a : Γ(I, U), idealSectionsLinearMap I i U a • s = 0 := by
    refine (forall_smul_eq_zero_iff_of_finite (idealSectionsLinearMap I i U) s n q hq).2 fun k =>
      ?_
    have hk := hs k
    change algebraMap Γ(X, U) Γ(X, V) (idealSectionsLinearMap I i U (q (Pi.single k 1))) • s = 0
      at hk
    rwa [IsScalarTower.algebraMap_smul] at hk
  intro a
  have ha := key a
  change algebraMap Γ(X, U) Γ(X, V) (idealSectionsLinearMap I i U a) • s = 0
  rwa [IsScalarTower.algebraMap_smul]

/-! ### Passing from an affine open to a principal open inside it -/

omit [Mono i] in
/-- A section over a principal open of an affine open killed by the restrictions of the sections
of `I` over that affine open is killed by every section of `I` over the principal open. -/
private lemma smul_eq_zero_of_restrict_basicOpen [I.IsQuasicoherent] (U : X.affineOpens)
    (f : Γ(X, U.1)) (s : Γ(F, X.basicOpen f))
    (hs : ∀ a : Γ(I, U.1),
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (show Γ(X, U.1) from i.app U.1 a) • s = 0)
    (r : Γ(I, X.basicOpen f)) :
    (show Γ(X, X.basicOpen f) from i.app (X.basicOpen f) r) • s = 0 := by
  classical
  let V := X.basicOpen f
  let j : V ⟶ U.1 := homOfLE (X.basicOpen_le f)
  let ρ := (X.presheaf.map j.op).hom
  let resI := Scheme.Modules.restrictionLinearMap I j
  let : Algebra Γ(X, U.1) Γ(X, V) := ρ.toAlgebra
  let : Module Γ(X, U.1) Γ(I, V) := Module.compHom Γ(I, V) ρ
  let : Module Γ(X, U.1) Γ(F, V) := Module.compHom Γ(F, V) ρ
  let : IsScalarTower Γ(X, U.1) Γ(X, V) Γ(I, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(X, U.1) Γ(X, V) Γ(F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsLocalizedModule (Submonoid.powers f) resI :=
    isLocalizedModule_restriction_basicOpen_of_qcqs I U.2.isCompact U.2.isQuasiSeparated f
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalizedModule.surj (S := Submonoid.powers f) resI r
  let c : Γ(X, V) := ρ d
  have hd' : c • r = resI a := by
    change algebraMap Γ(X, U.1) Γ(X, V) (d : Γ(X, U.1)) • r = resI a
    rwa [IsScalarTower.algebraMap_smul]
  have hz : c • ((show Γ(X, V) from i.app V r) • s) = 0 := by
    calc c • ((show Γ(X, V) from i.app V r) • s)
        = (c * (show Γ(X, V) from i.app V r)) • s := (mul_smul _ _ _).symm
      _ = (show Γ(X, V) from i.app V (c • r)) • s :=
          congrArg (· • s) (Scheme.Modules.Hom.app_smul (φ := i) c r).symm
      _ = (show Γ(X, V) from i.app V (resI a)) • s := by rw [hd']
      _ = (show Γ(X, V) from X.presheaf.map j.op (i.app U.1 a)) • s := (app_map_eq I i j a) ▸ rfl
      _ = 0 := hs a
  obtain ⟨k, hk⟩ := d.2
  obtain ⟨u, hu⟩ : IsUnit c := by
    change IsUnit (ρ d)
    rw [← hk, map_pow]
    exact (X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen f).pow k
  calc (show Γ(X, V) from i.app V r) • s
      = (↑u⁻¹ * c) • ((show Γ(X, V) from i.app V r) • s) := by
        rw [← hu]
        simp
    _ = (↑u⁻¹ : Γ(X, V)) • (c • ((show Γ(X, V) from i.app V r) • s)) := mul_smul _ _ _
    _ = 0 := by rw [hz, smul_zero]

omit [Mono i] in
/-- A section of `F` over an open `V` inside an affine open `U` which is killed by the
restrictions of the sections of `I` over `U` satisfies the local annihilation condition. -/
private lemma locally_annihilated_of_restrict [I.IsQuasicoherent] (U : X.affineOpens)
    (V : X.Opens) (v : V ⟶ U.1) (s : Γ(F, V))
    (hs : ∀ a : Γ(I, U.1),
      X.presheaf.map v.op (show Γ(X, U.1) from i.app U.1 a) • s = 0) :
    ∀ (W : X.Opens) (w : W ⟶ V) (r : Γ(I, W)),
      (show Γ(X, W) from i.app W r) • F.presheaf.map w.op s = 0 := by
  intro W w r
  apply F.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ ((w ≫ v) ⟨x, hx⟩).property
  let b : X.basicOpen f ⟶ W := homOfLE hfW
  have hsB : ∀ a : Γ(I, U.1),
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (show Γ(X, U.1) from i.app U.1 a) •
        F.presheaf.map (b ≫ w).op s = 0 := by
    intro a
    have h := congrArg (F.presheaf.map (b ≫ w).op) (hs a)
    rwa [F.map_smul, map_zero, ← X.presheaf.map_comp_apply] at h
  have hz := smul_eq_zero_of_restrict_basicOpen I F i U f (F.presheaf.map (b ≫ w).op s) hsB
    (I.presheaf.map b.op r)
  refine ⟨X.basicOpen f, hfW, hxf, ?_⟩
  change F.presheaf.map b.op ((show Γ(X, W) from i.app W r) • F.presheaf.map w.op s) =
    F.presheaf.map b.op 0
  rw [F.map_smul, map_zero, ← F.presheaf.map_comp_apply]
  rwa [← app_map_eq I i b r]

/-! ### The annihilator on an affine open -/

/-- **Stacks, Tag 01PO (2).** On an affine open it suffices to test annihilation by the sections
of the ideal over that open itself. -/
@[stacks 01PO "part (2)"]
theorem mem_annihilatorSubsheaf_iff_of_isAffine [I.IsQuasicoherent] (U : X.affineOpens)
    (s : Γ(F, U.1)) :
    s ∈ (annihilatorSubsheaf I F i).toSubmodule.obj (op U.1) ↔
      ∀ r : Γ(I, U.1), (show Γ(X, U.1) from i.app U.1 r) • s = 0 := by
  rw [mem_annihilatorSubsheaf_iff]
  refine ⟨fun h r => by simpa using h U.1 (𝟙 U.1) r, fun h => ?_⟩
  refine locally_annihilated_of_restrict I F i U U.1 (𝟙 _) s fun a => ?_
  change X.presheaf.map (𝟙 (op U.1)) (i.app U.1 a) • s = 0
  rw [X.presheaf.map_id]
  exact h a

/-! ### Quasi-coherence -/

omit [Mono i] in
/-- Multiplication by a section of the structure sheaf over `U`, as an endomorphism of the
restriction of `F` to the open subscheme `U`. -/
private noncomputable def restrictedSmulEndomorphism (U : X.Opens) (a : Γ(X, U)) :
    F.restrict U.ι ⟶ F.restrict U.ι :=
  smulEndomorphism (F.restrict U.ι) (X.presheaf.map (eqToHom U.ι_image_top).op a)

omit [Mono i] in
private lemma restrictedSmulEndomorphism_app (U : X.Opens) (a : Γ(X, U))
    (V : U.toScheme.Opens) (s : Γ(F.restrict U.ι, V)) :
    (restrictedSmulEndomorphism F U a).app V s =
      X.presheaf.map (homOfLE (U.ι_image_le V)).op a • (show Γ(F, U.ι ''ᵁ V) from s) := by
  let r : Γ(U.toScheme, V) :=
    U.toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (X.presheaf.map (eqToHom U.ι_image_top).op a)
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι F V r s
  change r • s = (U.ι.appIso V).inv r • (show Γ(F, U.ι ''ᵁ V) from s) at h
  refine h.trans ?_
  rw [Scheme.Opens.ι_appIso]
  change X.presheaf.map (U.ι.opensFunctor.map (homOfLE (le_top : V ≤ ⊤))).op
    (X.presheaf.map (eqToHom U.ι_image_top).op a) • (show Γ(F, U.ι ''ᵁ V) from s) = _
  rw [← X.presheaf.map_comp_apply]
  rfl

private lemma restrict_annihilatorSubsheaf_comp_smul (U : X.Opens) (a : Γ(I, U)) :
    (restrictFunctor U.ι).map (annihilatorSubsheaf I F i).ι ≫
      restrictedSmulEndomorphism F U (i.app U a) = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  change (restrictedSmulEndomorphism F U (i.app U a)).app V s.val = 0
  refine (restrictedSmulEndomorphism_app F U (i.app U a) V s.val).trans ?_
  have hz := (mem_annihilatorSubsheaf_iff I F i (U.ι ''ᵁ V) s.val).mp s.property
    (U.ι ''ᵁ V) (𝟙 _) (I.presheaf.map (homOfLE (U.ι_image_le V)).op a)
  simp only [op_id] at hz
  rw [F.presheaf.map_id] at hz
  change (show Γ(X, U.ι ''ᵁ V) from
    i.app (U.ι ''ᵁ V) (I.presheaf.map (homOfLE (U.ι_image_le V)).op a)) •
      (show Γ(F, U.ι ''ᵁ V) from s.val) = 0 at hz
  rwa [app_map_eq I i] at hz

private lemma exists_lift_restrict_annihilatorSubsheaf [I.IsQuasicoherent] (U : X.affineOpens)
    {K : U.1.toScheme.Modules} (φ : K ⟶ F.restrict U.1.ι)
    (hφ : ∀ (V : U.1.toScheme.Opens) (s : Γ(K, V)) (a : Γ(I, U.1)),
      X.presheaf.map (homOfLE (U.1.ι_image_le V)).op (i.app U.1 a) •
        (show Γ(F, U.1.ι ''ᵁ V) from φ.app V s) = 0) :
    ∃ ψ : K ⟶ Scheme.Modules.restrict (annihilatorSubsheaf I F i).toSheafOfModules U.1.ι,
      ψ ≫ (restrictFunctor U.1.ι).map (annihilatorSubsheaf I F i).ι = φ := by
  have hmem (V : U.1.toScheme.Opens) (s : Γ(K, V)) :
      φ.app V s ∈ (annihilatorSubsheaf I F i).toSubmodule.obj (op (U.1.ι ''ᵁ V)) :=
    (mem_annihilatorSubsheaf_iff I F i (U.1.ι ''ᵁ V) (φ.app V s)).mpr
      (locally_annihilated_of_restrict I F i U _ (homOfLE (U.1.ι_image_le V)) (φ.app V s)
        (hφ V s))
  let appHom (V : (U.1.toScheme.Opens)ᵒᵖ) :
      K.val.obj V ⟶
        (Scheme.Modules.restrict (annihilatorSubsheaf I F i).toSheafOfModules U.1.ι).val.obj V :=
    (ModuleCat.homEquiv (M := K.val.obj V)
      (N := (Scheme.Modules.restrict (annihilatorSubsheaf I F i).toSheafOfModules
        U.1.ι).val.obj V)).symm
      { toFun := fun s => ⟨φ.app V.unop s, hmem V.unop s⟩
        map_add' := fun s t => Subtype.ext ((φ.val.app V).hom.map_add s t)
        map_smul' := fun a s => Subtype.ext ((φ.val.app V).hom.map_smul a s) }
  refine ⟨⟨{ app := appHom
             naturality := by
               intro V W f
               ext s
               exact Subtype.ext (congrArg (fun q => q s) (φ.mapPresheaf.naturality f)) }⟩, ?_⟩
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  rfl

/-- **Stacks, Tag 01PO (1).** The subsheaf of sections annihilated by a quasi-coherent ideal
sheaf of finite type is quasi-coherent. -/
@[stacks 01PO "part (1)"]
theorem annihilatorSubsheaf_isQuasicoherent [I.IsQuasicoherent] [I.IsFiniteType]
    [F.IsQuasicoherent] :
    (annihilatorSubsheaf I F i).toSheafOfModules.IsQuasicoherent := by
  classical
  refine isQuasicoherent_of_restrict_isAffineOpen _ fun U hU => ?_
  let Ua : X.affineOpens := ⟨U, hU⟩
  let : Module.Finite Γ(X, U) Γ(I, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections I hU
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' Γ(X, U) Γ(I, U)
  let c : ℕ → Γ(X, U) := fun k => if hk : k < n then i.app U (q (Pi.single ⟨k, hk⟩ 1)) else 0
  let a : ℕ → Γ(U.toScheme, ⊤) := fun k => X.presheaf.map (eqToHom U.ι_image_top).op (c k)
  have hc (k : ℕ) (hk : k < n) : c k = i.app U (q (Pi.single ⟨k, hk⟩ 1)) := dite_eq_left hk
  let G := F.restrict U.ι
  let H := Scheme.Modules.restrict (annihilatorSubsheaf I F i).toSheafOfModules U.ι
  let j : H ⟶ G := (restrictFunctor U.ι).map (annihilatorSubsheaf I F i).ι
  let φ : smulKernelTower G a n ⟶ G := smulKernelTowerι G a n
  have hj : ∀ k, k < n → j ≫ smulEndomorphism G (a k) = 0 := by
    intro k hk
    change j ≫ smulEndomorphism G (X.presheaf.map (eqToHom U.ι_image_top).op (c k)) = 0
    rw [hc k hk]
    exact restrict_annihilatorSubsheaf_comp_smul I F i U (q (Pi.single ⟨k, hk⟩ 1))
  obtain ⟨l, hl⟩ := exists_lift_smulKernelTower a n j hj
  obtain ⟨ψ, hψ⟩ := exists_lift_restrict_annihilatorSubsheaf I F i Ua φ (by
    intro V s
    refine forall_restrict_smul_eq_zero I F i U (U.ι ''ᵁ V) (homOfLE (U.ι_image_le V))
      (φ.app V s) n q hq fun k => ?_
    have hz := congrArg (fun f => f.app V s) (smulKernelTowerι_comp_smulEndomorphism G a n k
      k.isLt)
    change (restrictedSmulEndomorphism F U (c k)).app V (φ.app V s) = 0 at hz
    rwa [restrictedSmulEndomorphism_app, hc k k.isLt] at hz)
  have : Mono j := by
    apply (SheafOfModules.forget U.toScheme.ringCatSheaf).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro V s t h
    exact Subtype.ext h
  have hiso : H ≅ smulKernelTower G a n :=
    { hom := l
      inv := ψ
      hom_inv_id := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hψ, hl, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono φ).mp
        rw [Category.assoc, hl, hψ, Category.id_comp] }
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso hiso.symm
    (smulKernelTower_isQuasicoherent G a n)

/-! ### Stalks -/

private lemma germ_smul_eq_zero_of_mem_range_stalk [I.IsQuasicoherent] (x : X)
    (s : F.presheaf.stalk x)
    (h : ∃ t : (Scheme.Modules.presheaf (annihilatorSubsheaf I F i).toSheafOfModules).stalk x,
      ((TopCat.Presheaf.stalkFunctor Ab x).map
        (Scheme.Modules.Hom.mapPresheaf (annihilatorSubsheaf I F i).ι)).hom t = s) :
    ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)), F.presheaf.germ U x hx t = s →
      ∀ r : Γ(I, U), F.presheaf.germ U x hx ((show Γ(X, U) from i.app U r) • t) = 0 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨V, hxV, aV, ha⟩ := TopCat.Presheaf.exists_germ_eq
    (Scheme.Modules.presheaf (annihilatorSubsheaf I F i).toSheafOfModules) g
  have hsource : F.presheaf.germ V x hxV aV.val = s := by
    rwa [← ha, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hg
  intro U hx t ht r
  have hxW : x ∈ U ⊓ V := ⟨hx, hxV⟩
  let wU : U ⊓ V ⟶ U := homOfLE inf_le_left
  let wV : U ⊓ V ⟶ V := homOfLE inf_le_right
  have hkill := (mem_annihilatorSubsheaf_iff I F i V aV.val).mp aV.property (U ⊓ V) wV
    (I.presheaf.map wU.op r)
  have hcoeff : TopCat.Presheaf.germ (C := RingCat) X.ringCatSheaf.obj U x hx
        (show Γ(X, U) from i.app U r) =
      TopCat.Presheaf.germ (C := RingCat) X.ringCatSheaf.obj (U ⊓ V) x hxW
        (show Γ(X, U ⊓ V) from i.app (U ⊓ V) (I.presheaf.map wU.op r)) := by
    rw [← TopCat.Presheaf.germ_res_apply (C := RingCat) X.ringCatSheaf.obj wU x hxW
      (show Γ(X, U) from i.app U r)]
    exact congrArg _ (app_map_eq I i wU r).symm
  have hsection : F.presheaf.germ (U ⊓ V) x hxW (F.presheaf.map wV.op aV.val) = s :=
    (TopCat.Presheaf.germ_res_apply F.presheaf wV x hxW aV.val).trans hsource
  have hsmulW := PresheafOfModules.germ_ringCat_smul F.val x (U ⊓ V) hxW
    (show Γ(X, U ⊓ V) from i.app (U ⊓ V) (I.presheaf.map wU.op r))
    (F.presheaf.map wV.op aV.val)
  have hz : F.presheaf.germ (U ⊓ V) x hxW
      ((show Γ(X, U ⊓ V) from i.app (U ⊓ V) (I.presheaf.map wU.op r)) •
        F.presheaf.map wV.op aV.val) = 0 := by
    simpa using congrArg (F.presheaf.germ (U ⊓ V) x hxW) hkill
  have htarget := PresheafOfModules.germ_ringCat_smul F.val x U hx
    (show Γ(X, U) from i.app U r) t
  change F.presheaf.germ U x hx ((show Γ(X, U) from i.app U r) • t) = _ at htarget
  change (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf U x hx)) t = s at ht
  rw [ht] at htarget
  rw [htarget, hcoeff, ← hsection]
  exact hsmulW.symm.trans hz

/-- **Stacks, Tag 01PO (3).** The germs of the annihilator subsheaf at a point are exactly the
germs of `F` annihilated by the stalk of the ideal. -/
@[stacks 01PO "part (3)"]
theorem mem_range_stalk_annihilatorSubsheaf_iff [I.IsQuasicoherent] [I.IsFiniteType]
    [F.IsQuasicoherent] (x : X) (s : F.presheaf.stalk x) :
    (∃ t : (Scheme.Modules.presheaf (annihilatorSubsheaf I F i).toSheafOfModules).stalk x,
      ((TopCat.Presheaf.stalkFunctor Ab x).map
        (Scheme.Modules.Hom.mapPresheaf (annihilatorSubsheaf I F i).ι)).hom t = s) ↔
      ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)), F.presheaf.germ U x hx t = s →
        ∀ r : Γ(I, U), F.presheaf.germ U x hx ((show Γ(X, U) from i.app U r) • t) = 0 := by
  classical
  refine ⟨germ_smul_eq_zero_of_mem_range_stalk I F i x s, fun h => ?_⟩
  obtain ⟨U₀, hx₀, hU₀, t₀, ht₀⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
    X.isBasis_affineOpens F.presheaf x s
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  let : Module.Finite Γ(X, U.1) Γ(I, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections I hU₀
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' Γ(X, U.1) Γ(I, U.1)
  have hgens : ∀ k : Fin n, ∃ W : X.Opens, ∃ _ : x ∈ W, ∃ w : W ⟶ U.1,
      F.presheaf.map w.op
        ((show Γ(X, U.1) from i.app U.1 (q (Pi.single k 1))) • t₀) = 0 := by
    intro k
    obtain ⟨W, hxW, wU, _, heq⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx₀ (Set.mem_univ x) _
      (0 : Γ(F, ⊤)) (by simpa using h U.1 hx₀ t₀ ht₀ (q (Pi.single k 1)))
    exact ⟨W, hxW, wU, by simpa using heq⟩
  choose Wj hxWj wj hj using hgens
  let W : X.Opens := ⟨(U.1 : Set X) ∩ ⋂ k : Fin n, (Wj k : Set X),
    U.1.2.inter (isOpen_iInter_of_finite fun k => (Wj k).2)⟩
  have hxW : x ∈ W := ⟨hx₀, Set.mem_iInter.mpr hxWj⟩
  have hWU : W ≤ U.1 := fun y hy => hy.1
  have hWWj (k : Fin n) : W ≤ Wj k := fun y hy => (Set.mem_iInter.mp hy.2) k
  obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hx₀
  let vU : X.basicOpen f ⟶ U.1 := homOfLE (hfW.trans hWU)
  let tV : Γ(F, X.basicOpen f) := F.presheaf.map vU.op t₀
  have hgenV : ∀ k : Fin n,
      X.presheaf.map vU.op (show Γ(X, U.1) from i.app U.1 (q (Pi.single k 1))) • tV = 0 := by
    intro k
    let vk : X.basicOpen f ⟶ Wj k := homOfLE (hfW.trans (hWWj k))
    have hz := congrArg (F.presheaf.map vk.op) (hj k)
    rwa [map_zero, ← F.presheaf.map_comp_apply (wj k).op vk.op,
      show (wj k).op ≫ vk.op = vU.op from Subsingleton.elim _ _,
      Scheme.Modules.map_smul (M := F) vU] at hz
  have hmem : tV ∈ (annihilatorSubsheaf I F i).toSubmodule.obj (op (X.basicOpen f)) :=
    (mem_annihilatorSubsheaf_iff_of_isAffine I F i ⟨X.basicOpen f, U.2.basicOpen f⟩ tV).mpr
      (smul_eq_zero_of_restrict_basicOpen I F i U f tV
        (forall_restrict_smul_eq_zero I F i U.1 (X.basicOpen f) vU tV n q hq hgenV))
  refine ⟨(Scheme.Modules.presheaf (annihilatorSubsheaf I F i).toSheafOfModules).germ
    (X.basicOpen f) x hxf ⟨tV, hmem⟩, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (X.basicOpen f) x hxf
    (Scheme.Modules.Hom.mapPresheaf (annihilatorSubsheaf I F i).ι) ⟨tV, hmem⟩).trans ?_
  change F.presheaf.germ (X.basicOpen f) x hxf tV = s
  exact (TopCat.Presheaf.germ_res_apply F.presheaf vU x hxf t₀).trans ht₀

end AlgebraicGeometry

end
