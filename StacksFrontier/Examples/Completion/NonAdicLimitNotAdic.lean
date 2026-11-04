module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.Examples.Completion.NonAdicLimitSpecialization

/-!
# `gᵉ ∉ I·M`: the last clause of Stacks 0EH8

Let `A = k[x,y][[s,t]]/(xs − yt)`, `I = (s,t)`, `𝔞 = (x,y,s,t)`, `X = Spec(A) ∖ V(𝔞)` and
`M = lim H⁰(X, 𝒪_X/Iⁿ𝒪_X)`. The rational function `g = t/x = s/y` is regular on
`V = D(x) ∪ D(y) ⊇ V(I𝒪_X)`, each power `gᵉ` is an element of `M`, and `gᵉ → 0` in the limit
topology — all of which is in
`StacksFrontier/Examples/Completion/NonAdicLimitTopology.lean`. This file proves the remaining
clause, that `gᵉ` is nevertheless never in `I·M`, so that the limit topology is not the
`I`-adic one.

The source leaves this to a computation of `H⁰(U, ℱₙ)` that it omits. The proof here does not
compute `H⁰(U, ℱₙ)`. Instead it produces one `A`-semilinear functional on `H⁰(X, ℱₑ₊₁)` that
separates `gᵉ` from `I·M`, by specializing the whole situation along

`ρ : A ⟶ R[x,y]`, `x ↦ x`, `y ↦ y`, `s ↦ y·z`, `t ↦ x·z`, `R = k[T]/(Tᵉ⁺¹)`

(`Stacks.Examples.NonAdicLimit.exists_specialization`). Three things make this work.

* `ρ` carries `𝔞 = (x,y,s,t)` into `(x,y)`, so `Spec ρ` carries the punctured plane
  `W = D(x) ∪ D(y) ⊆ Spec R[x,y]` into `X`, giving a morphism of schemes `f : W ⟶ X`
  (`exists_schemeMorphism`).
* `ρ(I)^(e+1) = 0`, because `ρ(I) ⊆ (z)` and `zᵉ⁺¹ = 0`. So `f` kills `Iᵉ⁺¹𝒪_X` and factors
  through the `(e+1)`-st term `ℱₑ₊₁` of the quotient tower, by the universal property of the
  sheaf cokernel (`exists_quotientDescent`).
* `Γ(W, 𝒪) = R[x,y]`: the punctured plane acquires no new function
  (`Stacks.CoordinatePlane.bijective_sectionsPuncturedPlane`). This is where the example's
  `cd(A, I) = 2` enters — it is the codimension of the locus removed.

Composing, every formal section of `ℱₑ₊₁` has a value in `R[x,y]`, `A`-semilinearly over `ρ`.
On `gᵉ` that value is `zᵉ`, because `xᵉ·gᵉ = tᵉ` and `ρ(tᵉ) = xᵉzᵉ` with `xᵉ` regular. But a
decomposition `gᵉ = s·m₁ + t·m₂` would make it `y z·(…) + x z·(…)`, which vanishes at
`x = y = 0` while `zᵉ ≠ 0`.

## Main results

* `Stacks.Examples.NonAdicLimit.structureMapAt_coordX_mul_sectionG` — `x·g = t` on all of
  `V = D(x) ∪ D(y)`, not only on the chart `D(x)` where `g` is defined as `t/x`.
* `Stacks.Examples.NonAdicLimit.exists_schemeMorphism` — the morphism `f : W ⟶ X` induced by
  the specialization, with its effect on global sections.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! The scalar action on sections is declared over `X.ringCatSheaf.obj.obj U`, and instance
search cannot cross the `TopCat.Sheaf` definition to see that as `Γ(X, U)`. The bridges are the
`local instance`s of `Completion.IdealPowerQuasicoherent` and
`Completion.Quasicoherent.IdealPowerMultiple`, reactivated here rather than restated. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsModuleRingCatSheaf
  sectionsSMulCommClassΓ monoSubmoduleι sectionsModuleΓPresheaf

namespace Stacks.Examples.NonAdicLimit

variable (k : Type u) [Field k]

/-! ### `x·g = t` on all of `V = D(x) ∪ D(y)` -/

/-- **`x·g = t` on the chart `D(y)` as well.** On `D(y)` the section `g` is defined as `s/y`,
so what is immediate there is `y·g = s`; but `x·g = t` holds too, and this is exactly the
defining relation `xs = yt` of `A`: multiplying `x·g` by the unit `y` gives
`x·(y·g) = x·s = y·t`. -/
theorem structureMapAt_coordX_mul_sectionY :
    structureMapAt k ((puncturedSpectrum k).basicOpen (structureMap k (coordY k))) (coordX k) *
        sectionY k =
      structureMapAt k ((puncturedSpectrum k).basicOpen (structureMap k (coordY k)))
        (coordT k) := by
  refine (isUnit_structureMapAt_coordY k).mul_left_cancel ?_
  calc structureMapAt k _ (coordY k) * (structureMapAt k _ (coordX k) * sectionY k)
      = structureMapAt k _ (coordX k) * (structureMapAt k _ (coordY k) * sectionY k) := by
        ring
    _ = structureMapAt k _ (coordX k) * structureMapAt k _ (coordS k) := by
        rw [structureMapAt_coordY_mul_sectionY]
    _ = structureMapAt k _ (coordY k) * structureMapAt k _ (coordT k) := by
        rw [← map_mul, ← map_mul, coordX_mul_coordS]

/-- **`x·g = t` on `V = D(x) ∪ D(y)`.** The identity holds on each of the two charts — on
`D(x)` by the definition of `g` as `t/x`, on `D(y)` by
`structureMapAt_coordX_mul_sectionY` — hence on their union, since `𝒪_X` is a sheaf.

This is what lets the single global relation `xᵉ·gᵉ = tᵉ` be used below: without it `gᵉ` would
only be pinned down on `D(x)`. -/
theorem structureMapAt_coordX_mul_sectionG :
    structureMapAt k (nearVanishingOpen k).openSet (coordX k) * sectionG k =
      structureMapAt k (nearVanishingOpen k).openSet (coordT k) := by
  -- The two inclusions are taken as hypotheses, so that the restriction maps below are
  -- *written* with `(nearVanishingOpen k).openSet` as their source rather than with the
  -- supremum it unfolds to; otherwise the rewrites meet a goal that is only
  -- definitionally well typed.
  have hxle : (puncturedSpectrum k).basicOpen (structureMap k (coordX k)) ≤
      (nearVanishingOpen k).openSet := le_sup_left
  have hyle : (puncturedSpectrum k).basicOpen (structureMap k (coordY k)) ≤
      (nearVanishingOpen k).openSet := le_sup_right
  have hresX : (puncturedSpectrum k).presheaf.map (homOfLE hxle).op (sectionG k) =
      sectionX k := res_sectionG_basicOpenX k
  have hresY : (puncturedSpectrum k).presheaf.map (homOfLE hyle).op (sectionG k) =
      sectionY k := res_sectionG_basicOpenY k
  have h₁ : (puncturedSpectrum k).presheaf.map (homOfLE hxle).op
        (structureMapAt k (nearVanishingOpen k).openSet (coordX k) * sectionG k) =
      (puncturedSpectrum k).presheaf.map (homOfLE hxle).op
        (structureMapAt k (nearVanishingOpen k).openSet (coordT k)) := by
    rw [map_mul, structureMapAt_res, structureMapAt_res, hresX]
    exact structureMapAt_coordX_mul_sectionX k
  have h₂ : (puncturedSpectrum k).presheaf.map (homOfLE hyle).op
        (structureMapAt k (nearVanishingOpen k).openSet (coordX k) * sectionG k) =
      (puncturedSpectrum k).presheaf.map (homOfLE hyle).op
        (structureMapAt k (nearVanishingOpen k).openSet (coordT k)) := by
    rw [map_mul, structureMapAt_res, structureMapAt_res, hresY]
    exact structureMapAt_coordX_mul_sectionY k
  exact (puncturedSpectrum k).sheaf.eq_of_locally_eq₂ (homOfLE hxle) (homOfLE hyle)
    le_rfl _ _ h₁ h₂

/-! ### The morphism of schemes induced by the specialization -/

variable {R : Type u} [CommRing R]

/-- `D(xⁱ)` read on `Spec R[x,y]` is the basic open of the coordinate. -/
theorem basicOpen_planeCoord (i : Fin 2) :
    (Spec (CommRingCat.of (Stacks.CoordinatePlane.planeRing R))).basicOpen
        (Stacks.CoordinatePlane.planeCoord R i) =
      PrimeSpectrum.basicOpen (MvPolynomial.X i) :=
  AlgebraicGeometry.basicOpen_eq_of_affine _

/-- **The morphism of schemes `W ⟶ X` induced by the specialization.** Since `ρ` sends `x` and
`y` to the two coordinates of `R[x,y]`, the composite
`W ⟶ Spec R[x,y] ⟶ Spec A` misses `V(𝔞)`: a point of `W = D(x) ∪ D(y)` has one of the two
coordinates invertible, so its preimage ideal cannot contain all of `𝔞 = (x,y,s,t)`. The
morphism therefore lifts through the open immersion `X ⟶ Spec A`, and on global sections it is
`ρ` read through `Stacks.CoordinatePlane.sectionsPuncturedPlane`. -/
theorem exists_schemeMorphism (ρ : exampleRing k →+* Stacks.CoordinatePlane.planeRing R)
    (hx : ρ (coordX k) = MvPolynomial.X 0) (hy : ρ (coordY k) = MvPolynomial.X 1) :
    ∃ f : (Stacks.CoordinatePlane.puncturedPlane R).toScheme ⟶ puncturedSpectrum k,
      ∀ w, f.appTop (structureMap k w) =
        (Stacks.CoordinatePlane.sectionsPuncturedPlane R).hom (ρ w) := by
  have hrange : Set.range ((Stacks.CoordinatePlane.puncturedPlane R).ι ≫
      Spec.map (CommRingCat.ofHom ρ)) ⊆ Set.range (puncturedSpectrumOpens k).ι := by
    rintro p ⟨q, rfl⟩
    refine ⟨⟨((Stacks.CoordinatePlane.puncturedPlane R).ι ≫
      Spec.map (CommRingCat.ofHom ρ)) q, ?_⟩, rfl⟩
    change ¬ (puncturingIdeal k : Set (exampleRing k)) ⊆
      (PrimeSpectrum.comap ρ q.1).asIdeal
    intro hp
    have hqmem : q.1 ∈
        (Spec (CommRingCat.of (Stacks.CoordinatePlane.planeRing R))).basicOpen
            (Stacks.CoordinatePlane.planeCoord R 0) ⊔
          (Spec (CommRingCat.of (Stacks.CoordinatePlane.planeRing R))).basicOpen
            (Stacks.CoordinatePlane.planeCoord R 1) := q.2
    rw [TopologicalSpace.Opens.mem_sup, basicOpen_planeCoord, basicOpen_planeCoord] at hqmem
    have key : ∀ (i : Fin 2) (c : exampleRing k), c ∈ puncturingIdeal k →
        ρ c = MvPolynomial.X i → q.1 ∈ PrimeSpectrum.basicOpen (MvPolynomial.X i) → False :=
      fun i c hc hρc hq => (PrimeSpectrum.mem_basicOpen _ _).mp hq (by
        have hh := hp hc
        change ρ c ∈ q.1.asIdeal at hh
        rwa [hρc] at hh)
    rcases hqmem with hq | hq
    · exact key 0 (coordX k) (Ideal.subset_span (by simp)) hx hq
    · exact key 1 (coordY k) (Ideal.subset_span (by simp)) hy hq
  refine ⟨IsOpenImmersion.lift (puncturedSpectrumOpens k).ι _ hrange, fun w => ?_⟩
  have hfac := IsOpenImmersion.lift_fac (puncturedSpectrumOpens k).ι _ hrange
  have happ : (puncturedSpectrumOpens k).ι.appTop ≫
      (IsOpenImmersion.lift (puncturedSpectrumOpens k).ι _ hrange).appTop =
      (Spec.map (CommRingCat.ofHom ρ)).appTop ≫
        (Stacks.CoordinatePlane.puncturedPlane R).ι.appTop := by
    rw [← Scheme.Hom.comp_appTop, hfac]
    exact Scheme.Hom.comp_appTop _ _
  change ((Scheme.ΓSpecIso (CommRingCat.of (exampleRing k))).inv ≫
    (puncturedSpectrumOpens k).ι.appTop ≫
      (IsOpenImmersion.lift (puncturedSpectrumOpens k).ι _ hrange).appTop) w =
    (CommRingCat.ofHom ρ ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Stacks.CoordinatePlane.planeRing R))).inv ≫
        (Stacks.CoordinatePlane.puncturedPlane R).ι.appTop) w
  rw [happ, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-! ### Descending a morphism through the quotient by `Iⁿ`

These two lemmas are about an arbitrary scheme. Keeping them general is not only tidier: the
example's `puncturedSpectrum k` is a complement of a zero locus, and elaborating these
statements with it in place of `X` unfolds that description repeatedly and exhausts the
heartbeat limit. -/

section Descent

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) {F G : X.Modules}

/-- **A morphism killing `Iⁿ` affine-locally kills the subsheaf `Iⁿ F`.** The subsheaf is the
least one whose sections over every affine open contain `I(U)ⁿ·F(U)`, so the hypothesis is
exactly what its universal property
(`Stacks.Algebraization.idealPowerMultiple_le_iff`) asks for; the conclusion then follows
because a section of the subsheaf over any open is, sectionwise, in the kernel. -/
theorem ι_comp_eq_zero_of_affine (f : F ⟶ G)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ I.ideal U ^ n →
      ∀ m : Γ(F, U.1), f.app U.1 (r • m) = 0) :
    ((idealPowerMultiple I n F).ι :
        ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ F) ≫ f =
      (0 : ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ _) := by
  have hker := (idealPowerMultiple_le_iff I n F (kernelSubmodule f)).mpr fun U =>
    Submodule.smul_le.mpr fun r hr m _ =>
      (kernelSubmodule_toSubmodule_obj f (op U.1)).ge (LinearMap.mem_ker.mpr (h U r hr m))
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact (kernelSubmodule_toSubmodule_obj f (op V)).le
    (SheafOfModules.Submodule.le_iff.mp hker (op V) x.property)

/-- **The descent to `F/IⁿF` on sections.** Given that `f` kills `Iⁿ F`, the universal property
of the sheaf cokernel factors it through `F/IⁿF`; reading that factorization on sections over an
open `W` gives an additive map, linear over `Γ(X, W)`, which agrees with `f` on reductions. -/
theorem exists_descOfQuotient (f : F ⟶ G)
    (hz : ((idealPowerMultiple I n F).ι :
        ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ F) ≫ f =
      (0 : ((idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ _)) (W : X.Opens) :
    ∃ H : ToType Γ((adicQuotientSystem I F).obj (op n), W) →+ ToType Γ(G, W),
      (∀ (a : Γ(X, W)) w, H (a • w) = a • H w) ∧
      (∀ a, H ((adicProj I F (op n)).app W a) = f.app W a) := by
  have hψπ := cokernel.π_desc (C := X.Modules) (idealPowerMultiple I n F).ι f hz
  refine ⟨AddMonoidHom.mk' (fun w => ConcreteCategory.hom
      ((cokernel.desc (C := X.Modules) (idealPowerMultiple I n F).ι f hz).app W) w)
    (fun p q => map_add _ p q), fun a w => ?_, fun a => ?_⟩
  · exact Scheme.Modules.Hom.app_smul _ a w
  · exact congrArg (fun χ => ConcreteCategory.hom (Scheme.Modules.Hom.app χ W) a) hψπ

/-- **`Γ(f_* 𝒪_Y, ⊤) = Γ(Y, ⊤)`**, definitionally: the pushforward's sections over `⊤` are the
sections of `𝒪_Y` over `f ⁻¹ᵁ ⊤`, which is `⊤`.

Recorded as an `AddEquiv` so that the definitional identification — which is not cheap, since
it unfolds the preimage of `⊤` — is performed once, here, instead of inside every proof that
needs it. -/
def pushforwardUnitTopAddEquiv {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ToType Γ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf),
        (⊤ : X.Opens)) ≃+
      ToType Γ(Y, (⊤ : Y.Opens)) :=
  AddEquiv.refl _

end Descent

/-! ### Descending the specialization through the quotient tower -/

/-- The morphism of sheaves of modules on `X` induced by a morphism of schemes into `X`: the
unit module maps to the pushforward of the unit module of the source.

Naming it fixes its source as `formalModule k` rather than as the unfolded
`SheafOfModules.unit`; applying the descent above to the unfolded form forces an expensive
unification against the quotient tower. -/
def pushforwardStructure {Y : Scheme.{u}} (f : Y ⟶ puncturedSpectrum k) :
    formalModule k ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- On sections, `pushforwardStructure` is `f` itself. -/
theorem app_pushforwardStructure {Y : Scheme.{u}} (f : Y ⟶ puncturedSpectrum k)
    (U : (puncturedSpectrum k).Opens) (a : Γ(formalModule k, U)) :
    Scheme.Modules.Hom.app (pushforwardStructure k f) U a = f.app U a := rfl

/-- **A function killed by `f` kills the sections of `f_* 𝒪_W`.** The action of `r : Γ(X, U)` on
sections of the pushforward of the unit module is multiplication by `f r`. -/
theorem app_pushforwardStructure_smul_eq_zero {Y : Scheme.{u}} (f : Y ⟶ puncturedSpectrum k)
    (U : (puncturedSpectrum k).Opens) (r : Γ(puncturedSpectrum k, U)) (hr : f.app U r = 0)
    (m : Γ(formalModule k, U)) :
    Scheme.Modules.Hom.app (pushforwardStructure k f) U (r • m) = 0 := by
  rw [Scheme.Modules.Hom.app_smul, app_pushforwardStructure]
  change f.app U r * f.app U m = 0
  rw [hr, zero_mul]

/-- **The specialization descends to the `n`-th term of the quotient tower.** The morphism of
sheaves of modules `𝒪_X ⟶ f_* 𝒪_W` induced by a morphism of schemes `f : W ⟶ X` kills `Iⁿ𝒪_X`
as soon as `f` kills `Iⁿ` on every affine open, so it factors through `ℱₙ = 𝒪_X/Iⁿ𝒪_X`. On
global sections the factorization is an additive map `H`, semilinear over `f`, agreeing with
`f` on the reductions of global functions.

This is the step that replaces the source's omitted computation of `H⁰(U, ℱₙ)`: no description
of those sections is needed, only one map out of them. -/
theorem exists_quotientDescent {Y : Scheme.{u}} (n : ℕ) (f : Y ⟶ puncturedSpectrum k)
    (hf : ∀ (U : (puncturedSpectrum k).affineOpens) (r : Γ(puncturedSpectrum k, U.1)),
      r ∈ (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
        (puncturingIdeal k)).ideal U ^ n → f.app U.1 r = 0) :
    ∃ H : ToType Γ((adicQuotientSystem (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
          (puncturingIdeal k)) (formalModule k)).obj (op n),
        (⊤ : (puncturedSpectrum k).Opens)) →+ ToType Γ(Y, (⊤ : Y.Opens)),
      (∀ (a : Γ(puncturedSpectrum k, (⊤ : (puncturedSpectrum k).Opens))) w,
          H (a • w) = f.appTop a * H w) ∧
      (∀ a, H ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
        (puncturingIdeal k)) (formalModule k) (op n)).app ⊤ a) = f.appTop a) := by
  obtain ⟨H, hsmul, hproj⟩ := exists_descOfQuotient
    (idealSheafNearVanishing (exampleRing k) (adicIdeal k) (puncturingIdeal k)) n
    (pushforwardStructure k f)
    (ι_comp_eq_zero_of_affine _ n _ (fun U r hr m =>
      app_pushforwardStructure_smul_eq_zero k f U.1 r (hf U r hr) m)) ⊤
  refine ⟨(pushforwardUnitTopAddEquiv f).toAddMonoidHom.comp H, fun a w => ?_, fun a => ?_⟩
  · exact (congrArg (pushforwardUnitTopAddEquiv f) (hsmul a w)).trans rfl
  · exact (congrArg (pushforwardUnitTopAddEquiv f) (hproj a)).trans
      (app_pushforwardStructure k f ⊤ a)

/-! ### Reading `gᵉ` on the `(e+1)`-st term of the tower -/

/-- The `n`-th component of a formal section, as a section of `ℱₙ` over all of `X`. -/
def formalComponent (n : ℕ) :
    ToType (formalLimitModuleCat k) →+
      ToType Γ((adicQuotientSystem (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
        (puncturingIdeal k)) (formalModule k)).obj (op n),
        (⊤ : (puncturedSpectrum k).Opens)) :=
  (ConcreteCategory.hom (limit.π (formalSectionsModule (exampleRing k) (adicIdeal k)
    (puncturingIdeal k) (formalModule k)) (op n))).toAddMonoidHom

/-- `formalComponent k n` is the `n`-th limit projection of `formalSectionsModule`. -/
theorem formalComponent_apply (n : ℕ) (m : ToType (formalLimitModuleCat k)) :
    formalComponent k n m =
      ConcreteCategory.hom (limit.π (formalSectionsModule (exampleRing k) (adicIdeal k)
        (puncturingIdeal k) (formalModule k)) (op n)) m := rfl

/-- The components are `Γ(X, 𝒪_X)`-linear, being the projections of a limit of modules. -/
theorem formalComponent_smul (n : ℕ)
    (a : Γ(puncturedSpectrum k, (⊤ : (puncturedSpectrum k).Opens)))
    (m : ToType (formalLimitModuleCat k)) :
    formalComponent k n (a • m) = a • formalComponent k n m :=
  map_smul (ConcreteCategory.hom (limit.π (formalSectionsModule (exampleRing k) (adicIdeal k)
    (puncturingIdeal k) (formalModule k)) (op n))) a m

/-- Restriction of sections of `ℱₙ` from `X` to the neighbourhood `V = D(x) ∪ D(y)`. -/
def resFormalComponent (n : ℕ)
    (w : ToType Γ((adicQuotientSystem (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
      (puncturingIdeal k)) (formalModule k)).obj (op n), (⊤ : (puncturedSpectrum k).Opens))) :
    ToType Γ((adicQuotientSystem (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
      (puncturingIdeal k)) (formalModule k)).obj (op n), (nearVanishingOpen k).openSet) :=
  ((adicQuotientSystem (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
    (puncturingIdeal k)) (formalModule k)).obj (op n)).val.map
      (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op w

/-- `resFormalComponent` is the restriction isomorphism of Stacks 0EG2. -/
theorem resFormalComponent_eq (n : ℕ) (w) :
    resFormalComponent k n w =
      ConcreteCategory.hom (resNearVanishing (exampleRing k) (adicIdeal k) (puncturingIdeal k)
        (formalModule k) (nearVanishingOpen k) (op n)) w := rfl

/-- **Restriction to `V` is injective on `ℱₙ`.** `ℱₙ` is supported on the formal locus, which
`V` contains, so restriction there loses nothing — it is in fact an isomorphism, by
`Stacks.Algebraization.isIso_quotientSystemNearVanishing_res`. -/
theorem injective_resFormalComponent (n : ℕ) :
    Function.Injective (resFormalComponent k n) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (isIso_quotientSystemNearVanishing_res
    (exampleRing k) (adicIdeal k) (puncturingIdeal k) (formalModule k)
    (nearVanishingOpen k) n)).1

/-- **The restriction of `gᵉ`'s component to `V` is the reduction of `gᵉ`.** This is what the
comparison map of Stacks 0EG2 does: it extends the reduction of a section defined only near the
formal locus to all of `X`, by inverting the restriction isomorphism. -/
theorem resFormalComponent_formalSectionGModule (e : ℕ) :
    resFormalComponent k (e + 1) (formalComponent k (e + 1) (formalSectionGModule k e)) =
      ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
        (puncturingIdeal k)) (formalModule k) (op (e + 1))).app
          (nearVanishingOpen k).openSet) (sectionG k ^ e) := by
  have h1 : formalComponent k (e + 1) (formalSectionGModule k e) =
      ConcreteCategory.hom (limit.π (formalSections (exampleRing k) (adicIdeal k)
        (puncturingIdeal k) (formalModule k)) (op (e + 1))) (formalSectionG k e) :=
    π_ofFormalSections (exampleRing k) (adicIdeal k) (puncturingIdeal k) (formalModule k)
      (op (e + 1)) (formalSectionG k e)
  have h2 := ConcreteCategory.congr_hom
    (comparisonAt_π (exampleRing k) (adicIdeal k) (puncturingIdeal k) (formalModule k)
      (nearVanishingOpen k) (op (e + 1))) (sectionGFormal k e)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    show ConcreteCategory.hom (comparisonAt (exampleRing k) (adicIdeal k) (puncturingIdeal k)
        (formalModule k) (nearVanishingOpen k)) (sectionGFormal k e) = formalSectionG k e from
      rfl] at h2
  rw [resFormalComponent_eq, h1, h2, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
    ConcreteCategory.id_apply]
  rfl

/-- **`xᵉ·gᵉ` and `tᵉ` have the same reduction modulo `I^(e+1)`, over all of `X`.** The two
agree on `V = D(x) ∪ D(y)`, where `gᵉ` is defined and `x·g = t` holds
(`structureMapAt_coordX_mul_sectionG`), and restriction to `V` is injective on `ℱₑ₊₁`. This is
what turns the chart identity into a statement about the formal section `gᵉ ∈ M`. -/
theorem smul_pow_coordX_formalComponent (e : ℕ) :
    structureMap k (coordX k) ^ e • formalComponent k (e + 1) (formalSectionGModule k e) =
      ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
        (puncturingIdeal k)) (formalModule k) (op (e + 1))).app ⊤)
        (structureMap k (coordT k) ^ e) := by
  have hchart : (puncturedSpectrum k).presheaf.map
          (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
          (structureMap k (coordX k) ^ e) * sectionG k ^ e =
      (puncturedSpectrum k).presheaf.map
          (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
          (structureMap k (coordT k) ^ e) := by
    rw [map_pow, map_pow, ← mul_pow]
    congr 1
    exact structureMapAt_coordX_mul_sectionG k
  refine injective_resFormalComponent k (e + 1) ?_
  calc resFormalComponent k (e + 1)
        (structureMap k (coordX k) ^ e • formalComponent k (e + 1) (formalSectionGModule k e))
      = (puncturedSpectrum k).presheaf.map
              (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
              (structureMap k (coordX k) ^ e) •
            resFormalComponent k (e + 1)
              (formalComponent k (e + 1) (formalSectionGModule k e)) :=
        PresheafOfModules.map_smul _ _ _ _
    _ = (puncturedSpectrum k).presheaf.map
              (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
              (structureMap k (coordX k) ^ e) •
            ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k)
              (adicIdeal k) (puncturingIdeal k)) (formalModule k) (op (e + 1))).app
                (nearVanishingOpen k).openSet) (sectionG k ^ e) :=
        congrArg _ (resFormalComponent_formalSectionGModule k e)
    _ = ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
            (puncturingIdeal k)) (formalModule k) (op (e + 1))).app
              (nearVanishingOpen k).openSet)
            ((puncturedSpectrum k).presheaf.map
              (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
              (structureMap k (coordX k) ^ e) * sectionG k ^ e) :=
        (Scheme.Modules.Hom.app_smul _ _ _).symm
    _ = ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
            (puncturingIdeal k)) (formalModule k) (op (e + 1))).app
              (nearVanishingOpen k).openSet)
            ((puncturedSpectrum k).presheaf.map
              (homOfLE (le_top : (nearVanishingOpen k).openSet ≤ ⊤)).op
              (structureMap k (coordT k) ^ e)) :=
        congrArg _ hchart
    _ = resFormalComponent k (e + 1)
          (ConcreteCategory.hom ((adicProj (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
            (puncturingIdeal k)) (formalModule k) (op (e + 1))).app ⊤)
            (structureMap k (coordT k) ^ e)) :=
        PresheafOfModules.naturality_apply _ _ _

/-! ### The last clause: `gᵉ ∉ I·M` -/

/-- A member of `(r, s)·N` is `r·p + s·q` for some `p, q ∈ N`. -/
theorem exists_pair_of_mem_span_pair_smul_top {A N : Type*} [CommSemiring A]
    [AddCommMonoid N] [Module A N] {r s : A} {w : N}
    (hw : w ∈ Ideal.span {r, s} • (⊤ : Submodule A N)) :
    ∃ p q : N, r • p + s • q = w := by
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro t ht m _
    obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp ht
    exact ⟨p • m, q • m, by simp [add_smul, smul_smul, mul_comm]⟩
  · intro x y hx hy
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp [smul_add, add_add_add_comm]⟩

/-- Moving a factor across a ring equivalence. -/
theorem symm_apply_mul {A B : Type*} [CommRing A] [CommRing B] (j : A ≃+* B) (a : A) (b : B) :
    j.symm (j a * b) = a * j.symm b := by
  rw [map_mul, j.symm_apply_apply]

/-- **The specialization kills `I^n` once `zⁿ = 0`.** `ρ` sends both generators of `I` into the
ideal generated by `z`, so `ρ(I)ⁿ ⊆ (zⁿ) = 0`. -/
theorem map_adicIdeal_pow_eq_bot {R : Type u} [CommRing R]
    (ρ : exampleRing k →+* Stacks.CoordinatePlane.planeRing R) (z : R)
    (hs : ρ (coordS k) = MvPolynomial.X 1 * MvPolynomial.C z)
    (ht : ρ (coordT k) = MvPolynomial.X 0 * MvPolynomial.C z)
    (n : ℕ) (hz : z ^ n = 0) :
    Ideal.map ρ (adicIdeal k ^ n) = ⊥ := by
  have hI : Ideal.map ρ (adicIdeal k) ≤ Ideal.span {MvPolynomial.C z} := by
    rw [adicIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, Ideal.span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · rw [hs]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  refine le_bot_iff.mp ?_
  calc Ideal.map ρ (adicIdeal k ^ n) = Ideal.map ρ (adicIdeal k) ^ n := Ideal.map_pow _ _ _
    _ ≤ Ideal.span {MvPolynomial.C z} ^ n := pow_le_pow_left' hI _
    _ = ⊥ := by
        rw [Ideal.span_singleton_pow, ← map_pow, hz, map_zero, Ideal.span_singleton_zero]

/-- **The specialization kills `Iⁿ` on sections over every affine open.** On an affine open `U`
the ideal sheaf of `I·𝒪_X` is the image of `I` under `structureMapAt`
(`idealSheafNearVanishing_ideal_eq_map_structureMapAt`), and `f` carries that image to
`ρ(Iⁿ) = 0` by naturality. This is the hypothesis `exists_quotientDescent` asks for. -/
theorem app_eq_zero_of_mem_idealSheaf {R : Type u} [CommRing R]
    (ρ : exampleRing k →+* Stacks.CoordinatePlane.planeRing R) (n : ℕ)
    (hbot : Ideal.map ρ (adicIdeal k ^ n) = ⊥)
    (f : (Stacks.CoordinatePlane.puncturedPlane R).toScheme ⟶ puncturedSpectrum k)
    (hfapp : ∀ w, f.app (⊤ : (puncturedSpectrum k).Opens) (structureMap k w) =
      (Stacks.CoordinatePlane.sectionsPuncturedPlane R).hom (ρ w))
    (U : (puncturedSpectrum k).affineOpens) (r : Γ(puncturedSpectrum k, U.1))
    (hr : r ∈ (idealSheafNearVanishing (exampleRing k) (adicIdeal k)
      (puncturingIdeal k)).ideal U ^ n) :
    f.app U.1 r = 0 := by
  rw [idealSheafNearVanishing_ideal_eq_map_structureMapAt, ← Ideal.map_pow] at hr
  have hzero : ∀ w ∈ adicIdeal k ^ n, ρ w = 0 := fun w hw =>
    Ideal.mem_bot.mp (hbot ▸ Ideal.mem_map_of_mem ρ hw)
  have hker : Ideal.map (structureMapAt k U.1) (adicIdeal k ^ n) ≤
      RingHom.ker (f.app U.1).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    refine RingHom.mem_ker.mpr ?_
    have hnat := ConcreteCategory.congr_hom
      (f.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op) (structureMap k w)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfapp w, hzero w hw,
      map_zero] at hnat
    exact hnat.trans (map_zero _)
  exact hker hr

/-- **The functional that separates `gᵉ` from `I·M`.** Every formal section acquires a value in
`R[x,y]`, `A`-semilinearly over the specialization `ρ`, and on `gᵉ` that value is `zᵉ`.

The value exists because the specialization descends to `ℱₑ₊₁` (`exists_quotientDescent`, which
is where `ρ(I)ᵉ⁺¹ = 0` is used) and the punctured plane carries no function beyond the
polynomials (`Stacks.CoordinatePlane.sectionsPuncturedPlaneEquiv`). Its value on `gᵉ` is forced
by `xᵉ·gᵉ = tᵉ` (`smul_pow_coordX_formalComponent`): the value satisfies
`xᵉ·(value) = ρ(tᵉ) = xᵉzᵉ`, and `xᵉ` is regular.

`R` is kept abstract — only a ring with an element `z` whose `(e+1)`-st power annihilates
`ρ(I)ᵉ⁺¹` — so that the sections of the punctured plane over it stay opaque. Instantiated at
`k[T]/(Tᵉ⁺¹)` the same statement exhausts the heartbeat limit. -/
theorem exists_valueFunctional (e : ℕ) {R : Type u} [CommRing R] (z : R)
    (ρ : exampleRing k →+* Stacks.CoordinatePlane.planeRing R)
    (hρx : ρ (coordX k) = MvPolynomial.X 0) (hρy : ρ (coordY k) = MvPolynomial.X 1)
    (hρt : ρ (coordT k) = MvPolynomial.X 0 * MvPolynomial.C z)
    (hbot : Ideal.map ρ (adicIdeal k ^ (e + 1)) = ⊥) :
    ∃ Θ : ToType (formalLimitModuleCat k) →+ Stacks.CoordinatePlane.planeRing R,
      (∀ (r : exampleRing k) (m : ToType (formalLimitModuleCat k)),
        Θ (structureMap k r • m) = ρ r * Θ m) ∧
      Θ (formalSectionGModule k e) = MvPolynomial.C z ^ e := by
  obtain ⟨f, hfapp⟩ := exists_schemeMorphism k ρ hρx hρy
  have hfappTop : ∀ w, f.app (⊤ : (puncturedSpectrum k).Opens) (structureMap k w) =
      (Stacks.CoordinatePlane.sectionsPuncturedPlane R).hom (ρ w) := hfapp
  obtain ⟨H, hHsmul, hHproj⟩ := exists_quotientDescent k (e + 1) f
    (fun U r hr => app_eq_zero_of_mem_idealSheaf k ρ (e + 1) hbot f hfappTop U r hr)
  obtain ⟨j, hj⟩ : ∃ j : Stacks.CoordinatePlane.planeRing R ≃+*
      Γ((Stacks.CoordinatePlane.puncturedPlane R).toScheme,
        (⊤ : (Stacks.CoordinatePlane.puncturedPlane R).toScheme.Opens)),
      ∀ w, j w = (Stacks.CoordinatePlane.sectionsPuncturedPlane R).hom w :=
    ⟨Stacks.CoordinatePlane.sectionsPuncturedPlaneEquiv R, fun _ => rfl⟩
  have hfj : ∀ r, f.appTop (structureMap k r) = j (ρ r) :=
    fun r => (hfapp r).trans (hj (ρ r)).symm
  refine ⟨(AddMonoidHom.mk' (fun w => j.symm w) (fun a b => map_add j.symm a b)).comp
    (H.comp (formalComponent k (e + 1))), ?_, ?_⟩
  · intro r m
    change j.symm (H (formalComponent k (e + 1) (structureMap k r • m))) = _
    rw [formalComponent_smul, hHsmul, hfj r]
    exact symm_apply_mul j (ρ r) _
  · change j.symm (H (formalComponent k (e + 1) (formalSectionGModule k e))) = _
    refine (MvPolynomial.isRegular_X_pow (R := R) (n := (0 : Fin 2)) e).left ?_
    have hlhs : j.symm (H (structureMap k (coordX k) ^ e •
          formalComponent k (e + 1) (formalSectionGModule k e))) =
        MvPolynomial.X (0 : Fin 2) ^ e *
          j.symm (H (formalComponent k (e + 1) (formalSectionGModule k e))) := by
      rw [hHsmul, map_pow, hfj, hρx, ← map_pow j]
      exact symm_apply_mul j _ _
    have hrhs : j.symm (H (ConcreteCategory.hom ((adicProj (idealSheafNearVanishing
          (exampleRing k) (adicIdeal k) (puncturingIdeal k)) (formalModule k)
          (op (e + 1))).app ⊤) (structureMap k (coordT k) ^ e))) =
        (MvPolynomial.X 0 * MvPolynomial.C z : Stacks.CoordinatePlane.planeRing R) ^ e :=
      (congrArg j.symm (hHproj (structureMap k (coordT k) ^ e))).trans (by
        rw [map_pow, hfj, hρt, ← map_pow j, j.symm_apply_apply])
    have h1 := congrArg (fun w => j.symm (H w)) (smul_pow_coordX_formalComponent k e)
    refine (hlhs.symm.trans (h1.trans hrhs)).trans ?_
    rw [mul_pow]

/-- **`gᵉ ∉ I·M`, the last clause of Stacks 0EH8.** Each power of the rational function
`g = t/x = s/y` is a formal section tending to zero in the limit topology on
`M = lim H⁰(X, 𝒪_X/Iⁿ𝒪_X)`, and none of them lies in `I·M`. The limit topology is therefore
not the `I`-adic topology, which is what makes the example sharp against Stacks 0EH7.

The whole situation is specialized along `ρ : A ⟶ R[x,y]`, `x ↦ x`, `y ↦ y`, `s ↦ y·z`,
`t ↦ x·z` with `R = k[T]/(Tᵉ⁺¹)` and `z` the image of `T`. Since `ρ(𝔞) ⊆ (x,y)`, the punctured
plane `W = D(x) ∪ D(y) ⊆ Spec R[x,y]` maps to `X`; since `ρ(I)ᵉ⁺¹ = 0`, that map factors
through `ℱₑ₊₁`; and since `Γ(W, 𝒪) = R[x,y]` — the punctured plane acquires no new function,
which is where the codimension two of the removed locus enters — every formal section acquires
a value in `R[x,y]` (`exists_specializationFunctional`). On `gᵉ` the value is `zᵉ`, whereas a
decomposition `gᵉ = s·p + t·q` makes it `y z·(…) + x z·(…)`, which vanishes at `x = y = 0`
while `zᵉ ≠ 0`. -/
@[stacks 0EH8 "g^e is never in I*M, so the limit topology on M differs from the I-adic one and \
the cd = 1 hypothesis of Stacks 0EH7 is sharp"]
theorem notMemAdicIdealSmulFormalLimit (e : ℕ) : NotMemAdicIdealSmulFormalLimit k e := by
  change formalSectionGModule k e ∉ adicIdealSmulFormalLimit k
  intro hmem
  rw [adicIdealSmulFormalLimit_eq, adicIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton] at hmem
  obtain ⟨p, q, hpq⟩ := exists_pair_of_mem_span_pair_smul_top hmem
  obtain ⟨ρ, hρx, hρy, hρs, hρt⟩ := exists_specialization k
    ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial k) ^ (e + 1)})).comp
      Polynomial.C) (truncParam k e) (isNilpotent_truncParam k e)
  obtain ⟨Θ, hΘsmul, hΘG⟩ := exists_valueFunctional k e (truncParam k e) ρ hρx hρy hρt
    (map_adicIdeal_pow_eq_bot k ρ (truncParam k e) hρs hρt (e + 1) (truncParam_pow_succ k e))
  have hdecomp : MvPolynomial.C (truncParam k e) ^ e =
      ρ (coordS k) * Θ p + ρ (coordT k) * Θ q := by
    rw [← hΘG, ← hpq, map_add, hΘsmul, hΘsmul]
  have heval := congrArg (MvPolynomial.eval fun _ : Fin 2 => (0 : truncCoeff k e)) hdecomp
  rw [hρs, hρt] at heval
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, zero_mul,
    zero_add] at heval
  exact truncParam_pow_ne_zero k e heval

end Stacks.Examples.NonAdicLimit

end
