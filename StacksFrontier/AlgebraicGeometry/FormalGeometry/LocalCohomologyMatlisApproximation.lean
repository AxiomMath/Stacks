module

public import Mathlib.RingTheory.FiniteLength
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension

/-!
# Approximating a local cohomology system by a Matlis dual

Fix a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)` and
`U = X \ Z`, and assume `A` local with maximal ideal `𝔪 = 𝔞`. Let `(M_n)` be an inverse system
of finite `A`-modules which is a finite module model, so that `(M_n^~|_U)` is an object of
`Coh(U, I𝒪_U)`. If the local cohomology modules `H^i_𝔪(M_n)` are, compatibly with the
transition maps, the Matlis duals of a direct system `(G_n)` of finite `A`-modules annihilated
by powers of `I`, and that direct system is essentially constant modulo modules of finite
length, then the system `(H^i_𝔪(M_n))` is, up to modules of finite length, constant with value
the Matlis dual of one finite `A`-module annihilated by a power of `I`.

The dualization is carried out by elementary exactness properties of `Hom_A(-, E)` for an
injective hull `E` of the residue field: the Matlis dual of a module of finite length again has
finite length, and the kernel, image and cokernel of the dual of a map are the duals of the
cokernel, image and kernel of the map.

## Main definitions

* `Stacks.Algebraization.localCohomologySystem` — the inverse system `H^i_𝔪(M_n)`.
* `Stacks.Algebraization.MatlisDualModel` — a direct system of finite `A`-modules annihilated by
  powers of `I` whose Matlis duals are the terms of `localCohomologySystem`, compatibly with the
  transition maps.
* `Stacks.Algebraization.IsEssentiallyConstantModFiniteLength` — essential constancy of a direct
  system of modules in the quotient of the finite `A`-modules by the modules of finite length.

## Main results

* `Stacks.Algebraization.isFiniteLength_matlisDual` — the Matlis dual of a module of finite
  length has finite length.
* `Stacks.Algebraization.exists_matlisDual_approximation_localCohomologySystem` — the
  dualization, which is Stacks 0EHK with the essentially constant Matlis dual model as an
  explicit hypothesis.

## Implementation notes

"For `n ≫ 0`" is rendered by shifting the index: the approximating maps are given at the
indices `n₀ + n` for an unspecified `n₀` and all `n`, and "for `n'' ≫ n' ≫ 0`" becomes a
hypothesis which, for each `n'`, holds at all sufficiently large `n''`.

The cokernels of the maps `N → G_n` form a direct system `(Q_n)`, and the image of
`Q_m → Q_n` is the image of the composite `G_m → G_n → Q_n`; that composite is the form the
image condition takes here, so that no proof obligation has to be discharged inside the
statement.

The source's conclusion is reached from the model by applying `Hom_A(-, E)`. The hypotheses of
the source that are not used by the dualization — locality with `𝔪 = 𝔞`, the existence of a
dualizing complex, the `(s, s + d)`-inequalities and the bound `d ≥ cd(A, I)` — are the
hypotheses from which the model is produced in the source, and they are carried in the
statement even though the dualization does not consume them.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0DXT](https://stacks.math.columbia.edu/tag/0DXT), the module model.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
* [Stacks Project, Tag 08Z9](https://stacks.math.columbia.edu/tag/08Z9), Matlis duality.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Exactness of the Matlis dual -/

section MatlisDual

variable {A : Type u} [CommRing A] {E : Type u} [AddCommGroup E] [Module A E]
  {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

/-- For an injective module `E`, the image of the Matlis dual of a map is the submodule of dual
vectors annihilating its kernel. -/
public theorem range_lcomp_eq_ker_lcomp_subtype [Module.Injective A E] (u : X →ₗ[A] Y)
    (K : Submodule A X) (hK : K = LinearMap.ker u) :
    LinearMap.range (LinearMap.lcomp A E u) =
      LinearMap.ker (LinearMap.lcomp A E K.subtype) := by
  subst hK
  refine le_antisymm ?_ ?_
  · rintro h ⟨c, rfl⟩
    ext x
    have : u x.1 = 0 := x.2
    simp [this]
  · intro h hh
    have hle : LinearMap.ker u ≤ LinearMap.ker h := by
      intro x hx
      have := LinearMap.congr_fun hh ⟨x, hx⟩
      simpa using this
    set hbar := (LinearMap.ker u).liftQ h hle with hbardef
    set e := LinearMap.quotKerEquivRange u with hedef
    obtain ⟨c', hc'⟩ := Module.Injective.out (R := A) (Q := E)
      (LinearMap.range u).subtype (Submodule.injective_subtype _)
      (hbar ∘ₗ (e.symm : LinearMap.range u →ₗ[A] X ⧸ LinearMap.ker u))
    refine ⟨c', ?_⟩
    ext x
    have hx : e ((LinearMap.ker u).mkQ x) = ⟨u x, ⟨x, rfl⟩⟩ := rfl
    have h1 : c' (u x) = hbar (e.symm ⟨u x, ⟨x, rfl⟩⟩) := hc' ⟨u x, ⟨x, rfl⟩⟩
    rw [← hx, e.symm_apply_apply] at h1
    simpa [hbardef] using h1

/-- For an injective module `E` and maps `v : W → Y` and `g : X → Y`, the image under the Matlis
dual of `g` of the dual vectors annihilating the image of `v` is the Matlis dual of the image of
the composite `X → Y → Y ⧸ im(v)`. -/
public theorem map_lcomp_ker_lcomp_eq_range_lcomp [Module.Injective A E] {W : Type u}
    [AddCommGroup W] [Module A W] (v : W →ₗ[A] Y) (g : X →ₗ[A] Y) :
    Submodule.map (LinearMap.lcomp A E g) (LinearMap.ker (LinearMap.lcomp A E v)) =
      LinearMap.range
        (LinearMap.lcomp A E (((LinearMap.range v).mkQ ∘ₗ g).rangeRestrict)) := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨h, hh, rfl⟩
    have hle : LinearMap.range v ≤ LinearMap.ker h := by
      rintro - ⟨w, rfl⟩
      have := LinearMap.congr_fun hh w
      simpa using this
    refine ⟨(LinearMap.range v).liftQ h hle ∘ₗ
      (LinearMap.range ((LinearMap.range v).mkQ ∘ₗ g)).subtype, ?_⟩
    ext x
    simp
  · rintro - ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := Module.Injective.out (R := A) (Q := E)
      (LinearMap.range ((LinearMap.range v).mkQ ∘ₗ g)).subtype
      (Submodule.injective_subtype _) c
    refine ⟨c' ∘ₗ (LinearMap.range v).mkQ, ?_, ?_⟩
    · ext w
      have hz : (LinearMap.range v).mkQ (v w) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, rfl⟩
      simpa using congrArg c' hz
    · ext x
      exact hc' ⟨((LinearMap.range v).mkQ ∘ₗ g) x, ⟨x, rfl⟩⟩

/-- For a surjection `f`, the image of its Matlis dual is isomorphic to the Matlis dual of the
target, so one has finite length if and only if the other has. -/
private theorem isFiniteLength_range_lcomp_iff {f : X →ₗ[A] Y} (hf : Function.Surjective f) :
    IsFiniteLength A (LinearMap.range (LinearMap.lcomp A E f)) ↔
      IsFiniteLength A (Y →ₗ[A] E) :=
  have e := LinearEquiv.ofInjective (LinearMap.lcomp A E f)
    (LinearMap.lcomp_injective_of_surjective f hf)
  ⟨e.symm.isFiniteLength, e.isFiniteLength⟩

/-- If the kernel `K` of `u` has Matlis dual of finite length, then the cokernel of the Matlis
dual of `u` has finite length. -/
private theorem isFiniteLength_quotient_range_lcomp [Module.Injective A E] (u : X →ₗ[A] Y)
    (K : Submodule A X) (hK : K = LinearMap.ker u) (h : IsFiniteLength A (K →ₗ[A] E)) :
    IsFiniteLength A ((X →ₗ[A] E) ⧸ LinearMap.range (LinearMap.lcomp A E u)) := by
  rw [range_lcomp_eq_ker_lcomp_subtype u K hK]
  exact (LinearMap.quotKerEquivRange (LinearMap.lcomp A E K.subtype)).symm.isFiniteLength
    (IsFiniteLength.of_injective h (Submodule.injective_subtype _))

end MatlisDual

/-! ### The Matlis dual of a module of finite length -/

section FiniteLength

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (E : Type u) [AddCommGroup E] [Module A E]

/-- The socle of an injective hull of the residue field has finite length. -/
private theorem isFiniteLength_socle
    (i : IsLocalRing.ResidueField A →ₗ[A] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i)) :
    IsFiniteLength A
      (Submodule.torsionBySet A E (IsLocalRing.maximalIdeal A : Set A)) := by
  have hE : IsArtinian A E :=
    Dualizing.isArtinian_of_isInjectiveHull_residueField A E (ModuleCat.ofHom i) hi
  have hsocle : Dualizing.HasFiniteSocle A E :=
    ((Dualizing.isArtinian_iff_powerTorsion_and_finiteSocle A E).mp hE).2
  set T := Submodule.torsionBySet A E (IsLocalRing.maximalIdeal A : Set A) with hT
  have hTt : Module.IsTorsionBySet A T (IsLocalRing.maximalIdeal A : Set A) :=
    Submodule.torsionBySet_isTorsionBySet _
  let : Module (IsLocalRing.ResidueField A) T := hTt.module
  let : IsScalarTower A (IsLocalRing.ResidueField A) T := hTt.isScalarTower
  have : Module.Finite (IsLocalRing.ResidueField A) T := hsocle
  have : Module.Finite A (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (Submodule.mkQ (IsLocalRing.maximalIdeal A))
      (Submodule.mkQ_surjective _)
  have : Module.Finite A T := Module.Finite.trans (IsLocalRing.ResidueField A) T
  have : IsArtinian A E := hE
  have : IsArtinian A T := inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The Matlis dual of a simple module has finite length. -/
private theorem isFiniteLength_matlisDual_of_isSimpleModule
    (i : IsLocalRing.ResidueField A →ₗ[A] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i))
    (X : Type u) [AddCommGroup X] [Module A X] [IsSimpleModule A X] :
    IsFiniteLength A (X →ₗ[A] E) := by
  have hE : IsArtinian A E :=
    Dualizing.isArtinian_of_isInjectiveHull_residueField A E (ModuleCat.ofHom i) hi
  obtain ⟨J, hJ, ⟨eX⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have hJm : J = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hJ
  subst hJm
  set m := IsLocalRing.maximalIdeal A with hm
  set T := Submodule.torsionBySet A E (m : Set A) with hT
  -- evaluation at the class of `1`
  set ev : ((A ⧸ m) →ₗ[A] E) →ₗ[A] E :=
    { toFun := fun h => h (m.mkQ 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hev
  have hsmul : ∀ a : A, m.mkQ a = a • m.mkQ 1 := by
    intro a
    rw [← LinearMap.map_smul]
    simp
  have hevapp : ∀ h : (A ⧸ m) →ₗ[A] E, ev h = h (m.mkQ 1) := fun _ => rfl
  have hevinj : Function.Injective ev := by
    intro h h' hh
    refine LinearMap.ext fun y => ?_
    obtain ⟨a, rfl⟩ := m.mkQ_surjective y
    rw [hsmul a, map_smul, map_smul]
    rw [hevapp h, hevapp h'] at hh
    exact congrArg (fun z => a • z) hh
  have hmem : ∀ h : (A ⧸ m) →ₗ[A] E, ev h ∈ T := by
    intro h
    rw [hT, Submodule.mem_torsionBySet_iff]
    intro a
    have hz : m.mkQ (a : A) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr a.2
    have hstep : (a : A) • ev h = h (m.mkQ (a : A)) := by
      rw [hsmul (a : A), map_smul, hevapp h]
    rw [hstep, hz, map_zero]
  set ev' : ((A ⧸ m) →ₗ[A] E) →ₗ[A] T :=
    { toFun := fun h => ⟨ev h, hmem h⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hev'
  have hev'inj : Function.Injective ev' := by
    intro h h' hh
    exact hevinj (congrArg Subtype.val hh)
  have hFLT : IsFiniteLength A T := isFiniteLength_socle A E i hi
  obtain ⟨hTn, hTa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hFLT
  have hquot : IsFiniteLength A ((A ⧸ m) →ₗ[A] E) := by
    have hn : IsNoetherian A ((A ⧸ m) →ₗ[A] E) := by
      have := hTn
      exact isNoetherian_of_injective ev' hev'inj
    have ha : IsArtinian A ((A ⧸ m) →ₗ[A] E) := by
      have := hE
      exact isArtinian_of_injective ev hevinj
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hn, ha⟩
  exact (LinearEquiv.arrowCongr eX (LinearEquiv.refl A E)).symm.isFiniteLength hquot

/-- **The Matlis dual of a module of finite length has finite length.** Here `E` is an injective
hull of the residue field of the Noetherian local ring `A`. -/
public theorem isFiniteLength_matlisDual
    (i : IsLocalRing.ResidueField A →ₗ[A] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i))
    {X : Type u} [AddCommGroup X] [Module A X] (hX : IsFiniteLength A X) :
    IsFiniteLength A (X →ₗ[A] E) := by
  have : CategoryTheory.Injective (ModuleCat.of A E) := hi.1
  have : Module.Injective A E := Module.injective_module_of_injective_object A E
  induction hX with
  | @of_subsingleton P _ _ _ =>
    have : Subsingleton (P →ₗ[A] E) :=
      ⟨fun f g => by ext x; rw [Subsingleton.elim x 0]; simp⟩
    exact IsFiniteLength.of_subsingleton
  | @of_simple_quotient P _ _ Q _ _ ih =>
    set V := LinearMap.range (LinearMap.lcomp A E Q.mkQ) with hV
    have h1 : IsFiniteLength A V :=
      (isFiniteLength_range_lcomp_iff Q.mkQ_surjective).mpr
        (isFiniteLength_matlisDual_of_isSimpleModule A E i hi (P ⧸ Q))
    have h2 : IsFiniteLength A ((P →ₗ[A] E) ⧸ V) :=
      isFiniteLength_quotient_range_lcomp Q.mkQ Q (Submodule.ker_mkQ Q).symm ih
    obtain ⟨hn1, ha1⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h1
    obtain ⟨hn2, ha2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h2
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨(isNoetherian_iff_submodule_quotient V).mpr ⟨hn1, hn2⟩,
        (isArtinian_iff_submodule_quotient V).mpr ⟨ha1, ha2⟩⟩

/-- **A module whose Matlis dual has finite length has finite length.** Here `E` is an injective
hull of the residue field of the Noetherian local ring `A`. This is the converse of
`Stacks.Algebraization.isFiniteLength_matlisDual`.

The biduality map `X → Hom_A(Hom_A(X, E), E)` is injective because `E` is a cogenerator of the
category of `A`-modules: a nonzero `x` spans a submodule `A x ≅ A/I` with `I ≠ A`, hence with
the residue field as a quotient because `A` is local, and `E` receives the residue field through
a monomorphism and is injective, so a functional nonzero at `x` exists and extends to `X`. The
target of the biduality map has finite length by the forward direction, and finite length passes
to submodules. -/
public theorem isFiniteLength_of_isFiniteLength_matlisDual
    (i : IsLocalRing.ResidueField A →ₗ[A] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i))
    {X : Type u} [AddCommGroup X] [Module A X] (hX : IsFiniteLength A (X →ₗ[A] E)) :
    IsFiniteLength A X := by
  have hobj : CategoryTheory.Injective (ModuleCat.of A E) := hi.1
  have hinjE : Module.Injective A E := Module.injective_module_of_injective_object A E
  have hiinj : Function.Injective i :=
    (ModuleCat.mono_iff_injective (ModuleCat.ofHom i)).mp inferInstance
  have hcog : ∀ x : X, x ≠ 0 → ∃ φ : X →ₗ[A] E, φ x ≠ 0 := by
    intro x hx
    set g : A →ₗ[A] X := LinearMap.toSpanSingleton A X x with hg
    have hgx : g 1 = x := by simp [hg]
    have hkertop : LinearMap.ker g ≠ ⊤ := fun h =>
      hx (hgx.symm.trans (LinearMap.mem_ker.mp (h ▸ Submodule.mem_top)))
    set j : A →ₗ[A] E := i ∘ₗ Algebra.linearMap A (IsLocalRing.ResidueField A) with hj
    have hle : LinearMap.ker g ≤ LinearMap.ker j := by
      intro r hr
      have hz : algebraMap A (IsLocalRing.ResidueField A) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (IsLocalRing.le_maximalIdeal hkertop hr)
      show i (algebraMap A (IsLocalRing.ResidueField A) r) = 0
      rw [hz, map_zero]
    obtain ⟨φ, hφ⟩ := Module.Injective.out (R := A) (Q := E)
      (LinearMap.range g).subtype (Submodule.injective_subtype _)
      (((LinearMap.ker g).liftQ j hle) ∘ₗ
        (g.quotKerEquivRange.symm : LinearMap.range g →ₗ[A] A ⧸ LinearMap.ker g))
    refine ⟨φ, ?_⟩
    have h := hφ ⟨g 1, LinearMap.mem_range_self g 1⟩
    change φ (g 1) = ((LinearMap.ker g).liftQ j hle)
      (g.quotKerEquivRange.symm ⟨g 1, LinearMap.mem_range_self g 1⟩) at h
    rw [LinearMap.quotKerEquivRange_symm_apply_image] at h
    change φ (g 1) = j 1 at h
    rw [hgx] at h
    rw [h]
    show i (algebraMap A (IsLocalRing.ResidueField A) 1) ≠ 0
    rw [map_one]
    exact fun h0 => one_ne_zero (hiinj (h0.trans (map_zero i).symm))
  set D : X →ₗ[A] ((X →ₗ[A] E) →ₗ[A] E) :=
    { toFun := fun x =>
        { toFun := fun φ => φ x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := fun x y => LinearMap.ext fun φ => φ.map_add x y
      map_smul' := fun a x => LinearMap.ext fun φ => φ.map_smul a x } with hD
  have hDinj : Function.Injective D := by
    intro x y hxy
    by_contra hne
    obtain ⟨φ, hφ⟩ := hcog (x - y) (sub_ne_zero.mpr hne)
    refine hφ ?_
    have h : D x φ = D y φ := by rw [hxy]
    rw [map_sub]
    exact sub_eq_zero.mpr h
  exact IsFiniteLength.of_injective (isFiniteLength_matlisDual A E i hi hX) hDinj

/-- **The image of the Matlis dual of a map has finite length only if the image of the map
has.** For an injective hull `E` of the residue field of the Noetherian local ring `A` and an
`A`-linear map `u : X → Y`, the image of `Hom_A(Y, E) → Hom_A(X, E)` is the Matlis dual of the
image of `u`: the map factors as the surjection `X → im(u)` followed by the inclusion
`im(u) → Y`, the dual of the inclusion is surjective because `E` is injective, and the dual of
the surjection is injective. So finite length of that image is finite length of
`Hom_A(im(u), E)`, which by
`Stacks.Algebraization.isFiniteLength_of_isFiniteLength_matlisDual` is finite length of
`im(u)`. -/
public theorem isFiniteLength_range_of_isFiniteLength_range_lcomp
    (i : IsLocalRing.ResidueField A →ₗ[A] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i))
    {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (u : X →ₗ[A] Y)
    (h : IsFiniteLength A (LinearMap.range (LinearMap.lcomp A E u))) :
    IsFiniteLength A (LinearMap.range u) := by
  have hobj : CategoryTheory.Injective (ModuleCat.of A E) := hi.1
  have hinjE : Module.Injective A E := Module.injective_module_of_injective_object A E
  have hsurj : Function.Surjective (LinearMap.lcomp A E (LinearMap.range u).subtype) := by
    intro ψ
    obtain ⟨φ, hφ⟩ := Module.Injective.out (R := A) (Q := E)
      (LinearMap.range u).subtype (Submodule.injective_subtype _) ψ
    exact ⟨φ, LinearMap.ext fun x => hφ x⟩
  have hfactor : LinearMap.lcomp A E u =
      (LinearMap.lcomp A E u.rangeRestrict) ∘ₗ
        LinearMap.lcomp A E (LinearMap.range u).subtype :=
    LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  rw [hfactor, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top] at h
  exact isFiniteLength_of_isFiniteLength_matlisDual A E i hi
    ((isFiniteLength_range_lcomp_iff u.surjective_rangeRestrict).mp h)

end FiniteLength

/-! ### The local cohomology system and its dual models -/

/-- The inverse system `H^i_𝔪(M_n)` of local cohomology modules, in degree `i` and with support
in the maximal ideal, of an inverse system `(M_n)` of modules over the local ring of an
algebraization situation. -/
public abbrev localCohomologySystem (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (i : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
  M ⋙ _root_.Stacks.LocalCohomology.localCohomologyModuleFunctor S.A i

/-- A *Matlis dual model* in degree `i` of an inverse system `(M_n)` of modules over the local
ring of an algebraization situation: a direct system `(G_n)` of finite `A`-modules annihilated
by powers of `I` together with identifications of `H^i_𝔪(M_n)` with the Matlis duals
`Hom_A(G_n, E)`, compatible with the transition maps on both sides. Local duality identifies
`Hom_A(H^i_𝔪(M_n), E)` with the completion of `Ext^{-i}_A(M_n, ω_A^∙)` for a normalized
dualizing complex `ω_A^∙`, and Matlis duality turns that into such a model. -/
public structure MatlisDualModel (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (E : Type u) [AddCommGroup E] [Module S.A E] (i : ℤ) where
  /-- The direct system of finite modules. -/
  G : ℕ ⥤ ModuleCat.{u} S.A
  /-- Each term is a finite `A`-module. -/
  finite : ∀ n, Module.Finite S.A (G.obj n)
  /-- Each term is annihilated by a power of `I`. -/
  annihilated : ∀ n, ∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A (G.obj n)) = ⊥
  /-- The identification of `H^i_𝔪(M_n)` with the Matlis dual of `G_n`. -/
  dualEquiv : ∀ n : ℕ, (localCohomologySystem S M i).obj (op n) ≃ₗ[S.A] (G.obj n →ₗ[S.A] E)
  /-- The identifications are compatible with the transition maps. -/
  dualEquiv_comp : ∀ (m n : ℕ) (h : m ≤ n) (x : (localCohomologySystem S M i).obj (op n)),
    dualEquiv m (((localCohomologySystem S M i).map (homOfLE h).op).hom x) =
      (dualEquiv n x).comp (G.map (homOfLE h)).hom

/-- A direct system `(G_n)` of `A`-modules is *essentially constant modulo finite length* when
there is a finite `A`-module `N` annihilated by a power of `I` and, for `n ≫ 0`, compatible
maps `N → G_n` whose kernels have finite length and whose cokernels `Q_n` form a system in
which the image of `Q_m → Q_n` has finite length for `n ≫ m ≫ 0`. This is essential constancy
of `(G_n)` in the quotient of the category of finite `A`-modules by the Serre subcategory of
modules of finite length. -/
public def IsEssentiallyConstantModFiniteLength (A : Type u) [CommRing A] (I : Ideal A)
    (G : ℕ ⥤ ModuleCat.{u} A) : Prop :=
  ∃ (N : ModuleCat.{u} A) (n₀ : ℕ) (α : ∀ n : ℕ, N →ₗ[A] G.obj (n₀ + n)),
    Module.Finite A N ∧
    (∃ k : ℕ, I ^ k • (⊤ : Submodule A N) = ⊥) ∧
    (∀ (m n : ℕ) (h : m ≤ n),
      (G.map (homOfLE (Nat.add_le_add_left h n₀))).hom ∘ₗ α m = α n) ∧
    (∀ n : ℕ, IsFiniteLength A (LinearMap.ker (α n))) ∧
    (∀ m : ℕ, ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      IsFiniteLength A
        (LinearMap.range ((LinearMap.range (α n)).mkQ ∘ₗ
          (G.map (homOfLE (Nat.add_le_add_left hmn n₀))).hom)))

/-! ### The dualization -/

/-- **Stacks Project, Tag 0EHK.** In the situation of Stacks 0EHC, let `(M_n)` be an inverse
system of `A`-modules as in Stacks 0DXT and let `(ℱ_n)` be the corresponding object of
`Coh(U, I𝒪_U)`. Let `d ≥ cd(A, I)` and `s ≥ 0` be integers, assume that `A` is local with
maximal ideal `𝔪 = 𝔞`, that `A` has a dualizing complex, and that `(ℱ_n)` satisfies the
`(s, s + d)`-inequalities. Let `E` be an injective hull of the residue field of `A`. Then for
`i ≤ s` there is a finite `A`-module `N` annihilated by a power of `I` and, for `n ≫ 0`,
compatible maps `H^i_𝔪(M_n) → Hom_A(N, E)` whose cokernels have finite length and whose kernels
`K_n` form an inverse system in which the image of `K_{n''} → K_{n'}` has finite length for
`n'' ≫ n' ≫ 0`.

The existence of an essentially constant Matlis dual model of the local cohomology system is an
explicit hypothesis: in the source it is the system of the modules `Ext^{-i}_A(M_n, ω_A^∙)` for
a normalized dualizing complex, identified with the Matlis duals of the local cohomology modules
by local duality (Stacks 0AAK) and Matlis duality (Stacks 08Z9). This library proves local
duality only objectwise, with no naturality in the module
(`Dualizing.LocalDuality.nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology`),
and its Matlis biduality isomorphism
(`Dualizing.isIso_matlisEvaluation_of_isArtinian`) assumes `A` adically complete, so the model
cannot be produced here; the essential constancy of that system is the substance of the proof in
the source. -/
@[stacks 0EHK "the dualization; the essentially constant Matlis dual model of the local
cohomology system, which local duality 0AAK and Matlis duality 08Z9 supply in the source, is an
explicit hypothesis"]
public theorem exists_matlisDual_approximation_localCohomologySystem
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M) (d s : ℤ)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    (ιE : IsLocalRing.ResidueField S.A →ₗ[S.A] E) [Mono (ModuleCat.ofHom ιE)]
    (hιE : Module.IsInjectiveHull (ModuleCat.ofHom ιE))
    (_hmaximal : IsLocalRing.maximalIdeal S.A = S.a)
    (_hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (_hineq : SatisfiesDepthInequalities S
      (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (_hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (_hs : 0 ≤ s)
    (hmodel : ∀ i : ℤ, i ≤ s → ∃ D : MatlisDualModel S M E i,
      IsEssentiallyConstantModFiniteLength S.A S.I D.G) :
    ∀ i : ℤ, i ≤ s →
      ∃ (N : ModuleCat.{u} S.A) (n₀ : ℕ)
        (φ : ∀ n : ℕ,
          (localCohomologySystem S M i).obj (op (n₀ + n)) →ₗ[S.A] (N →ₗ[S.A] E)),
        Module.Finite S.A N ∧
        (∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A N) = ⊥) ∧
        (∀ (m n : ℕ) (h : m ≤ n),
          φ m ∘ₗ ((localCohomologySystem S M i).map
            (homOfLE (Nat.add_le_add_left h n₀)).op).hom = φ n) ∧
        (∀ n : ℕ, IsFiniteLength S.A ((N →ₗ[S.A] E) ⧸ LinearMap.range (φ n))) ∧
        (∀ m : ℕ, ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
          IsFiniteLength S.A
            (Submodule.map ((localCohomologySystem S M i).map
              (homOfLE (Nat.add_le_add_left hmn n₀)).op).hom (LinearMap.ker (φ n)))) := by
  have : CategoryTheory.Injective (ModuleCat.of S.A E) := hιE.1
  have : Module.Injective S.A E := Module.injective_module_of_injective_object S.A E
  intro i hi
  obtain ⟨D, N, n₀, α, hNfin, hNann, hαcomp, hker, himg⟩ := hmodel i hi
  refine ⟨N, n₀, fun n =>
    LinearMap.lcomp S.A E (α n) ∘ₗ (D.dualEquiv (n₀ + n)).toLinearMap,
    hNfin, hNann, ?_, ?_, ?_⟩
  · intro m n h
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have hcomp := D.dualEquiv_comp (n₀ + m) (n₀ + n) (Nat.add_le_add_left h n₀) x
    have hα := LinearMap.congr_fun (hαcomp m n h) y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.lcomp_apply] at hα ⊢
    rw [hcomp, LinearMap.comp_apply, hα]
  · intro n
    have hrange : LinearMap.range
        (LinearMap.lcomp S.A E (α n) ∘ₗ (D.dualEquiv (n₀ + n)).toLinearMap) =
          LinearMap.range (LinearMap.lcomp S.A E (α n)) :=
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (D.dualEquiv (n₀ + n)).surjective)
    rw [hrange]
    exact isFiniteLength_quotient_range_lcomp (α n) _ rfl
      (isFiniteLength_matlisDual S.A E ιE hιE (hker n))
  · intro m
    obtain ⟨k, hk⟩ := himg m
    refine ⟨k, fun n hmn hkn => ?_⟩
    set g := (D.G.map (homOfLE (Nat.add_le_add_left hmn n₀))).hom with hg
    set t := ((localCohomologySystem S M i).map
      (homOfLE (Nat.add_le_add_left hmn n₀)).op).hom with ht
    have hsub : ∀ y ∈ Submodule.map t (LinearMap.ker
        (LinearMap.lcomp S.A E (α n) ∘ₗ (D.dualEquiv (n₀ + n)).toLinearMap)),
        D.dualEquiv (n₀ + m) y ∈
          Submodule.map (LinearMap.lcomp S.A E g)
            (LinearMap.ker (LinearMap.lcomp S.A E (α n))) := by
      rintro - ⟨x, hx, rfl⟩
      refine ⟨D.dualEquiv (n₀ + n) x, ?_, ?_⟩
      · simpa using hx
      · exact (D.dualEquiv_comp (n₀ + m) (n₀ + n) (Nat.add_le_add_left hmn n₀) x).symm
    have hfl : IsFiniteLength S.A
        (Submodule.map (LinearMap.lcomp S.A E g)
          (LinearMap.ker (LinearMap.lcomp S.A E (α n)))) := by
      rw [map_lcomp_ker_lcomp_eq_range_lcomp (E := E) (α n) g]
      exact (isFiniteLength_range_lcomp_iff (LinearMap.surjective_rangeRestrict _)).mpr
        (isFiniteLength_matlisDual S.A E ιE hιE (hk n hmn hkn))
    refine IsFiniteLength.of_injective (f := ?_) hfl ?_
    · exact
      { toFun := fun y => ⟨D.dualEquiv (n₀ + m) y.1, hsub y.1 y.2⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    · intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext ((D.dualEquiv (n₀ + m)).injective this)

end Stacks.Algebraization

end
