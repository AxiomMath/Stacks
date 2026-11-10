module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.EffaceabilityInput

/-!
# Effaceability of the Čech δ-functor

`StacksDraft.Ch20.Sec13.Tag01ENEffaceable` reduces the first input of Stacks 01EN to
`DeltaFunctor.Effaceable` for the Čech δ-functor of a covering, and leaves that hypothesis
undischarged. This file discharges it, for a space and a presheaf of rings whose module
universe is the one the Čech construction of Tag 01EJ fixes, namely `Type 0`.

## The argument

The effaceability asked for by `CechEffaceable.effaceable_of_exists_mono` is weaker than the
vanishing of the higher Čech cohomology of injective presheaves of modules: it suffices to
embed each presheaf of `R`-modules in *some* presheaf whose higher Čech cohomology vanishes,
and the target may depend on the object. The *Godement presheaf*

`(god R M)(V) = ∏_{W ≤ V} M(W)`

does the job, and needs neither injective objects nor the Hom-complex presentation of the Čech
complex (Stacks 01EL and 01EM).

* It receives a monomorphism from `M`, namely `godUnit`, sending a section over `V` to the
  family of its restrictions: the component indexed by `V` itself is the identity.
* Its Čech complex is contractible in positive degrees. Indeed the degree-`p` Čech cochains of
  `god R M` are `∏_σ ∏_{W ≤ U_σ} M(W)`, and the Čech differential acts on the component
  indexed by an open `W` purely by reindexing tuples — no restriction map of `M` intervenes,
  because every component is a section over the same `W`. Any `W` occurring there satisfies
  `W ≤ U_{σ 0}`, so a member `U_t` of the covering containing `W` can be chosen once and for
  all; prepending `t` to the tuple is then a contracting homotopy `homotopyMap`, the usual one
  for the cochain complex of a nonempty simplex. The identity `homotopyMap_id` holds in every
  positive degree, whence exactness there by `exact_of_id_eq`.

## Main results

* `god`, `godUnit`, `mono_godUnit`: the Godement presheaf of `M` and its embedding of `M`.
* `homotopyMap`, `homotopyMap_id`: the contracting homotopy of the Čech complex of the
  Godement presheaf, and the identity it satisfies in positive degrees.
* `isZero_cechCohomology_god`: the higher Čech cohomology of the Godement presheaf vanishes.
* `effaceable_cechDeltaFunctor`: **the `Effaceable` instance**, the input Stacks 01EN was
  missing, and `isUniversal_cechDeltaFunctor`, the universality of Stacks 010T that follows.

## Implementation notes

`cechIsLimit` records that the degree-`p` Čech cochain module of a presheaf is a product of the
Čech factors evaluated at it: the Čech cochains of Tag 01EJ are a product of *functors*, and
limits in a functor category are computed pointwise. It supplies the `lift` used to build the
homotopy and the extensionality used to verify the homotopy identity.

Sections of Čech cochains are read off by `cechCoeff`, and by `cechVal`, which extends
`cechCoeff` by zero outside its domain of definition so that the alternating sums can be
rearranged without carrying inclusion proofs.

What Stacks 01EN still lacks after this file is its third input: a δ-functor whose components
are the right derived functors of degree-zero Čech cohomology. Mathlib has no long exact
sequence for `Functor.rightDerived`, so that is carried as a hypothesis by
`Stacks.Cohomology.CechDerivedFull.cechDeltaIsoRightDerivedOfIso₀`; the tag is therefore not
attached here.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 01EL](https://stacks.math.columbia.edu/tag/01EL)
* [Stacks Project, Tag 01EM](https://stacks.math.columbia.edu/tag/01EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechDerived

universe r

namespace Stacks.Cohomology.CechGodement

section Godement

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{r})

/-- The restriction ring homomorphism `R(V) ⟶ R(W)` attached to an inclusion `W ≤ V`. -/
def resRing {V W : Opens Y} (h : W ≤ V) : R.obj (op V) →+* R.obj (op W) :=
  (R.map (homOfLE h).op).hom

/-- Restricting a scalar twice is restricting it once, along the composite inclusion. -/
theorem resRing_resRing {V W Z : Opens Y} (h : W ≤ V) (h' : Z ≤ W) (x : R.obj (op V)) :
    resRing R h' (resRing R h x) = resRing R (h'.trans h) x := by
  have e : (homOfLE h).op ≫ (homOfLE h').op = (homOfLE (h'.trans h)).op := rfl
  rw [resRing, resRing, resRing, ← e, R.map_comp]
  rfl

variable (M : PresheafOfModules.{0} R)

/-- The sections of the Godement presheaf of `M` over `V`: a family of sections of `M`, one
over each open contained in `V`. -/
def GodSections (V : (Opens Y)ᵒᵖ) : Type :=
  ∀ W : {W : Opens Y // W ≤ V.unop}, M.obj (op W.1)

/-- Godement sections are added componentwise. -/
instance (V : (Opens Y)ᵒᵖ) : AddCommGroup (GodSections R M V) :=
  inferInstanceAs (AddCommGroup (∀ W : {W : Opens Y // W ≤ V.unop}, M.obj (op W.1)))

/-- The `R(V)`-module structure on `GodSections R M V`: a scalar acts on the component indexed
by `W` through the restriction `R(V) → R(W)`. -/
instance (V : (Opens Y)ᵒᵖ) : Module (R.obj V) (GodSections R M V) where
  smul r x := fun W ↦ resRing R W.2 r • x W
  one_smul x := by
    funext W
    change resRing R W.2 1 • x W = x W
    simp
  mul_smul r s x := by
    funext W
    change resRing R W.2 (r * s) • x W = resRing R W.2 r • resRing R W.2 s • x W
    rw [map_mul, mul_smul]
  smul_zero r := by
    funext W
    change resRing R W.2 r • (0 : M.obj (op W.1)) = 0
    rw [smul_zero]
  smul_add r x y := by
    funext W
    change resRing R W.2 r • (x W + y W) = resRing R W.2 r • x W + resRing R W.2 r • y W
    rw [smul_add]
  add_smul r s x := by
    funext W
    change resRing R W.2 (r + s) • x W = resRing R W.2 r • x W + resRing R W.2 s • x W
    rw [map_add, add_smul]
  zero_smul x := by
    funext W
    change resRing R W.2 0 • x W = 0
    rw [map_zero, zero_smul]

/-- The value of the Godement presheaf of `M` at `V`, as an `R(V)`-module. -/
def godObj (V : (Opens Y)ᵒᵖ) : ModuleCat.{0} (R.obj V) :=
  ModuleCat.of _ (GodSections R M V)

/-- A scalar `r` of `R(V)` acts on the component of a Godement section indexed by `W` through
its restriction to `R(W)`. -/
@[simp]
theorem godObj_smul_apply {V : (Opens Y)ᵒᵖ} (r : R.obj V) (x : godObj R M V)
    (W : {W : Opens Y // W ≤ V.unop}) : (r • x) W = resRing R W.2 r • x W :=
  rfl

/-- **The Godement presheaf of `M`.** Its sections over `V` are the families `(x_W)_{W ≤ V}`
with `x_W` a section of `M` over `W`; restriction along `V' ≤ V` forgets the components indexed
by the opens that are not contained in `V'`. -/
def god : PresheafOfModules.{0} R where
  obj V := godObj R M V
  map {V V'} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (godObj R M V'))
      { toFun := fun x W ↦ x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          funext W
          change resRing R (W.2.trans (leOfHom f.unop)) r • x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
              = resRing R W.2 ((R.map f).hom r) • x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
          rw [show (R.map f).hom = resRing R (leOfHom f.unop) from rfl, resRing_resRing] }

/-- Sections of the Godement presheaf over `V` are families of sections of `M`. -/
theorem god_obj (V : (Opens Y)ᵒᵖ) : (god R M).obj V = godObj R M V :=
  rfl

/-- Restriction in the Godement presheaf drops the components outside the smaller open. -/
@[simp]
theorem god_map_apply {V V' : (Opens Y)ᵒᵖ} (f : V ⟶ V') (x : (god R M).obj V)
    (W : {W : Opens Y // W ≤ V'.unop}) :
    (god R M).map f x W = x ⟨W.1, W.2.trans (leOfHom f.unop)⟩ :=
  rfl

/-- Restriction along the identity inclusion is the identity on sections. -/
theorem map_le_rfl_apply {V : Opens Y} (x : M.obj (op V)) :
    M.map (homOfLE (le_refl V)).op x = x := by
  change M.map (𝟙 (op V)) x = x
  rw [M.map_id]
  rfl

/-- **The Godement embedding of `M`.** A section of `M` over `V` is sent to the family of its
restrictions to the opens contained in `V`. -/
def godUnit : M ⟶ god R M where
  app V := ModuleCat.ofHom
    { toFun := fun x W ↦ M.map (homOfLE W.2).op x
      map_add' := fun x y ↦ by funext W; exact map_add _ x y
      map_smul' := fun r x ↦ by funext W; exact M.map_smul (homOfLE W.2).op r x }
  naturality {V V'} f := by
    ext x
    funext W
    exact (M.map_comp_apply f (homOfLE W.2).op x).symm

/-- The components of the Godement embedding are the restriction maps of `M`. -/
@[simp]
theorem godUnit_app_apply {V : (Opens Y)ᵒᵖ} (x : M.obj V)
    (W : {W : Opens Y // W ≤ V.unop}) :
    (godUnit R M).app V x W = M.map (homOfLE W.2).op x :=
  rfl

/-- **The Godement embedding is a monomorphism.** Its component indexed by `V` itself is
restriction along the identity, hence the identity on sections over `V`. -/
instance mono_godUnit : Mono (godUnit R M) := by
  apply PresheafOfModules.mono_of_injective
  intro V x y h
  have h' := congrFun h ⟨V.unop, le_rfl⟩
  rw [godUnit_app_apply, godUnit_app_apply, map_le_rfl_apply, map_le_rfl_apply] at h'
  exact h'

end Godement

section SplitExact

variable {C : Type*} [Category C] [Abelian C]

/-- **A short complex whose identity splits through its two maps is exact.** If
`u ≫ f + g ≫ v = 𝟙 X₂` for some `u : X₂ ⟶ X₁` and `v : X₃ ⟶ X₂`, then `X₁ → X₂ → X₃` is
exact: the canonical map `X₁ ⟶ cycles` has `iCycles ≫ u` as a section, hence is an
epimorphism. This is the form in which a contracting homotopy produces exactness. -/
theorem exact_of_id_eq (S : ShortComplex C) (u : S.X₂ ⟶ S.X₁) (v : S.X₃ ⟶ S.X₂)
    (h : u ≫ S.f + S.g ≫ v = 𝟙 S.X₂) : S.Exact := by
  have hu : S.iCycles ≫ u ≫ S.f = S.iCycles := by
    have := congrArg (fun φ ↦ S.iCycles ≫ φ) h
    simp only [Preadditive.comp_add, Category.comp_id] at this
    rw [← Category.assoc S.iCycles S.g v, S.iCycles_g, Limits.zero_comp, add_zero] at this
    exact this
  have key : (S.iCycles ≫ u) ≫ S.toCycles = 𝟙 S.cycles := by
    rw [← cancel_mono S.iCycles, Category.assoc, S.toCycles_i, Category.id_comp,
      Category.assoc, hu]
  rw [ShortComplex.exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles := IsSplitEpi.mk' ⟨S.iCycles ≫ u, key⟩
  infer_instance

end SplitExact

section CechProduct

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{r}) (𝒰 : CechOpenCover Y)
  (N : PresheafOfModules.{0} R)

/-- Evaluating the discrete diagram of the degree-`p` Čech factors at `N` is the discrete
diagram of their values at `N`. -/
def cechDiagramIso (p : ℕ) :
    (Discrete.functor fun σ : Fin (p + 1) → 𝒰.ι ↦ cechTermFunctor R 𝒰 p σ) ⋙
        (evaluation (PresheafOfModules.{0} R) (ModuleCat.{0} (R.obj (op 𝒰.U)))).obj N ≅
      Discrete.functor fun σ : Fin (p + 1) → 𝒰.ι ↦ (cechTermFunctor R 𝒰 p σ).obj N :=
  Discrete.natIso fun _ ↦ Iso.refl _

/-- **The degree-`p` Čech cochain module of `N` is a product of the Čech factors at `N`.**
The degree-`p` Čech cochains are a product of functors, and limits in a functor category are
computed pointwise, so evaluating at `N` leaves a product of modules with the Čech projections
as its projections. -/
def cechIsLimit (p : ℕ) :
    IsLimit (Fan.mk ((cechObj R 𝒰 p).obj N)
      fun σ : Fin (p + 1) → 𝒰.ι ↦ (cechπ R 𝒰 p σ).app N) := by
  have h := (IsLimit.postcomposeHomEquiv (cechDiagramIso R 𝒰 N p)
      (((evaluation (PresheafOfModules.{0} R) (ModuleCat.{0} (R.obj (op 𝒰.U)))).obj N).mapCone
        (limit.cone (Discrete.functor fun σ : Fin (p + 1) → 𝒰.ι ↦ cechTermFunctor R 𝒰 p σ)))).symm
      (isLimitOfPreserves _ (limit.isLimit _))
  exact IsLimit.ofIsoLimit h
    (Cone.ext (Iso.refl _) (by rintro ⟨σ⟩; exact (Category.id_comp _).symm))

/-- A morphism into the degree-`p` Čech cochains of `N` is determined by its components. -/
theorem cech_hom_ext_app {p : ℕ} {Z : ModuleCat.{0} (R.obj (op 𝒰.U))}
    {f g : Z ⟶ (cechObj R 𝒰 p).obj N}
    (h : ∀ σ, f ≫ (cechπ R 𝒰 p σ).app N = g ≫ (cechπ R 𝒰 p σ).app N) : f = g :=
  (cechIsLimit R 𝒰 N p).hom_ext (by rintro ⟨σ⟩; simpa using h σ)

/-- The morphism into the degree-`p` Čech cochains of `N` with prescribed components. -/
def cechLiftApp {p : ℕ} {Z : ModuleCat.{0} (R.obj (op 𝒰.U))}
    (φ : ∀ σ : Fin (p + 1) → 𝒰.ι, Z ⟶ (cechTermFunctor R 𝒰 p σ).obj N) :
    Z ⟶ (cechObj R 𝒰 p).obj N :=
  (cechIsLimit R 𝒰 N p).lift (Fan.mk Z φ)

/-- The components of `cechLiftApp` are the prescribed ones. -/
@[reassoc (attr := simp)]
theorem cechLiftApp_π {p : ℕ} {Z : ModuleCat.{0} (R.obj (op 𝒰.U))}
    (φ : ∀ σ : Fin (p + 1) → 𝒰.ι, Z ⟶ (cechTermFunctor R 𝒰 p σ).obj N)
    (σ : Fin (p + 1) → 𝒰.ι) :
    cechLiftApp R 𝒰 N φ ≫ (cechπ R 𝒰 p σ).app N = φ σ := by
  simpa [cechLiftApp] using (cechIsLimit R 𝒰 N p).fac (Fan.mk Z φ) ⟨σ⟩

/-- **The Čech differential.** In degree `p` it is the alternating sum of the reindexings along
the coface maps of the simplex category, by construction of the Čech complex as the alternating
coface map complex of the Čech cosimplicial object. -/
theorem cechComplex_d (p : ℕ) :
    ((cechComplexFunctor R 𝒰).obj N).d p (p + 1) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (cechMap R 𝒰 (SimplexCategory.δ i).toOrderHom).app N :=
  CochainComplex.of_d (fun n ↦ (cechObj R 𝒰 n).obj N)
    (fun n ↦ ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (cechMap R 𝒰 (SimplexCategory.δ i).toOrderHom).app N) p

end CechProduct

section Homotopy

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{r}) (𝒰 : CechOpenCover Y)

/-- A chosen member of the covering containing `W`, for an open `W` that is contained in one. -/
def coverIdx (W : Opens Y) (hW : ∃ i, W ≤ 𝒰.obj i) : 𝒰.ι := hW.choose

/-- The chosen member of the covering does contain `W`. -/
theorem le_coverIdx (W : Opens Y) (hW : ∃ i, W ≤ 𝒰.obj i) : W ≤ 𝒰.obj (coverIdx 𝒰 W hW) :=
  hW.choose_spec

/-- An open contained in an intersection of members of the covering is contained in a member:
the tuple indexing the intersection is nonempty. -/
theorem exists_le_of_le_cechInter {p : ℕ} {σ : Fin (p + 1) → 𝒰.ι} {W : Opens Y}
    (h : W ≤ cechInter 𝒰 p σ) : ∃ i, W ≤ 𝒰.obj i :=
  ⟨σ 0, h.trans (iInf_le _ 0)⟩

/-- Prepending an index to a tuple does not enlarge the intersection beyond an open contained
both in the intersection of the tuple and in the member prepended. -/
theorem le_cechInter_cons {p : ℕ} (t : 𝒰.ι) (σ : Fin (p + 1) → 𝒰.ι) {W : Opens Y}
    (ht : W ≤ 𝒰.obj t) (hσ : W ≤ cechInter 𝒰 p σ) :
    W ≤ cechInter 𝒰 (p + 1) (Fin.cons t σ) := by
  simp only [cechInter, le_iInf_iff]
  refine Fin.cases ?_ ?_
  · simpa using ht
  · intro j
    simpa using hσ.trans (iInf_le (fun k ↦ 𝒰.obj (σ k)) j)

variable (M : PresheafOfModules.{0} R)

/-- The index prepended to the tuple `σ` for the component of the Godement sections indexed by
the open `W`: a chosen member of the covering containing `W`, which exists because `W` is
contained in the intersection indexed by `σ`. -/
def homIdx {p : ℕ} (σ : Fin (p + 1) → 𝒰.ι) (W : {W : Opens Y // W ≤ cechInter 𝒰 p σ}) : 𝒰.ι :=
  coverIdx 𝒰 W.1 (exists_le_of_le_cechInter 𝒰 W.2)

/-- `W` is contained in the intersection indexed by the tuple `σ` with `homIdx 𝒰 σ W`
prepended. -/
theorem le_cechInter_homCons {p : ℕ} (σ : Fin (p + 1) → 𝒰.ι)
    (W : {W : Opens Y // W ≤ cechInter 𝒰 p σ}) :
    W.1 ≤ cechInter 𝒰 (p + 1) (Fin.cons (homIdx 𝒰 σ W) σ) :=
  le_cechInter_cons 𝒰 _ σ (le_coverIdx 𝒰 W.1 (exists_le_of_le_cechInter 𝒰 W.2)) W.2

/-- Scalars from `R(U)` act on the Godement sections over a Čech intersection through the
restriction to the open indexing the component. -/
theorem cechTerm_god_smul_apply {p : ℕ} (σ : Fin (p + 1) → 𝒰.ι) (r : R.obj (op 𝒰.U))
    (y : (cechTermFunctor R 𝒰 p σ).obj (god R M))
    (W : {W : Opens Y // W ≤ cechInter 𝒰 p σ}) :
    (r • y) W = resRing R (W.2.trans (cechInter_le_U 𝒰 p σ)) r • y W := by
  change resRing R W.2 ((cechRestMap R 𝒰 p σ).hom r) • y W = _
  rw [show (cechRestMap R 𝒰 p σ).hom = resRing R (cechInter_le_U 𝒰 p σ) from rfl,
    resRing_resRing]

section ModuleCatApply

variable {S : Type*} [Ring S] {A B : ModuleCat.{0} S}

/-- A sum of morphisms of modules acts as the sum of their actions. -/
theorem moduleCat_sum_apply {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  simp [ModuleCat.hom_sum, LinearMap.sum_apply]

end ModuleCatApply

/-- The section over `W` of the component at the tuple `τ` of a degree-`q` Čech cochain of the
Godement presheaf of `M`. -/
def cechCoeff {q : ℕ} (c : (cechObj R 𝒰 q).obj (god R M)) (τ : Fin (q + 1) → 𝒰.ι)
    {W : Opens Y} (h : W ≤ cechInter 𝒰 q τ) : M.obj (op W) :=
  (cechπ R 𝒰 q τ).app (god R M) c ⟨W, h⟩

/-- Sections of Čech cochains are additive. -/
theorem cechCoeff_add {q : ℕ} (c c' : (cechObj R 𝒰 q).obj (god R M)) (τ : Fin (q + 1) → 𝒰.ι)
    {W : Opens Y} (h : W ≤ cechInter 𝒰 q τ) :
    cechCoeff R 𝒰 M (c + c') τ h = cechCoeff R 𝒰 M c τ h + cechCoeff R 𝒰 M c' τ h :=
  congrFun (map_add ((cechπ R 𝒰 q τ).app (god R M)).hom c c') ⟨W, h⟩

/-- Sections of Čech cochains are semilinear: a scalar from `R(U)` acts on the section over `W`
through its restriction to `W`. -/
theorem cechCoeff_smul {q : ℕ} (r : R.obj (op 𝒰.U)) (c : (cechObj R 𝒰 q).obj (god R M))
    (τ : Fin (q + 1) → 𝒰.ι) {W : Opens Y} (h : W ≤ cechInter 𝒰 q τ) :
    cechCoeff R 𝒰 M (r • c) τ h =
      resRing R (h.trans (cechInter_le_U 𝒰 q τ)) r • cechCoeff R 𝒰 M c τ h :=
  (congrFun (map_smul ((cechπ R 𝒰 q τ).app (god R M)).hom r c) ⟨W, h⟩).trans
    (cechTerm_god_smul_apply R 𝒰 M τ r _ ⟨W, h⟩)

/-- Sections of Čech cochains commute with integer scalars. -/
theorem cechCoeff_zsmul {q : ℕ} (n : ℤ) (c : (cechObj R 𝒰 q).obj (god R M))
    (τ : Fin (q + 1) → 𝒰.ι) {W : Opens Y} (h : W ≤ cechInter 𝒰 q τ) :
    cechCoeff R 𝒰 M (n • c) τ h = n • cechCoeff R 𝒰 M c τ h :=
  congrFun (map_zsmul ((cechπ R 𝒰 q τ).app (god R M)).hom n c) ⟨W, h⟩

/-- Sections of Čech cochains commute with finite sums. -/
theorem cechCoeff_sum {q : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → (cechObj R 𝒰 q).obj (god R M)) (τ : Fin (q + 1) → 𝒰.ι)
    {W : Opens Y} (h : W ≤ cechInter 𝒰 q τ) :
    cechCoeff R 𝒰 M (∑ i ∈ s, c i) τ h = ∑ i ∈ s, cechCoeff R 𝒰 M (c i) τ h :=
  (congrFun (map_sum ((cechπ R 𝒰 q τ).app (god R M)).hom c s) ⟨W, h⟩).trans
    (Finset.sum_apply _ _ _)

/-- Two morphisms into the degree-`q` Čech cochains of the Godement presheaf agree as soon as
all sections of all their components agree. -/
theorem cech_god_hom_ext {q : ℕ} {Z : ModuleCat.{0} (R.obj (op 𝒰.U))}
    {f g : Z ⟶ (cechObj R 𝒰 q).obj (god R M)}
    (h : ∀ (z : Z) (τ : Fin (q + 1) → 𝒰.ι) (W : Opens Y) (hW : W ≤ cechInter 𝒰 q τ),
      cechCoeff R 𝒰 M (f z) τ hW = cechCoeff R 𝒰 M (g z) τ hW) : f = g := by
  refine cech_hom_ext_app R 𝒰 (god R M) fun τ ↦ ?_
  ext z
  refine funext fun W ↦ ?_
  exact h z τ W.1 W.2

/-- Reindexing a Čech cochain along a map of tuples reads off the component at the reindexed
tuple. -/
theorem cechCoeff_cechMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → 𝒰.ι)
    (c : (cechObj R 𝒰 m).obj (god R M)) {W : Opens Y} (h : W ≤ cechInter 𝒰 n τ) :
    cechCoeff R 𝒰 M ((cechMap R 𝒰 f).app (god R M) c) τ h =
      cechCoeff R 𝒰 M c (τ ∘ f) (h.trans (cechInter_le_comp 𝒰 τ f)) :=
  congrFun (ConcreteCategory.congr_hom
    (NatTrans.congr_app (cechMap_comp_π R 𝒰 f τ) (god R M)) c) ⟨W, h⟩

/-- The Čech differential of the Godement presheaf, written with the Čech cochain modules
themselves as source and target. -/
def godD (p : ℕ) :
    (cechObj R 𝒰 p).obj (god R M) ⟶ (cechObj R 𝒰 (p + 1)).obj (god R M) :=
  ((cechComplexFunctor R 𝒰).obj (god R M)).d p (p + 1)

/-- **The sections of the Čech differential.** The section over `W` of the component at `τ` of
`d c` is the alternating sum, over the coface maps, of the sections over `W` of the components
of `c` at the faces of `τ`. -/
theorem cechCoeff_d (q : ℕ) (c : (cechObj R 𝒰 q).obj (god R M)) (τ : Fin (q + 2) → 𝒰.ι)
    {W : Opens Y} (h : W ≤ cechInter 𝒰 (q + 1) τ) :
    cechCoeff R 𝒰 M (godD R 𝒰 M q c) τ h =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechCoeff R 𝒰 M c (τ ∘ (SimplexCategory.δ i).toOrderHom)
          (h.trans (cechInter_le_comp 𝒰 τ _)) := by
  have hc : godD R 𝒰 M q c =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        (cechMap R 𝒰 (SimplexCategory.δ i).toOrderHom).app (god R M) c :=
    (ConcreteCategory.congr_hom (cechComplex_d R 𝒰 (god R M) q) c).trans
      (moduleCat_sum_apply _ _ c)
  rw [hc, cechCoeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cechCoeff_zsmul, cechCoeff_cechMap]

/-- **The degree-`p` component of the contracting homotopy.** The section over `W` of the value
at the tuple `σ` is the section over `W` of the value at `σ` with `homIdx 𝒰 σ W` prepended. -/
def homCompFun (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) (c : (cechObj R 𝒰 (p + 1)).obj (god R M)) :
    (cechTermFunctor R 𝒰 p σ).obj (god R M) :=
  fun W ↦ cechCoeff R 𝒰 M c (Fin.cons (homIdx 𝒰 σ W) σ) (le_cechInter_homCons 𝒰 σ W)

/-- The degree-`p` homotopy component, as a morphism of `R(U)`-modules. -/
def homComp (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    (cechObj R 𝒰 (p + 1)).obj (god R M) ⟶ (cechTermFunctor R 𝒰 p σ).obj (god R M) :=
  ConcreteCategory.ofHom
    { toFun := homCompFun R 𝒰 M p σ
      map_add' := fun c c' ↦ by
        funext W
        exact cechCoeff_add R 𝒰 M c c' _ (le_cechInter_homCons 𝒰 σ W)
      map_smul' := fun r c ↦ by
        funext W
        exact (cechCoeff_smul R 𝒰 M r c (Fin.cons (homIdx 𝒰 σ W) σ)
            (le_cechInter_homCons 𝒰 σ W)).trans
          (cechTerm_god_smul_apply R 𝒰 M σ r (homCompFun R 𝒰 M p σ c) W).symm }

/-- **The contracting homotopy of the Čech complex of the Godement presheaf.** -/
def homotopyMap (p : ℕ) :
    (cechObj R 𝒰 (p + 1)).obj (god R M) ⟶ (cechObj R 𝒰 p).obj (god R M) :=
  cechLiftApp R 𝒰 (god R M) (homComp R 𝒰 M p)

/-- **The sections of the contracting homotopy.** -/
theorem cechCoeff_homotopyMap (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι)
    (c : (cechObj R 𝒰 (p + 1)).obj (god R M)) {W : Opens Y} (h : W ≤ cechInter 𝒰 p σ)
    (hW : ∃ i, W ≤ 𝒰.obj i) :
    cechCoeff R 𝒰 M (homotopyMap R 𝒰 M p c) σ h =
      cechCoeff R 𝒰 M c (Fin.cons (coverIdx 𝒰 W hW) σ)
        (le_cechInter_cons 𝒰 _ σ (le_coverIdx 𝒰 W hW) h) :=
  congrFun (ConcreteCategory.congr_hom
    (cechLiftApp_π R 𝒰 (god R M) (homComp R 𝒰 M p) σ) c) ⟨W, h⟩

open scoped Classical in
/-- The section over `W` of the component at `τ`, extended by zero when `W` is not contained in
the intersection indexed by `τ`. This makes it a function of the tuple alone, so that the
alternating sums below can be rearranged without carrying inclusion proofs. -/
def cechVal {q : ℕ} (c : (cechObj R 𝒰 q).obj (god R M)) (W : Opens Y)
    (τ : Fin (q + 1) → 𝒰.ι) : M.obj (op W) :=
  if h : W ≤ cechInter 𝒰 q τ then cechCoeff R 𝒰 M c τ h else 0

/-- Where the inclusion holds, `cechVal` is the section. -/
theorem cechVal_eq {q : ℕ} (c : (cechObj R 𝒰 q).obj (god R M)) (W : Opens Y)
    (τ : Fin (q + 1) → 𝒰.ι) (h : W ≤ cechInter 𝒰 q τ) :
    cechVal R 𝒰 M c W τ = cechCoeff R 𝒰 M c τ h := by
  unfold cechVal
  split_ifs
  rfl

/-- `cechVal` is additive in the cochain. -/
theorem cechVal_add {q : ℕ} (c c' : (cechObj R 𝒰 q).obj (god R M)) (W : Opens Y)
    (τ : Fin (q + 1) → 𝒰.ι) :
    cechVal R 𝒰 M (c + c') W τ = cechVal R 𝒰 M c W τ + cechVal R 𝒰 M c' W τ := by
  unfold cechVal
  split_ifs with h
  · exact cechCoeff_add R 𝒰 M c c' τ h
  · exact (add_zero 0).symm

/-- Two morphisms into the degree-`q` Čech cochains of the Godement presheaf agree as soon as
all the sections of all their components agree. -/
theorem cech_god_hom_ext' {q : ℕ} {Z : ModuleCat.{0} (R.obj (op 𝒰.U))}
    {f g : Z ⟶ (cechObj R 𝒰 q).obj (god R M)}
    (h : ∀ (z : Z) (τ : Fin (q + 1) → 𝒰.ι) (W : Opens Y), W ≤ cechInter 𝒰 q τ →
      cechVal R 𝒰 M (f z) W τ = cechVal R 𝒰 M (g z) W τ) : f = g := by
  refine cech_god_hom_ext R 𝒰 M fun z τ W hW ↦ ?_
  rw [← cechVal_eq R 𝒰 M _ W τ hW, ← cechVal_eq R 𝒰 M _ W τ hW]
  exact h z τ W hW

/-- **The sections of the Čech differential**, in the proof-free form. -/
theorem cechVal_d (q : ℕ) (c : (cechObj R 𝒰 q).obj (god R M)) (W : Opens Y)
    (τ : Fin (q + 2) → 𝒰.ι) (h : W ≤ cechInter 𝒰 (q + 1) τ) :
    cechVal R 𝒰 M (godD R 𝒰 M q c) W τ =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechVal R 𝒰 M c W (τ ∘ (SimplexCategory.δ i).toOrderHom) := by
  refine (cechVal_eq R 𝒰 M _ W τ h).trans ?_
  rw [cechCoeff_d]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cechVal_eq R 𝒰 M c W _ (h.trans (cechInter_le_comp 𝒰 τ _))]

/-- **The sections of the contracting homotopy**, in the proof-free form. -/
theorem cechVal_homotopyMap (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι)
    (c : (cechObj R 𝒰 (p + 1)).obj (god R M)) (W : Opens Y) (h : W ≤ cechInter 𝒰 p σ)
    (hex : ∃ i, W ≤ 𝒰.obj i) :
    cechVal R 𝒰 M (homotopyMap R 𝒰 M p c) W σ =
      cechVal R 𝒰 M c W (Fin.cons (coverIdx 𝒰 W hex) σ) := by
  refine (cechVal_eq R 𝒰 M _ W σ h).trans ?_
  rw [cechCoeff_homotopyMap R 𝒰 M p σ c h hex,
    cechVal_eq R 𝒰 M c W _ (le_cechInter_cons 𝒰 _ σ (le_coverIdx 𝒰 W hex) h)]

/-- The zeroth coface of a tuple with an index prepended is the tuple itself. -/
theorem cons_comp_delta_zero {p : ℕ} (t : 𝒰.ι) (τ : Fin (p + 2) → 𝒰.ι) :
    Fin.cons t τ ∘ (SimplexCategory.δ (0 : Fin (p + 3))).toOrderHom = τ := by
  funext j
  have h0 : (SimplexCategory.δ (0 : Fin (p + 3))).toOrderHom j = j.succ := rfl
  rw [Function.comp_apply, h0, Fin.cons_succ]

/-- The `(j+1)`-st coface of a tuple with an index prepended prepends the index to the `j`-th
coface of the tuple. -/
theorem cons_comp_delta_succ {p : ℕ} (t : 𝒰.ι) (τ : Fin (p + 2) → 𝒰.ι) (j : Fin (p + 2)) :
    Fin.cons t τ ∘ (SimplexCategory.δ j.succ).toOrderHom =
      Fin.cons t (τ ∘ (SimplexCategory.δ j).toOrderHom) := by
  funext m
  refine Fin.cases ?_ (fun m' ↦ ?_) m
  · have h0 : (SimplexCategory.δ j.succ).toOrderHom (0 : Fin (p + 2)) = 0 :=
      Fin.succ_succAbove_zero j
    rw [Function.comp_apply, h0, Fin.cons_zero, Fin.cons_zero]
  · have hs : (SimplexCategory.δ j.succ).toOrderHom m'.succ = (j.succAbove m').succ :=
      Fin.succ_succAbove_succ j m'
    rw [Function.comp_apply, hs, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]
    rfl

/-- **The contracting homotopy identity.** In every positive degree the identity of the Čech
complex of the Godement presheaf is the sum of the two composites with the homotopy. The
cancellation is the usual one: the zeroth coface of `t :: τ` is `τ`, which produces the
identity, and its remaining cofaces are `t :: (τ ∘ δⱼ)`, whose signed contributions cancel the
other composite. -/
theorem homotopyMap_id (p : ℕ) :
    homotopyMap R 𝒰 M p ≫ godD R 𝒰 M p + godD R 𝒰 M (p + 1) ≫ homotopyMap R 𝒰 M (p + 1) =
      𝟙 ((cechObj R 𝒰 (p + 1)).obj (god R M)) := by
  refine cech_god_hom_ext' R 𝒰 M fun z τ W hW ↦ ?_
  have hex : ∃ i, W ≤ 𝒰.obj i := exists_le_of_le_cechInter 𝒰 hW
  have hWt : W ≤ 𝒰.obj (coverIdx 𝒰 W hex) := le_coverIdx 𝒰 W hex
  have e1 : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechVal R 𝒰 M (homotopyMap R 𝒰 M p z) W (τ ∘ (SimplexCategory.δ i).toOrderHom) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cechVal R 𝒰 M z W
        (Fin.cons (coverIdx 𝒰 W hex) (τ ∘ (SimplexCategory.δ i).toOrderHom)) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [cechVal_homotopyMap R 𝒰 M p _ z W (hW.trans (cechInter_le_comp 𝒰 τ _)) hex]
  have hsplit : ∑ k : Fin (p + 3), (-1 : ℤ) ^ (k : ℕ) • cechVal R 𝒰 M z W
        (Fin.cons (coverIdx 𝒰 W hex) τ ∘ (SimplexCategory.δ k).toOrderHom) =
      cechVal R 𝒰 M z W τ + ∑ j : Fin (p + 2), -((-1 : ℤ) ^ (j : ℕ) • cechVal R 𝒰 M z W
        (Fin.cons (coverIdx 𝒰 W hex) (τ ∘ (SimplexCategory.δ j).toOrderHom))) := by
    rw [Fin.sum_univ_succ]
    congr 1
    · rw [cons_comp_delta_zero]
      simp
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [cons_comp_delta_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  refine Eq.trans (cechVal_add R 𝒰 M (godD R 𝒰 M p (homotopyMap R 𝒰 M p z))
    (homotopyMap R 𝒰 M (p + 1) (godD R 𝒰 M (p + 1) z)) W τ) ?_
  rw [cechVal_d R 𝒰 M p _ W τ hW, cechVal_homotopyMap R 𝒰 M (p + 1) τ _ W hW hex,
    cechVal_d R 𝒰 M (p + 1) z W (Fin.cons (coverIdx 𝒰 W hex) τ)
      (le_cechInter_cons 𝒰 _ τ hWt hW),
    e1, hsplit, Finset.sum_neg_distrib]
  change _ = cechVal R 𝒰 M z W τ
  abel

/-- **The Čech complex of the Godement presheaf is exact in every positive degree.** -/
theorem exactAt_god (p : ℕ) :
    ((cechComplexFunctor R 𝒰).obj (god R M)).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2)
    (CochainComplex.prev_nat_succ p) ((ComplexShape.up ℕ).next_eq' rfl)]
  exact exact_of_id_eq _ (homotopyMap R 𝒰 M p) (homotopyMap R 𝒰 M (p + 1))
    (homotopyMap_id R 𝒰 M p)

/-- **The higher Čech cohomology of the Godement presheaf vanishes.** -/
theorem isZero_cechCohomology_god (p : ℕ) :
    IsZero ((cechCohomologyFunctor R 𝒰 (p + 1)).obj (god R M)) :=
  (CechEffaceable.isZero_cechCohomology_iff_exactAt R 𝒰 (god R M) (p + 1)).2
    (exactAt_god R 𝒰 M p)

end Homotopy

section Instance

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{r}) (𝒰 : CechOpenCover Y)

/-- **Effaceability of the Čech δ-functor of a covering, the missing input of Stacks 01EN.**
Every presheaf of `R`-modules embeds in its Godement presheaf, whose higher Čech cohomology
vanishes, so the Čech δ-functor is effaceable in every positive degree. -/
instance effaceable_cechDeltaFunctor : (cechDeltaFunctor R 𝒰).Effaceable :=
  CechEffaceable.effaceable_of_exists_mono R 𝒰 fun p M ↦
    ⟨god R M, godUnit R M, mono_godUnit R M, isZero_cechCohomology_god R 𝒰 M p⟩

/-- **Universality of the Čech δ-functor of a covering, unconditionally.** This is Stacks 010T
applied to Čech cohomology, with the effaceability hypothesis now discharged: every natural
transformation out of degree-zero Čech cohomology extends uniquely to a morphism of
δ-functors. -/
theorem isUniversal_cechDeltaFunctor : (cechDeltaFunctor R 𝒰).IsUniversal :=
  CechEffaceable.cechDeltaFunctor_isUniversal R 𝒰

end Instance

end Stacks.Cohomology.CechGodement

end
