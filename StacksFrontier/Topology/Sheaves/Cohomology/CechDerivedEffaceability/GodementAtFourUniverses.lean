module

public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.GodementResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.AtFourUniverses

/-!
# Effaceability of the Čech δ-functor of Stacks 01EK, at four independent universes

Let `X : Type u` be a space, `R` a presheaf of rings on `X` in `RingCat.{r}`, and
`obj : ι → Opens X` a family of opens contained in `U`, indexed by `ι : Type w`. The Čech
δ-functor of [Stacks, Tag 01EK] on presheaves of `R`-modules at the module universe
`max u s w`, with `s` free, is effaceable. Specialized at `s := max r v w` this is
effaceability at the four universes of [Stacks, Tag 01EN] — the space universe `u`, the ring
universe `r`, the module universe `v` and the covering index universe `w`, with the common
module universe `max u r v w` — which is the last input of that comparison whose only
obstruction was a universe one: `Stacks.Cohomology.CechComparisonU` proves seven of the ten
fields of the four-universe comparison outright and reduces the rest to this instance together
with the identification of the connecting morphisms.

## Why the argument is restated rather than reused

`Stacks.Cohomology.CechGodement` runs the same Godement argument at `TopCat.{0}` with the
module universe `0`. That statement does not imply the present one: effaceability at four
independent universes is strictly more general, and there is no transport from a fixed
universe to it. What is
reused by name is everything that is already universe-polymorphic — the intersection and Čech
cochain machinery of `StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, the Čech complex and
δ-functor of [Stacks, Tag 01EJ] and [Stacks, Tag 01EK], the splitting criterion
`Stacks.Cohomology.CechGodement.exact_of_id_eq`, and `PresheafOfModules.mono_of_injective`.

## The argument

It is Godement's. The presheaf `(god R M)(V) = ∏_{W ≤ V} M(W)` receives a monomorphism from
`M`, namely the family of restrictions, whose component indexed by `V` itself is the identity.
Its Čech complex is contractible in positive degrees: the degree-`p` Čech cochains of `god R M`
are `∏_x ∏_{W ≤ U_x} M(W)`, where `U_x` is the open underlying the Čech intersection indexed by
the tuple `x`, and the Čech differential acts on the component indexed by an open `W` purely by
reindexing tuples, since every component is a section over the same `W`. Any such `W` is
contained in `U_{x 0}`, so a member of the family containing `W` can be chosen once and for all;
prepending its index to the tuple is a contracting homotopy.

The Čech complex of [Stacks, Tag 01EJ] is Mathlib's `CategoryTheory.cechComplexFunctor` for the
family `i ↦ Over.mk (homOfLE (le i))` of objects of `Over U`, whose degree-`p` term is a product
over categorical intersections *in `Over U`* rather than over infima of opens. `cechOpen` is the
open underlying such an intersection, and `cechOpen_le_obj`, `cechOpen_le_U`, `le_cechOpen` and
`cechOpen_le_comp` are the four facts about it that the homotopy uses; all four come from the
product structure alone, so the intersection is never computed. These four inequalities are also
the only thing the homotopy knows about the space, which is why the space universe `u` enters
only through the module universe: the Godement sections `∀ W ≤ V, M(W)` are indexed by a type in
`Type u` and valued in the module universe, so they live in `Type (max u s w)` exactly when the
modules do. That single `max u` is the whole universe content of the argument; `r` and `w` stay
free.

## Main definitions

* `resRing`, `GodSections`, `godObj`, `god`, `godUnit`, `godOver`: the Godement presheaf of a
  presheaf of modules, its embedding, and its restriction to the opens over `U`; these need only
  the space universe, the ring universe and a free module universe `max u s`, with no reference
  to a covering.
* `cechOpen`: the open underlying the Čech intersection indexed by a tuple of indices.
* `cechCoeff`, `cechVal`: the sections of a Čech cochain of the Godement presheaf, the second
  extended by zero outside its domain of definition.
* `homotopyMap`: the contracting homotopy.

## Main results

* `mono_godUnit`: the Godement embedding is a monomorphism.
* `homotopyMap_id`: the contracting homotopy identity, in every positive degree.
* `isZero_homology_god`: the higher Čech cohomology of the Godement presheaf vanishes.
* `effaceable_cechDeltaFunctor`: **the `Effaceable` instance** for the Čech δ-functor of
  [Stacks, Tag 01EK] at four independent universes.
* `cechDerivedComparisonOfDerivedδ`: with that instance available,
  `Stacks.Cohomology.CechComparisonU.cechDerivedComparisonOfEffaceable` takes the four-universe
  comparison of [Stacks, Tag 01EN] from the single remaining input `derivedδ_eq`.

## Implementation notes

The module universe is written `max u s` in the Godement section, which mentions no covering,
and `max u s w` from the Čech section on, because the Čech complex functor of
[Stacks, Tag 01EJ] lands in modules at `max (module universe) w`: the products are over
`(p+1)`-tuples of covering indices. Both shapes carry a single free universe beside the ones
that occur on their own, so the declarations say nothing more than they need to.

Universe arguments are written out explicitly at almost every call site. They have to be: the
module universe is a `max` expression, and universe unification refuses to guess the components
of a `max` from its value, so a bare `rw [godUnit_app_apply]` is stuck on
`max u ?s =?= max u s` where the annotated form is immediate.

Nothing here carries the tag `01EN`: the tag belongs on a complete
`Stacks.Cohomology.CechComparisonU.CechDerivedComparison`, whose `derivedδ_eq` field is not
proved in this repository yet.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechExactFunctor (presheafCechComplexFunctor sectionsOverFunctor)

universe u r s w v uS vS

namespace Stacks.Cohomology.CechGodementU

section Godement

variable {X : Type u} [TopologicalSpace X] (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X)

/-- The restriction ring homomorphism `R(V) ⟶ R(W)` attached to an inclusion `W ≤ V`, with the
ring universe `r` independent of the space universe `u`. -/
def resRing {V W : Opens X} (h : W ≤ V) : R.obj (op V) →+* R.obj (op W) :=
  (R.map (homOfLE h).op).hom

/-- Restricting a scalar twice is restricting it once, along the composite inclusion. -/
theorem resRing_resRing {V W Z : Opens X} (h : W ≤ V) (h' : Z ≤ W) (x : R.obj (op V)) :
    resRing R h' (resRing R h x) = resRing R (h'.trans h) x := by
  have e : (homOfLE h).op ≫ (homOfLE h').op = (homOfLE (h'.trans h)).op := rfl
  rw [resRing, resRing, resRing, ← e, R.map_comp]
  rfl

variable (M : PresheafOfModules.{max u s} R)

/-- The sections of the Godement presheaf of `M` over `V`: a family of sections of `M`, one
over each open contained in `V`. The index type lives in `Type u` and the values in
`Type (max u s)`, so the family lives in `Type (max u s)` and no universe is forced. -/
def GodSections (V : (Opens X)ᵒᵖ) : Type (max u s) :=
  ∀ W : {W : Opens X // W ≤ V.unop}, M.obj (op W.1)

/-- Godement sections are added componentwise. -/
instance (V : (Opens X)ᵒᵖ) : AddCommGroup (GodSections.{u, r, s} R M V) :=
  inferInstanceAs (AddCommGroup (∀ W : {W : Opens X // W ≤ V.unop}, M.obj (op W.1)))

/-- The `R(V)`-module structure on `GodSections R M V`: a scalar acts on the component indexed
by `W` through the restriction `R(V) → R(W)`. -/
instance (V : (Opens X)ᵒᵖ) : Module (R.obj V) (GodSections.{u, r, s} R M V) where
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
def godObj (V : (Opens X)ᵒᵖ) : ModuleCat.{max u s} (R.obj V) :=
  ModuleCat.of _ (GodSections.{u, r, s} R M V)

/-- A scalar acts on the component of a Godement section indexed by `W` through the restriction
of the scalar to `W`. -/
@[simp]
theorem godObj_smul_apply {V : (Opens X)ᵒᵖ} (r : R.obj V) (x : godObj.{u, r, s} R M V)
    (W : {W : Opens X // W ≤ V.unop}) : (r • x) W = resRing R W.2 r • x W :=
  rfl

/-- **The Godement presheaf of `M`.** Its sections over `V` are the families `(x_W)_{W ≤ V}`
with `x_W` a section of `M` over `W`; restriction along `V' ≤ V` forgets the components indexed
by the opens that are not contained in `V'`. -/
def god : PresheafOfModules.{max u s} R where
  obj V := godObj.{u, r, s} R M V
  map {V V'} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (godObj.{u, r, s} R M V'))
      { toFun := fun x W ↦ x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          funext W
          change resRing R (W.2.trans (leOfHom f.unop)) r • x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
              = resRing R W.2 ((R.map f).hom r) • x ⟨W.1, W.2.trans (leOfHom f.unop)⟩
          rw [show (R.map f).hom = resRing R (leOfHom f.unop) from rfl, resRing_resRing] }

/-- Restriction in the Godement presheaf drops the components outside the smaller open. -/
@[simp]
theorem god_map_apply {V V' : (Opens X)ᵒᵖ} (f : V ⟶ V') (x : (god.{u, r, s} R M).obj V)
    (W : {W : Opens X // W ≤ V'.unop}) :
    (god.{u, r, s} R M).map f x W = x ⟨W.1, W.2.trans (leOfHom f.unop)⟩ :=
  rfl

/-- Restriction along the identity inclusion is the identity on sections. -/
theorem map_le_rfl_apply {V : Opens X} (x : M.obj (op V)) :
    M.map (homOfLE (le_refl V)).op x = x := by
  show M.map (𝟙 (op V)) x = x
  rw [M.map_id]
  rfl

/-- **The Godement embedding of `M`.** A section of `M` over `V` is sent to the family of its
restrictions to the opens contained in `V`. -/
def godUnit : M ⟶ god.{u, r, s} R M where
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
theorem godUnit_app_apply {V : (Opens X)ᵒᵖ} (x : M.obj V)
    (W : {W : Opens X // W ≤ V.unop}) :
    (godUnit.{u, r, s} R M).app V x W = M.map (homOfLE W.2).op x :=
  rfl

/-- **The Godement embedding is a monomorphism.** Its component indexed by `V` itself is
restriction along the identity, hence the identity on sections over `V`. -/
instance mono_godUnit : Mono (godUnit.{u, r, s} R M) := by
  apply PresheafOfModules.mono_of_injective
  intro V x y h
  have h' := congrFun h ⟨V.unop, le_rfl⟩
  rw [godUnit_app_apply.{u, r, s}, godUnit_app_apply.{u, r, s},
    map_le_rfl_apply.{u, r, s}, map_le_rfl_apply.{u, r, s}] at h'
  exact h'

/-- The Godement presheaf of `M`, regarded as a presheaf of `R(U)`-modules on the opens over
`U`: the presheaf whose Čech complex [Stacks, Tag 01EJ] forms. It does not depend on the
covering, so the covering index universe does not occur here. -/
abbrev godOver : (Over U)ᵒᵖ ⥤ ModuleCat.{max u s} (R.obj (op U)) :=
  (sectionsOverFunctor.{u, r, max u s} R U).obj (god.{u, r, s} R M)

end Godement

section CechOver

variable {X : Type u} [TopologicalSpace X] (U : Opens X) {ι : Type w} (obj : ι → Opens X)
  (le : ∀ i, obj i ≤ U)

/-- The family of objects of `Over U` whose Čech complex is the Čech complex of
[Stacks, Tag 01EJ]. The index universe `w` is independent of the space universe `u`. -/
abbrev fam : ι → Over U := fun i ↦ Over.mk (homOfLE (le i))

/-- The open underlying the Čech intersection indexed by the tuple `x`, that is, the source of
the categorical product in `Over U` of the members of the family selected by `x`. It is the
infimum of those members, but nothing below computes it: only the four inequalities
`cechOpen_le_obj`, `cechOpen_le_U`, `le_cechOpen` and `cechOpen_le_comp` are used. -/
abbrev cechOpen {m : ℕ} (x : Fin m → ι) : Opens X :=
  (inter (fam U obj le) x).left

/-- The Čech intersection is contained in each member of the family it is taken over. -/
theorem cechOpen_le_obj {m : ℕ} (x : Fin m → ι) (a : Fin m) : cechOpen U obj le x ≤ obj (x a) :=
  leOfHom (interπ (fam U obj le) x a).left

/-- The Čech intersection is contained in the covered open. -/
theorem cechOpen_le_U {m : ℕ} (x : Fin m → ι) : cechOpen U obj le x ≤ U :=
  leOfHom (inter (fam U obj le) x).hom

/-- An open contained in every member of the family selected by `x` is contained in the Čech
intersection: it is the universal property of the product, read in the poset `Over U`. -/
theorem le_cechOpen {m : ℕ} (x : Fin m → ι) {W : Opens X} (hU : W ≤ U)
    (h : ∀ a, W ≤ obj (x a)) : W ≤ cechOpen U obj le x :=
  leOfHom (interLift (fam U obj le) (T := Over.mk (homOfLE hU))
    fun a ↦ Over.homMk (homOfLE (h a)) (Subsingleton.elim _ _)).left

/-- Reindexing a tuple enlarges its Čech intersection. -/
theorem cechOpen_le_comp {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m) :
    cechOpen U obj le x ≤ cechOpen U obj le (x ∘ h) :=
  leOfHom (interMap (fam U obj le) x h).left

/-- An open contained in a nonempty Čech intersection is contained in a member of the family:
the tuple indexing the intersection has a zeroth entry. -/
theorem exists_le_of_le_cechOpen {p : ℕ} {x : Fin (p + 1) → ι} {W : Opens X}
    (h : W ≤ cechOpen U obj le x) : ∃ i, W ≤ obj i :=
  ⟨x 0, h.trans (cechOpen_le_obj U obj le x 0)⟩

/-- Prepending an index to a tuple keeps an open inside the Čech intersection, provided the
open is contained in the member prepended. -/
theorem le_cechOpen_cons {p : ℕ} (t : ι) (x : Fin (p + 1) → ι) {W : Opens X} (ht : W ≤ obj t)
    (hx : W ≤ cechOpen U obj le x) : W ≤ cechOpen U obj le (Fin.cons t x) :=
  le_cechOpen U obj le _ (hx.trans (cechOpen_le_U U obj le x))
    (Fin.cases (by simpa using ht) fun j ↦ by
      simpa using hx.trans (cechOpen_le_obj U obj le x j))

/-- A chosen member of the family containing `W`, for an open `W` that is contained in one. -/
def coverIdx (W : Opens X) (hW : ∃ i, W ≤ obj i) : ι := hW.choose

/-- The chosen member of the family does contain `W`. -/
theorem le_coverIdx (W : Opens X) (hW : ∃ i, W ≤ obj i) : W ≤ obj (coverIdx obj W hW) :=
  hW.choose_spec

/-- The index prepended to the tuple `x` for the component of the Godement sections indexed by
the open `W`: a chosen member of the family containing `W`, which exists because `W` is
contained in the Čech intersection indexed by `x`. -/
def homIdx {p : ℕ} (x : Fin (p + 1) → ι)
    (W : {W : Opens X // W ≤ cechOpen U obj le x}) : ι :=
  coverIdx obj W.1 (exists_le_of_le_cechOpen U obj le W.2)

/-- `W` is contained in the Čech intersection indexed by `x` with `homIdx U obj le x W`
prepended. -/
theorem le_cechOpen_homCons {p : ℕ} (x : Fin (p + 1) → ι)
    (W : {W : Opens X // W ≤ cechOpen U obj le x}) :
    W.1 ≤ cechOpen U obj le (Fin.cons (homIdx U obj le x W) x) :=
  le_cechOpen_cons U obj le _ x
    (le_coverIdx obj W.1 (exists_le_of_le_cechOpen U obj le W.2)) W.2

end CechOver

section ModuleCatApply

variable {S : Type uS} [Ring S] {A B : ModuleCat.{vS} S}

/-- A finite sum of morphisms of modules acts as the sum of their actions. The ring universe and
the module universe are independent. -/
theorem moduleCat_sum_apply {κ : Type*} (s : Finset κ) (f : κ → (A ⟶ B)) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  change (ModuleCat.Hom.hom (∑ i ∈ s, f i : A ⟶ B)) a = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]

end ModuleCatApply

section Homotopy

variable {X : Type u} [TopologicalSpace X] (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X)
  {ι : Type w} (obj : ι → Opens X) (le : ∀ i, obj i ≤ U)
  (M : PresheafOfModules.{max u s w} R)

/-- The Čech complex of the Godement presheaf of `M`, that is, the value at `god R M` of the
Čech complex functor of [Stacks, Tag 01EJ]. -/
abbrev godComplex : CochainComplex (ModuleCat.{max u s w} (R.obj (op U))) ℕ :=
  (CategoryTheory.cechComplexFunctor (fam U obj le)).obj (godOver.{u, r, max s w} R U M)

/-- Scalars from `R(U)` act on the Godement sections over a Čech intersection through the
restriction to the open indexing the component. -/
theorem godOver_smul_apply {m : ℕ} (x : Fin m → ι) (r : R.obj (op U))
    (y : (godOver.{u, r, max s w} R U M).obj (op (inter (fam U obj le) x)))
    (W : {W : Opens X // W ≤ cechOpen U obj le x}) :
    (r • y) W = resRing R (W.2.trans (cechOpen_le_U U obj le x)) r • y W := by
  show resRing R W.2 (resRing R (cechOpen_le_U U obj le x) r) • y W = _
  rw [resRing_resRing]

/-- The section over `W` of the component at the tuple `x` of a degree-`q` Čech cochain of the
Godement presheaf of `M`. -/
def cechCoeff {q : ℕ} (c : (godComplex.{u, r, s, w} R U obj le M).X q) (x : Fin (q + 1) → ι)
    {W : Opens X} (h : W ≤ cechOpen U obj le x) : M.obj (op W) :=
  π (fam U obj le) (godOver.{u, r, max s w} R U M) q x c ⟨W, h⟩

/-- Sections of Čech cochains are additive. -/
theorem cechCoeff_add {q : ℕ} (c c' : (godComplex.{u, r, s, w} R U obj le M).X q)
    (x : Fin (q + 1) → ι) {W : Opens X} (h : W ≤ cechOpen U obj le x) :
    cechCoeff R U obj le M (c + c') x h =
      cechCoeff R U obj le M c x h + cechCoeff R U obj le M c' x h :=
  congrFun (map_add (π (fam U obj le) (godOver.{u, r, max s w} R U M) q x).hom c c') ⟨W, h⟩

/-- Sections of Čech cochains are semilinear: a scalar from `R(U)` acts on the section over `W`
through its restriction to `W`. -/
theorem cechCoeff_smul {q : ℕ} (r : R.obj (op U))
    (c : (godComplex.{u, r, s, w} R U obj le M).X q)
    (x : Fin (q + 1) → ι) {W : Opens X} (h : W ≤ cechOpen U obj le x) :
    cechCoeff R U obj le M (r • c) x h =
      resRing R (h.trans (cechOpen_le_U U obj le x)) r • cechCoeff R U obj le M c x h :=
  (congrFun (map_smul (π (fam U obj le) (godOver.{u, r, max s w} R U M) q x).hom r c) ⟨W, h⟩).trans
    (godOver_smul_apply R U obj le M x r _ ⟨W, h⟩)

/-- Sections of Čech cochains commute with integer scalars. -/
theorem cechCoeff_zsmul {q : ℕ} (n : ℤ) (c : (godComplex.{u, r, s, w} R U obj le M).X q)
    (x : Fin (q + 1) → ι) {W : Opens X} (h : W ≤ cechOpen U obj le x) :
    cechCoeff R U obj le M (n • c) x h = n • cechCoeff R U obj le M c x h :=
  congrFun (map_zsmul (π (fam U obj le) (godOver.{u, r, max s w} R U M) q x).hom n c) ⟨W, h⟩

/-- Sections of Čech cochains commute with finite sums. -/
theorem cechCoeff_sum {q : ℕ} {κ : Type*} (s : Finset κ)
    (c : κ → (godComplex.{u, r, s, w} R U obj le M).X q) (x : Fin (q + 1) → ι)
    {W : Opens X} (h : W ≤ cechOpen U obj le x) :
    cechCoeff R U obj le M (∑ i ∈ s, c i) x h =
      ∑ i ∈ s, cechCoeff R U obj le M (c i) x h := by
  exact (congrFun (map_sum (π (fam U obj le) (godOver.{u, r, max s w} R U M) q x).hom c s)
    ⟨W, h⟩).trans (Finset.sum_apply _ _ _)

/-- Two morphisms into the degree-`q` Čech cochains of the Godement presheaf agree as soon as
all sections of all their components agree. -/
theorem cech_god_hom_ext {q : ℕ} {Z : ModuleCat.{max u s w} (R.obj (op U))}
    {f g : Z ⟶ (godComplex.{u, r, s, w} R U obj le M).X q}
    (h : ∀ (z : Z) (x : Fin (q + 1) → ι) (W : Opens X) (hW : W ≤ cechOpen U obj le x),
      cechCoeff R U obj le M (f z) x hW = cechCoeff R U obj le M (g z) x hW) : f = g := by
  refine hom_ext (fam U obj le) (godOver.{u, r, max s w} R U M) fun x ↦ ?_
  ext z
  refine funext fun W ↦ ?_
  exact h z x W.1 W.2

/-- **Reindexing along a face map reads off the component at the reindexed tuple.** The
restriction maps of the Godement presheaf change the index of a component, not the section
itself, because every component is a section over the same open. -/
theorem cechCoeff_face {q : ℕ} (i : Fin (q + 2)) (y : Fin (q + 2) → ι)
    (c : (godComplex.{u, r, s, w} R U obj le M).X q) {W : Opens X}
    (h : W ≤ cechOpen U obj le y) :
    cechCoeff R U obj le M
        (face (fam U obj le) (godOver.{u, r, max s w} R U M) q i c) y h =
      cechCoeff R U obj le M c (y ∘ i.succAbove)
        (h.trans (cechOpen_le_comp U obj le y i.succAbove)) :=
  congrFun (ConcreteCategory.congr_hom
    (face_comp_π (fam U obj le) (godOver.{u, r, max s w} R U M) q i y) c) ⟨W, h⟩

/-- The Čech differential of the Godement presheaf, written with the Čech cochain modules
themselves as source and target. -/
def godD (p : ℕ) :
    (godComplex.{u, r, s, w} R U obj le M).X p ⟶ (godComplex.{u, r, s, w} R U obj le M).X (p + 1) :=
  (godComplex.{u, r, s, w} R U obj le M).d p (p + 1)

/-- **The sections of the Čech differential.** The section over `W` of the component at `y` of
`d c` is the alternating sum, over the face maps, of the sections over `W` of the components of
`c` at the faces of `y`. -/
theorem cechCoeff_d (q : ℕ) (c : (godComplex.{u, r, s, w} R U obj le M).X q)
    (y : Fin (q + 2) → ι) {W : Opens X} (h : W ≤ cechOpen U obj le y) :
    cechCoeff R U obj le M (godD R U obj le M q c) y h =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechCoeff R U obj le M c (y ∘ i.succAbove)
          (h.trans (cechOpen_le_comp U obj le y i.succAbove)) := by
  have hc : godD R U obj le M q c =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        face (fam U obj le) (godOver.{u, r, max s w} R U M) q i c :=
    (ConcreteCategory.congr_hom (d_eq (fam U obj le) (godOver.{u, r, max s w} R U M) q) c).trans
      (moduleCat_sum_apply _ _ c)
  rw [hc, cechCoeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cechCoeff_zsmul, cechCoeff_face]

/-- **The degree-`p` component of the contracting homotopy.** The section over `W` of the value
at the tuple `x` is the section over `W` of the value at `x` with `homIdx U obj le x W`
prepended. -/
def homCompFun (p : ℕ) (x : Fin (p + 1) → ι)
    (c : (godComplex.{u, r, s, w} R U obj le M).X (p + 1)) :
    (godOver.{u, r, max s w} R U M).obj (op (inter (fam U obj le) x)) :=
  fun W ↦ cechCoeff R U obj le M c (Fin.cons (homIdx U obj le x W) x)
    (le_cechOpen_homCons U obj le x W)

/-- The degree-`p` homotopy component, as a morphism of `R(U)`-modules. -/
def homComp (p : ℕ) (x : Fin (p + 1) → ι) :
    (godComplex.{u, r, s, w} R U obj le M).X (p + 1) ⟶
      (godOver.{u, r, max s w} R U M).obj (op (inter (fam U obj le) x)) :=
  ConcreteCategory.ofHom
    { toFun := homCompFun R U obj le M p x
      map_add' := fun c c' ↦ by
        funext W
        exact cechCoeff_add R U obj le M c c' _ (le_cechOpen_homCons U obj le x W)
      map_smul' := fun r c ↦ by
        funext W
        exact (cechCoeff_smul R U obj le M r c (Fin.cons (homIdx U obj le x W) x)
            (le_cechOpen_homCons U obj le x W)).trans
          (godOver_smul_apply R U obj le M x r (homCompFun R U obj le M p x c) W).symm }

/-- **The contracting homotopy of the Čech complex of the Godement presheaf.** -/
def homotopyMap (p : ℕ) :
    (godComplex.{u, r, s, w} R U obj le M).X (p + 1) ⟶
      (godComplex.{u, r, s, w} R U obj le M).X p :=
  lift (fam U obj le) (godOver.{u, r, max s w} R U M) (homComp R U obj le M p)

/-- **The sections of the contracting homotopy.** -/
theorem cechCoeff_homotopyMap (p : ℕ) (x : Fin (p + 1) → ι)
    (c : (godComplex.{u, r, s, w} R U obj le M).X (p + 1)) {W : Opens X}
    (h : W ≤ cechOpen U obj le x) (hW : ∃ i, W ≤ obj i) :
    cechCoeff R U obj le M (homotopyMap R U obj le M p c) x h =
      cechCoeff R U obj le M c (Fin.cons (coverIdx obj W hW) x)
        (le_cechOpen_cons U obj le _ x (le_coverIdx obj W hW) h) :=
  congrFun (ConcreteCategory.congr_hom
    (lift_comp_π (fam U obj le) (godOver.{u, r, max s w} R U M) (homComp R U obj le M p) x) c)
      ⟨W, h⟩

open scoped Classical in
/-- The section over `W` of the component at `x`, extended by zero when `W` is not contained in
the Čech intersection indexed by `x`. This makes it a function of the tuple alone, so that the
alternating sums below can be rearranged without carrying inclusion proofs. -/
def cechVal {q : ℕ} (c : (godComplex.{u, r, s, w} R U obj le M).X q) (W : Opens X)
    (x : Fin (q + 1) → ι) : M.obj (op W) :=
  if h : W ≤ cechOpen U obj le x then cechCoeff R U obj le M c x h else 0

/-- Where the inclusion holds, `cechVal` is the section. -/
theorem cechVal_eq {q : ℕ} (c : (godComplex.{u, r, s, w} R U obj le M).X q) (W : Opens X)
    (x : Fin (q + 1) → ι) (h : W ≤ cechOpen U obj le x) :
    cechVal R U obj le M c W x = cechCoeff R U obj le M c x h := by
  unfold cechVal
  split_ifs
  rfl

/-- `cechVal` is additive in the cochain. -/
theorem cechVal_add {q : ℕ} (c c' : (godComplex.{u, r, s, w} R U obj le M).X q) (W : Opens X)
    (x : Fin (q + 1) → ι) :
    cechVal R U obj le M (c + c') W x =
      cechVal R U obj le M c W x + cechVal R U obj le M c' W x := by
  unfold cechVal
  split_ifs with h
  · exact cechCoeff_add R U obj le M c c' x h
  · exact (add_zero 0).symm

/-- Two morphisms into the degree-`q` Čech cochains of the Godement presheaf agree as soon as
all the sections of all their components agree. -/
theorem cech_god_hom_ext' {q : ℕ} {Z : ModuleCat.{max u s w} (R.obj (op U))}
    {f g : Z ⟶ (godComplex.{u, r, s, w} R U obj le M).X q}
    (h : ∀ (z : Z) (x : Fin (q + 1) → ι) (W : Opens X), W ≤ cechOpen U obj le x →
      cechVal R U obj le M (f z) W x = cechVal R U obj le M (g z) W x) : f = g := by
  refine cech_god_hom_ext R U obj le M fun z x W hW ↦ ?_
  rw [← cechVal_eq R U obj le M _ W x hW, ← cechVal_eq R U obj le M _ W x hW]
  exact h z x W hW

/-- **The sections of the Čech differential**, in the proof-free form. -/
theorem cechVal_d (q : ℕ) (c : (godComplex.{u, r, s, w} R U obj le M).X q) (W : Opens X)
    (y : Fin (q + 2) → ι) (h : W ≤ cechOpen U obj le y) :
    cechVal R U obj le M (godD R U obj le M q c) W y =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechVal R U obj le M c W (y ∘ i.succAbove) := by
  refine (cechVal_eq R U obj le M _ W y h).trans ?_
  rw [cechCoeff_d]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cechVal_eq R U obj le M c W _ (h.trans (cechOpen_le_comp U obj le y i.succAbove))]

/-- **The sections of the contracting homotopy**, in the proof-free form. -/
theorem cechVal_homotopyMap (p : ℕ) (x : Fin (p + 1) → ι)
    (c : (godComplex.{u, r, s, w} R U obj le M).X (p + 1)) (W : Opens X)
    (h : W ≤ cechOpen U obj le x) (hex : ∃ i, W ≤ obj i) :
    cechVal R U obj le M (homotopyMap R U obj le M p c) W x =
      cechVal R U obj le M c W (Fin.cons (coverIdx obj W hex) x) := by
  refine (cechVal_eq R U obj le M _ W x h).trans ?_
  rw [cechCoeff_homotopyMap R U obj le M p x c h hex,
    cechVal_eq R U obj le M c W _
      (le_cechOpen_cons U obj le _ x (le_coverIdx obj W hex) h)]

/-- The zeroth face of a tuple with an index prepended is the tuple itself. -/
theorem cons_comp_succAbove_zero {p : ℕ} (t : ι) (y : Fin (p + 2) → ι) :
    Fin.cons t y ∘ (0 : Fin (p + 3)).succAbove = y := by
  funext j
  rw [Function.comp_apply, Fin.zero_succAbove, Fin.cons_succ]

/-- The `(j+1)`-st face of a tuple with an index prepended prepends the index to the `j`-th
face of the tuple. -/
theorem cons_comp_succAbove_succ {p : ℕ} (t : ι) (y : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    Fin.cons t y ∘ j.succ.succAbove = Fin.cons t (y ∘ j.succAbove) := by
  funext m
  refine Fin.cases ?_ (fun m' ↦ ?_) m
  · rw [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero, Fin.cons_zero]
  · rw [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ,
      Function.comp_apply]

/-- **The contracting homotopy identity.** In every positive degree the identity of the Čech
complex of the Godement presheaf is the sum of the two composites with the homotopy. The
cancellation is the usual one: the zeroth face of `t :: y` is `y`, which produces the identity,
and its remaining faces are `t :: (y ∘ δⱼ)`, whose signed contributions cancel the other
composite. -/
theorem homotopyMap_id (p : ℕ) :
    homotopyMap R U obj le M p ≫ godD R U obj le M p +
        godD R U obj le M (p + 1) ≫ homotopyMap R U obj le M (p + 1) =
      𝟙 ((godComplex.{u, r, s, w} R U obj le M).X (p + 1)) := by
  refine cech_god_hom_ext' R U obj le M fun z y W hW ↦ ?_
  have hex : ∃ i, W ≤ obj i := exists_le_of_le_cechOpen U obj le hW
  have hWt : W ≤ obj (coverIdx obj W hex) := le_coverIdx obj W hex
  have e1 : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechVal R U obj le M (homotopyMap R U obj le M p z) W (y ∘ i.succAbove) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cechVal R U obj le M z W
        (Fin.cons (coverIdx obj W hex) (y ∘ i.succAbove)) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [cechVal_homotopyMap R U obj le M p _ z W
        (hW.trans (cechOpen_le_comp U obj le y i.succAbove)) hex]
  have hsplit : ∑ k : Fin (p + 3), (-1 : ℤ) ^ (k : ℕ) • cechVal R U obj le M z W
        (Fin.cons (coverIdx obj W hex) y ∘ k.succAbove) =
      cechVal R U obj le M z W y + ∑ j : Fin (p + 2), -((-1 : ℤ) ^ (j : ℕ) •
        cechVal R U obj le M z W
          (Fin.cons (coverIdx obj W hex) (y ∘ j.succAbove))) := by
    rw [Fin.sum_univ_succ]
    congr 1
    · rw [cons_comp_succAbove_zero]
      simp
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [cons_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  refine Eq.trans (cechVal_add R U obj le M (godD R U obj le M p (homotopyMap R U obj le M p z))
    (homotopyMap R U obj le M (p + 1) (godD R U obj le M (p + 1) z)) W y) ?_
  rw [cechVal_d R U obj le M p _ W y hW,
    cechVal_homotopyMap R U obj le M (p + 1) y _ W hW hex,
    cechVal_d R U obj le M (p + 1) z W (Fin.cons (coverIdx obj W hex) y)
      (le_cechOpen_cons U obj le _ y hWt hW),
    e1, hsplit, Finset.sum_neg_distrib]
  show _ = cechVal R U obj le M z W y
  abel

/-- **The Čech complex of the Godement presheaf is exact in every positive degree.** -/
theorem exactAt_god (p : ℕ) :
    ((presheafCechComplexFunctor.{u, r, max u s w, w} R U obj le).obj
      (god.{u, r, max s w} R M)).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2)
    (CochainComplex.prev_nat_succ p) ((ComplexShape.up ℕ).next_eq' rfl)]
  exact CechGodement.exact_of_id_eq _ (homotopyMap R U obj le M p)
    (homotopyMap R U obj le M (p + 1)) (homotopyMap_id R U obj le M p)

/-- **The higher Čech cohomology of the Godement presheaf vanishes.** Čech cohomology is the
homology of the Čech complex, which `exactAt_god` makes exact in every positive degree. -/
theorem isZero_homology_god (p : ℕ) :
    IsZero (((presheafCechComplexFunctor.{u, r, max u s w, w} R U obj le).obj
      (god.{u, r, max s w} R M)).homology (p + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ (p + 1)).1
    (exactAt_god.{u, r, max s w} R U obj le M p)

end Homotopy

end Stacks.Cohomology.CechGodementU

namespace Stacks.Cohomology.CechComparisonU

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- **Effaceability of the Čech δ-functor of [Stacks, Tag 01EK] at four independent
universes**, the first of the two inputs that `cechDerivedComparisonOfEffaceable` needs. Every
presheaf of `O`-modules at the module universe `max u r v w` embeds in its Godement presheaf,
whose higher Čech cohomology vanishes, so the Čech δ-functor is effaceable in every positive
degree.

Nothing in the Godement argument forces the space, ring, module and covering index universes to
agree. -/
instance effaceable_cechDeltaFunctor :
    (CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).Effaceable where
  nonempty M n :=
    ⟨{ I := CechGodementU.god.{u, r, max r v w} O.obj M
       ι := CechGodementU.godUnit.{u, r, max r v w} O.obj M
       map_ι :=
        (CechGodementU.isZero_homology_god.{u, r, max r v w, w} O.obj 𝒰.U 𝒰.obj 𝒰.le M
          n).eq_of_tgt _ _ }⟩

/-- **The four-universe comparison of [Stacks, Tag 01EN] from its one remaining input.** With
effaceability available, `cechDerivedComparisonOfEffaceable` asks only for `derivedδ_eq`: the
identification of the connecting morphisms of the right-derived δ-functor with the ones computed
degreewise on a short exact sequence of injective resolutions. Every other field of
`CechDerivedComparison` is proved at the four universes. -/
def cechDerivedComparisonOfDerivedδ
    (hδ : letI := enoughInjectives_modules.{u, r, v, w} O 𝒰
      DerivedConnectingProperty.{u, r, v, w} O 𝒰 (derivedDeltaFunctor.{u, r, v, w} O 𝒰)
        (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰)) :
    CechDerivedComparison.{u, r, v, w} O 𝒰 :=
  cechDerivedComparisonOfEffaceable.{u, r, v, w} O 𝒰 hδ

end Stacks.Cohomology.CechComparisonU

end
