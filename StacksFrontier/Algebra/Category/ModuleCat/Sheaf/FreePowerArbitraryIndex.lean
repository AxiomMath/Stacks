module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The symmetric and exterior powers of a free sheaf of modules on an arbitrary index type

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `γ` a type in the module
universe. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify` proves
`Symⁿ (free γ) ≅ free {d : γ →₀ ℕ | d.degree = n}` and `⋀ⁿ (free γ) ≅ free (powersetCard γ n)`
for a **finite** `γ`, and records in its implementation notes that the infinite case is a genuine
gap: its whole argument runs through `Stacks.SheafOfModules.freeCoordBasis`, which exists only
for a finite index because the sections of `free γ` are computed there from the coproduct being
a product.

This file removes the finiteness hypothesis. The route does not describe the sections of
`free γ` at all. Instead it works with the **free presheaf of modules** `freeConst γ`, whose
sections over `V` are honestly `γ →₀ O♯(V)` with the standard basis, and identifies its
sheafification with `free γ`:

* `Symⁿ` and `⋀ⁿ` of `freeConst γ` are computed sectionwise by matching bases, exactly as in
  `FreePowerSheafify` but with `Finsupp.basisSingleOne` in place of `freeCoordBasis` — and that
  basis is natural for a trivial reason, since the restriction maps of `freeConst γ` send
  `single i r` to `single i (ρ r)`;
* `freeConst γ` is the coproduct of `γ` copies of the unit presheaf of modules, so its
  sheafification is the coproduct of `γ` copies of the unit *sheaf* of modules, which is
  `SheafOfModules.free γ` by definition;
* `SheafOfModules.tensorExteriorSymmetricAlgebras J a F` — the inhabitant of Section 17.21's
  bundle built in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant` — is a package of
  algebras for the sheafification of an **arbitrary presheaf of modules** `F`, and its degree-`n`
  symmetric and exterior pieces are the sheafifications of `PresheafOfModules.symPow n F` and
  `extPow n F` on the nose. Taking `F := freeConst γ` therefore computes the powers of `free γ`
  with no reference to the sections of `free γ`.

## Main definitions

* `Stacks.PresheafOfModules.freeConst`: the free presheaf of modules on a type, i.e.
  `PresheafOfModules.freeObj` of the constant presheaf of types.
* `Stacks.PresheafOfModules.freeConstBasis`: the standard basis of its sections.
* `Stacks.PresheafOfModules.freeConstDesc`: the morphism out of `freeConst γ` prescribed by a
  family of global sections of the target, with `freeConst_hom_ext` for its uniqueness.
* `Stacks.PresheafOfModules.freeConstCoprodIso`: `freeConst γ ≅ ∐ (fun _ : γ => unit R)`.
* `Stacks.PresheafOfModules.symPowFreeConstIso` and `extPowFreeConstIso`: the sectionwise
  symmetric and exterior powers of `freeConst γ` are free presheaves of modules, on the
  degree-`n` multidegrees and on the `n`-element subsets of `γ` respectively.
* `Stacks.SheafOfModules.sheafifyFreeConstIso`: the sheafification of `freeConst γ` is
  `SheafOfModules.free γ`.

## Main results

* `Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` and `exteriorPowerFreeIsoAnyIndex`:
  **`Symⁿ (free γ) ≅ free {d | d.degree = n}` and `⋀ⁿ (free γ) ≅ free (powersetCard γ n)` for an
  arbitrary index type `γ`**, for an arbitrary package of algebras in the sense of Section 17.21
  over `free γ`.
* `Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex` and
  `exteriorPowerFreeIsoOfIsoAnyIndex`: the same for a sheaf of modules merely isomorphic to a
  free one.
* `Stacks.SheafOfModules.exists_nonempty_iso_free_symmetricPower` and
  `exists_nonempty_iso_free_exteriorPower`: the consumer form — every symmetric or exterior power
  of a sheaf of modules isomorphic to a free one is free.

## Implementation notes

**No Stacks tag is claimed.** Tag 00DN is the statement about modules over a ring and is already
formalized and tagged. Tag 01CK clause (6) is the assertion for a *locally* free sheaf of
modules; what is proved here, as in `FreePowerFree` and `FreePowerSheafify`, is the globally free
case — with the finiteness hypothesis removed. The localization step, that the powers commute
with restriction to a slice site, is `Stacks.SheafOfModules.symmetricPowerOverIso` and
`exteriorPowerOverIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction` together with
`tensorPowerOverIso` of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers`; the
clause itself is carried there, by
`Stacks.SheafOfModules.isLocallyFree_symmetricPower`, `isLocallyFree_exteriorPower` and
`isLocallyFree_tensorPower`, which are exactly those isomorphisms composed with the three
statements below. So the tag is declined here because the globally free case is not the clause,
not because anything is missing.

**No filtered colimits and no local bijectivity of `symPow`.** `FreePowerSheafify` suggests two
routes to the infinite case: writing `free γ` as the filtered colimit of `free S` over the finite
subsets, and showing `Symⁿ` and `⋀ⁿ` commute with that colimit; or proving that `symPow n` of a
locally bijective morphism of presheaves of modules is again locally bijective, and applying it
to the sheafification unit of `freeConst γ`. Neither is needed. The package of algebras produced
by `tensorExteriorSymmetricAlgebras` is already a package for the sheafification of an arbitrary
presheaf of modules, so the comparison between two packages over one sheaf of modules
(`TensorExteriorSymmetricAlgebras.symmetricAlgebraIso`) does all the work that local bijectivity
of `symPow n` would have done, and it is already proved.

**Why `freeConst` rather than the coproduct of units.** The two are identified by
`freeConstCoprodIso`, and the sheafification half of the argument uses the coproduct spelling,
since `SheafOfModules.free γ` *is* `∐ (fun _ : γ => unit)`. But the symmetric and exterior powers
need a basis of the sections over each object, and only the `freeObj` spelling has one on the
nose: `(freeObj (const γ)).obj V` is `γ →₀ O♯(V)`, whose basis is `Finsupp.basisSingleOne`,
whereas the sections of the coproduct are a colimit that would have to be computed.

**The transport of a package along an isomorphism keeps the three graded algebras.**
`SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso` changes only the generators and the
homogeneous identifications of the tensor algebra, so a package and its transport have literally
the same symmetric and exterior powers. That is what lets a package given over `free γ` be read
as a package over the sheafification of `freeConst γ` with no comparison isomorphism in the
statement.

**Universes.** The index type lies in the module universe `u`, which is forced and not chosen:
`SheafOfModules.free` is only defined for an index there, and `PresheafOfModules.freeObj` of a
presheaf of types in `Type u` is a presheaf of modules in `PresheafOfModules.{u}`. The site
universes `u₁` and `v` are independent of `u` throughout. The ring universe equals the module
universe, as it does in `FreePowerSheafify`, because
`SheafOfModules.tensorExteriorSymmetricAlgebras` is stated for `GradedAlgebra.{w, w}`.

**The decidable equality and the linear order are supplied classically** in the `exists_` forms,
so they do not appear in those statements; the monomial basis of a symmetric power needs the
former and Mathlib's exterior basis needs the latter.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The free presheaf of modules on a constant presheaf of types. -/
noncomputable abbrev freeConst (γ : Type u) : PresheafOfModules.{u} R :=
  PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj γ)

/-- The standard basis of the sections of `freeConst γ`. -/
noncomputable def freeConstBasis (γ : Type u) (V : Cᵒᵖ) :
    Module.Basis γ (ToType (R.obj V)) (ToType ((freeConst (R := R) γ).obj V)) :=
  Finsupp.basisSingleOne

/-- The restriction maps of `freeConst γ` send each standard basis vector to the standard basis
vector of the same index. -/
theorem freeConstBasis_map (γ : Type u) {V W : Cᵒᵖ} (m : V ⟶ W) (i : γ) :
    (freeConst (R := R) γ).map m (freeConstBasis γ V i) = freeConstBasis γ W i :=
  ModuleCat.freeDesc_apply _ i

/-- **The restriction maps of the free presheaf of modules are the restriction maps of the
structure presheaf applied coefficientwise.**  The sections of `freeConst γ` over an object are
the finitely supported families of sections of `R` there, and the restriction maps act on such a
family through `Finsupp.mapRange`.  This is `freeConstBasis_map` read on
an arbitrary family rather than on a standard basis vector. -/
theorem freeConst_map_apply (γ : Type u) {V W : Cᵒᵖ} (m : V ⟶ W)
    (c : γ →₀ ToType (R.obj V)) :
    (freeConst (R := R) γ).map m c = Finsupp.mapRange (R.map m) (map_zero _) c := by
  have hb : ∀ (U : Cᵒᵖ) (l : γ),
      (freeConstBasis (R := R) γ U) l =
        Finsupp.single l (1 : ToType (R.obj U)) :=
    fun U l => congrFun Finsupp.coe_basisSingleOne l
  induction c using Finsupp.induction_linear with
  | zero =>
      exact ((freeConst (R := R) γ).map m).hom.map_zero.trans
        Finsupp.mapRange_zero.symm
  | add x y hx hy =>
      have hadd : ((freeConst (R := R) γ).map m) (x + y) =
          ((freeConst (R := R) γ).map m) x +
            ((freeConst (R := R) γ).map m) y := map_add _ x y
      exact hadd.trans ((congrArg₂ (· + ·) hx hy).trans
        (Finsupp.mapRange_add
          (fun a b => map_add (ConcreteCategory.hom (R.map m)) a b) x y).symm)
  | single l r =>
      have h1 : (Finsupp.single l r : γ →₀ ToType (R.obj V)) =
          r • (freeConstBasis (R := R) γ V) l :=
        (((congrArg (fun z => r • z) (hb V l)).trans
          (Finsupp.smul_single r l (1 : ToType (R.obj V)))).trans
            (congrArg (Finsupp.single l)
              (by simp : r • (1 : ToType (R.obj V)) = r))).symm
      have h4 : ((R.map m) r) • (freeConstBasis (R := R) γ W) l =
          (Finsupp.single l ((R.map m) r) : γ →₀ ToType (R.obj W)) :=
        ((congrArg (fun z => ((R.map m) r) • z) (hb W l)).trans
          (Finsupp.smul_single _ l (1 : ToType (R.obj W)))).trans
            (congrArg (Finsupp.single l)
              (by simp : ((R.map m) r) • (1 : ToType (R.obj W)) = (R.map m) r))
      exact (congrArg ((freeConst (R := R) γ).map m) h1).trans
        ((PresheafOfModules.map_smul (M := freeConst (R := R) γ) m r _).trans
          ((congrArg (fun z => ((R.map m) r) • z)
              (freeConstBasis_map γ m l)).trans
            (h4.trans Finsupp.mapRange_single.symm)))

/-- A morphism out of `freeConst γ` is determined by its values on the standard basis. -/
theorem freeConst_hom_ext {γ : Type u} {M : PresheafOfModules.{u} R}
    {f g : freeConst (R := R) γ ⟶ M}
    (h : ∀ (V : Cᵒᵖ) (i : γ), f.app V (freeConstBasis γ V i) = g.app V (freeConstBasis γ V i)) :
    f = g :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ((freeConstBasis γ V).ext (h V))

/-- The morphism out of `freeConst γ` sending the `i`-th basis vector to the global section
`s i`. -/
noncomputable def freeConstDesc {γ : Type u} {M : PresheafOfModules.{u} R}
    (s : γ → M.sections) : freeConst (R := R) γ ⟶ M :=
  PresheafOfModules.freeObjDesc
    { app := fun V => ↾fun i => (s i).val V
      naturality := fun {_ _} m => by ext i; exact ((s i).2 m).symm }

/-- `freeConstDesc s` sends the `i`-th standard basis vector over `V` to the value of `s i` at
`V`. -/
@[simp]
theorem freeConstDesc_app_basis {γ : Type u} {M : PresheafOfModules.{u} R} (s : γ → M.sections)
    (V : Cᵒᵖ) (i : γ) :
    (freeConstDesc s).app V (freeConstBasis γ V i) = (s i).val V :=
  ModuleCat.freeDesc_apply (↾fun i => (s i).val V) i

/-- **The morphism out of `freeConst γ` prescribed by a family of global sections carries a
finitely supported family of sections of `R` to the corresponding finite sum of multiples.**
This is `Stacks.PresheafOfModules.freeConstDesc_app_basis` read on an arbitrary family; it is
stated with the `Finsupp` spelling of the sections of `freeConst γ`, which is the spelling the
geometric computations are in. -/
theorem freeConstDesc_app_apply {γ : Type u} {M : PresheafOfModules.{u} R}
    (s : γ → M.sections) (V : Cᵒᵖ) (c : γ →₀ ToType (R.obj V)) :
    (freeConstDesc s).app V c =
      Finsupp.linearCombination (ToType (R.obj V))
        (fun i => PresheafOfModules.sections.eval (s i) V) c := by
  rw [Finsupp.linearCombination_apply]
  rfl

/-- The tautological global section of `freeConst γ` indexed by `i`. -/
noncomputable def freeConstSection {γ : Type u} (i : γ) : (freeConst (R := R) γ).sections :=
  PresheafOfModules.sectionsMk (fun V => freeConstBasis γ V i)
    fun {_ _} m => freeConstBasis_map γ m i

/-- The value of `freeConstSection i` at `V` is the `i`-th standard basis vector. -/
theorem freeConstSection_val {γ : Type u} (i : γ) (V : Cᵒᵖ) :
    (freeConstSection (R := R) i).val V = freeConstBasis γ V i := rfl

/-- On global sections, `freeConstDesc s` sends `freeConstSection i` to `s i`. -/
theorem sectionsMap_freeConstDesc {γ : Type u} {M : PresheafOfModules.{u} R}
    (s : γ → M.sections) (i : γ) :
    PresheafOfModules.sectionsMap (freeConstDesc s) (freeConstSection i) = s i :=
  PresheafOfModules.sections_ext _ _ fun V => freeConstDesc_app_basis s V i

/-- The composite of `freeConstDesc s` with `ψ` is `freeConstDesc` of the images of the global
sections `s i` under `ψ`. -/
theorem freeConstDesc_comp {γ : Type u} {M N : PresheafOfModules.{u} R} (s : γ → M.sections)
    (ψ : M ⟶ N) :
    freeConstDesc s ≫ ψ = freeConstDesc fun i => PresheafOfModules.sectionsMap ψ (s i) :=
  freeConst_hom_ext fun V i =>
    Eq.trans (congrArg (fun x : M.obj V => ψ.app V x) (freeConstDesc_app_basis s V i))
      (freeConstDesc_app_basis (fun i => PresheafOfModules.sectionsMap ψ (s i)) V i).symm

/-- The morphism out of `freeConst γ` prescribed by the tautological global sections is the
identity. -/
theorem freeConstDesc_freeConstSection (γ : Type u) :
    freeConstDesc (fun i : γ => freeConstSection (R := R) i) = 𝟙 (freeConst (R := R) γ) :=
  freeConst_hom_ext fun V i => freeConstDesc_app_basis _ V i

/-- The global section corresponding to `f ≫ ψ` under `unitHomEquiv` is the image under `ψ` of the
global section corresponding to `f`. -/
theorem sectionsMap_unitHomEquiv {M N : PresheafOfModules.{u} R}
    (f : PresheafOfModules.unit R ⟶ M) (ψ : M ⟶ N) :
    PresheafOfModules.sectionsMap ψ (PresheafOfModules.unitHomEquiv M f) =
      PresheafOfModules.unitHomEquiv N (f ≫ ψ) := rfl

/-! ### `freeConst γ` is a coproduct of copies of the unit -/

section Coproduct

variable (γ : Type u) [HasCoproduct fun _ : γ => PresheafOfModules.unit R]

/-- **The free presheaf of modules on a type is the coproduct of copies of the unit indexed by
that type.** -/
noncomputable def freeConstCoprodIso :
    freeConst (R := R) γ ≅ ∐ fun _ : γ => PresheafOfModules.unit R where
  hom := freeConstDesc fun i => PresheafOfModules.unitHomEquiv _
    (Sigma.ι (fun _ : γ => PresheafOfModules.unit R) i)
  inv := Sigma.desc fun i =>
    (PresheafOfModules.unitHomEquiv (freeConst (R := R) γ)).symm (freeConstSection i)
  hom_inv_id := by
    rw [freeConstDesc_comp]
    refine Eq.trans (congrArg freeConstDesc (funext fun i => ?_))
      (freeConstDesc_freeConstSection γ)
    rw [sectionsMap_unitHomEquiv, Sigma.ι_desc]
    exact (PresheafOfModules.unitHomEquiv (freeConst (R := R) γ)).apply_symm_apply _
  inv_hom_id := Sigma.hom_ext _ _ fun i => by
    rw [Category.comp_id, ← Category.assoc, Sigma.ι_desc]
    refine (PresheafOfModules.unitHomEquiv _).injective ?_
    rw [← sectionsMap_unitHomEquiv,
      (PresheafOfModules.unitHomEquiv (freeConst (R := R) γ)).apply_symm_apply]
    exact sectionsMap_freeConstDesc _ i

end Coproduct

/-! ### The symmetric powers -/

variable {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The monomial basis of the sections of `symPow n (freeConst γ)`. -/
noncomputable def basisSymPowFreeConst (γ : Type u) [DecidableEq γ] (n : ℕ) (V : Cᵒᵖ) :
    Module.Basis {d : γ →₀ ℕ | d.degree = n}
      (ToType ((O ⋙ forget₂ _ RingCat).obj V))
      (ToType ((PresheafOfModules.symPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).obj V)) :=
  (SymPow.basisSymmetricPower (freeConstBasis γ V) n).map
    (PresheafOfModules.symPowSections n (freeConst (R := O ⋙ forget₂ _ RingCat) γ) V).symm

/-- The restriction maps of `symPow n (freeConst γ)` send each monomial basis vector to the
monomial basis vector of the same multidegree. -/
theorem basisSymPowFreeConst_map (γ : Type u) [DecidableEq γ] (n : ℕ) {V W : Cᵒᵖ} (m : V ⟶ W)
    (d : {d : γ →₀ ℕ | d.degree = n}) :
    (PresheafOfModules.symPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).map m
      (basisSymPowFreeConst γ n V d) = basisSymPowFreeConst γ n W d := by
  obtain ⟨σ, hσ⟩ := SymPow.exists_prod_ι_eq_coe_basisSymmetricPower_uniform n d
  have hb : ∀ X : Cᵒᵖ, (↑(PresheafOfModules.symPowSections n
        (freeConst (R := O ⋙ forget₂ _ RingCat) γ) X (basisSymPowFreeConst γ n X d)) :
      SymmetricAlgebra (ToType ((O ⋙ forget₂ _ RingCat).obj X))
        (ToType ((freeConst (R := O ⋙ forget₂ _ RingCat) γ).obj X))) =
      ∏ i : Fin n, SymmetricAlgebra.ι _ _ (freeConstBasis γ X (σ i)) := by
    intro X
    rw [basisSymPowFreeConst, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, ← hσ]
  refine (PresheafOfModules.symPowSections n _ W).injective (Subtype.ext ?_)
  rw [PresheafOfModules.symPowSections_map_prod_ι n _ m (fun i => freeConstBasis γ V (σ i)) _
    (hb V), hb W]
  exact Finset.prod_congr rfl fun i _ => by rw [freeConstBasis_map]

/-- Sections of `symPow n (freeConst γ)` over an object, matched with the sections of
`freeConst {d | d.degree = n}`. -/
noncomputable def symPowFreeConstEquiv (γ : Type u) [DecidableEq γ] (n : ℕ) (V : Cᵒᵖ) :
    ToType ((PresheafOfModules.symPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).obj V) ≃ₗ[
      ToType ((O ⋙ forget₂ _ RingCat).obj V)]
      ToType ((freeConst (R := O ⋙ forget₂ _ RingCat) {d : γ →₀ ℕ | d.degree = n}).obj V) :=
  (basisSymPowFreeConst γ n V).equiv (freeConstBasis _ V) (Equiv.refl _)

/-- **The sectionwise symmetric power of a free presheaf of modules is free.** -/
noncomputable def symPowFreeConstIso (γ : Type u) [DecidableEq γ] (n : ℕ) :
    PresheafOfModules.symPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ) ≅
      freeConst (R := O ⋙ forget₂ _ RingCat) {d : γ →₀ ℕ | d.degree = n} :=
  PresheafOfModules.isoMk (fun V => (symPowFreeConstEquiv γ n V).toModuleIso) fun {V W} m =>
    ModuleCat.hom_ext ((basisSymPowFreeConst γ n V).ext fun d => by
      change symPowFreeConstEquiv γ n W ((PresheafOfModules.symPow n
          (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).map m (basisSymPowFreeConst γ n V d)) =
        (freeConst (R := O ⋙ forget₂ _ RingCat) {d : γ →₀ ℕ | d.degree = n}).map m
          (symPowFreeConstEquiv γ n V (basisSymPowFreeConst γ n V d))
      rw [basisSymPowFreeConst_map, symPowFreeConstEquiv, symPowFreeConstEquiv,
        Module.Basis.equiv_apply, Module.Basis.equiv_apply, freeConstBasis_map])

/-! ### The exterior powers -/

/-- A basis of the sections of `extPow n (freeConst γ)`. -/
noncomputable def basisExtPowFreeConst (γ : Type u) [LinearOrder γ] (n : ℕ) (V : Cᵒᵖ) :
    Module.Basis ↥(Set.powersetCard γ n)
      (ToType ((O ⋙ forget₂ _ RingCat).obj V))
      (ToType ((PresheafOfModules.extPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).obj V)) :=
  ((freeConstBasis γ V).exteriorPower n).map
    (PresheafOfModules.extPowSections n (freeConst (R := O ⋙ forget₂ _ RingCat) γ) V).symm

/-- The restriction maps of `extPow n (freeConst γ)` send each basis vector to the basis vector of
the same `n`-element subset. -/
theorem basisExtPowFreeConst_map (γ : Type u) [LinearOrder γ] (n : ℕ) {V W : Cᵒᵖ} (m : V ⟶ W)
    (s : Set.powersetCard γ n) :
    (PresheafOfModules.extPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).map m
      (basisExtPowFreeConst γ n V s) = basisExtPowFreeConst γ n W s := by
  have hb : ∀ X : Cᵒᵖ, (↑(PresheafOfModules.extPowSections n
        (freeConst (R := O ⋙ forget₂ _ RingCat) γ) X (basisExtPowFreeConst γ n X s)) :
      ExteriorAlgebra (ToType ((O ⋙ forget₂ _ RingCat).obj X))
        (ToType ((freeConst (R := O ⋙ forget₂ _ RingCat) γ).obj X))) =
      ExteriorAlgebra.ιMulti _ n
        fun i => freeConstBasis γ X (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
    intro X
    rw [basisExtPowFreeConst, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe]
    rfl
  refine (PresheafOfModules.extPowSections n _ W).injective (Subtype.ext ?_)
  rw [PresheafOfModules.extPowSections_map, hb V, ExteriorAlgebra.mapₛₗ_ιMulti, hb W]
  exact congrArg
    (fun g : Fin n → ToType ((freeConst (R := O ⋙ forget₂ _ RingCat) γ).obj W) =>
      ExteriorAlgebra.ιMulti _ n g)
    (funext fun i => by rw [PresheafOfModules.restrictₛₗ_apply, freeConstBasis_map])

/-- Sections of `extPow n (freeConst γ)` over an object, matched with the sections of
`freeConst (Set.powersetCard γ n)`. -/
noncomputable def extPowFreeConstEquiv (γ : Type u) [LinearOrder γ] (n : ℕ) (V : Cᵒᵖ) :
    ToType ((PresheafOfModules.extPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).obj V) ≃ₗ[
      ToType ((O ⋙ forget₂ _ RingCat).obj V)]
      ToType ((freeConst (R := O ⋙ forget₂ _ RingCat) ↥(Set.powersetCard γ n)).obj V) :=
  (basisExtPowFreeConst γ n V).equiv (freeConstBasis _ V) (Equiv.refl _)

/-- **The sectionwise exterior power of a free presheaf of modules is free.** -/
noncomputable def extPowFreeConstIso (γ : Type u) [LinearOrder γ] (n : ℕ) :
    PresheafOfModules.extPow n (freeConst (R := O ⋙ forget₂ _ RingCat) γ) ≅
      freeConst (R := O ⋙ forget₂ _ RingCat) ↥(Set.powersetCard γ n) :=
  PresheafOfModules.isoMk (fun V => (extPowFreeConstEquiv γ n V).toModuleIso) fun {V W} m =>
    ModuleCat.hom_ext ((basisExtPowFreeConst γ n V).ext fun s => by
      change extPowFreeConstEquiv γ n W ((PresheafOfModules.extPow n
          (freeConst (R := O ⋙ forget₂ _ RingCat) γ)).map m (basisExtPowFreeConst γ n V s)) =
        (freeConst (R := O ⋙ forget₂ _ RingCat) ↥(Set.powersetCard γ n)).map m
          (extPowFreeConstEquiv γ n V (basisExtPowFreeConst γ n V s))
      rw [basisExtPowFreeConst_map, extPowFreeConstEquiv, extPowFreeConstEquiv,
        Module.Basis.equiv_apply, Module.Basis.equiv_apply, freeConstBasis_map])

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

open CategoryTheory.Sheaf Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Sheafifying the unit presheaf of modules gives the unit sheaf of modules. -/
noncomputable def sheafifyUnitPresheafIso :
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
        (PresheafOfModules.unit (toRingCat J Osharp).obj) ≅
      _root_.SheafOfModules.unit (toRingCat J Osharp) :=
  _root_.SheafOfModules.sheafifyValIso J (_root_.SheafOfModules.unit (toRingCat J Osharp))

/-- **Sheafifying the free presheaf of modules on a type gives the free sheaf of modules on that
type**, for an arbitrary index type. -/
noncomputable def sheafifyFreeConstIso (γ : Type u) :
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
        (freeConst (R := (toRingCat J Osharp).obj) γ) ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) γ :=
  let F := PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)
  have _ : PreservesColimitsOfSize.{u, u} F :=
    (PresheafOfModules.sheafificationAdjunction
      (toRingCatMap J (𝟙 Osharp.obj))).leftAdjoint_preservesColimits
  (F.mapIso (freeConstCoprodIso γ)).trans
    ((PreservesCoproduct.iso F fun _ : γ => PresheafOfModules.unit (toRingCat J Osharp).obj).trans
      (Sigma.mapIso fun _ : γ => sheafifyUnitPresheafIso J))

/-! ### The symmetric and exterior powers of a free sheaf of modules -/

/-- The degree-`n` symmetric power of a package of algebras over `free γ`, identified with the
sheafification of the presheaf of sectionwise symmetric powers of `freeConst γ`. -/
noncomputable def symmetricPowerSheafifyFreeConstIso (γ : Type u) (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) γ)) :
    A.symmetricPower n ≅ (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
      (PresheafOfModules.symPow n (freeConst (R := (toRingCat J Osharp).obj) γ)) :=
  _root_.SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraIso
    (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J
      (sheafifyFreeConstIso J γ).symm A)
    (_root_.SheafOfModules.tensorExteriorSymmetricAlgebras J (𝟙 Osharp.obj)
      (freeConst (R := (toRingCat J Osharp).obj) γ)) (n : ℤ)

/-- The exterior analogue of `Stacks.SheafOfModules.symmetricPowerSheafifyFreeConstIso`. -/
noncomputable def exteriorPowerSheafifyFreeConstIso (γ : Type u) (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) γ)) :
    A.exteriorPower n ≅ (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
      (PresheafOfModules.extPow n (freeConst (R := (toRingCat J Osharp).obj) γ)) :=
  _root_.SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso
    (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J
      (sheafifyFreeConstIso J γ).symm A)
    (_root_.SheafOfModules.tensorExteriorSymmetricAlgebras J (𝟙 Osharp.obj)
      (freeConst (R := (toRingCat J Osharp).obj) γ)) (n : ℤ)

/-- **The degree-`n` symmetric power of a free sheaf of modules on an arbitrary index type is
free on the degree-`n` multidegrees.** -/
noncomputable def symmetricPowerFreeIsoAnyIndex (γ : Type u) [DecidableEq γ] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) γ)) :
    A.symmetricPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) {d : γ →₀ ℕ | d.degree = n} :=
  (symmetricPowerSheafifyFreeConstIso J γ n A).trans
    (((PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).mapIso
      (symPowFreeConstIso (O := Osharp.obj) γ n)).trans
        (sheafifyFreeConstIso J {d : γ →₀ ℕ | d.degree = n}))

/-- **The degree-`n` exterior power of a free sheaf of modules on an arbitrary index type is
free on the `n`-element subsets of the index type.** -/
noncomputable def exteriorPowerFreeIsoAnyIndex (γ : Type u) [LinearOrder γ] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) γ)) :
    A.exteriorPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) ↥(Set.powersetCard γ n) :=
  (exteriorPowerSheafifyFreeConstIso J γ n A).trans
    (((PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).mapIso
      (extPowFreeConstIso (O := Osharp.obj) γ n)).trans
        (sheafifyFreeConstIso J ↥(Set.powersetCard γ n)))

variable {F : _root_.SheafOfModules.{u} (toRingCat J Osharp)}

/-- `Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` for a sheaf of modules merely
*isomorphic* to a free one. -/
noncomputable def symmetricPowerFreeIsoOfIsoAnyIndex (γ : Type u) [DecidableEq γ] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    (e : F ≅ _root_.SheafOfModules.free (R := toRingCat J Osharp) γ) :
    A.symmetricPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) {d : γ →₀ ℕ | d.degree = n} :=
  symmetricPowerFreeIsoAnyIndex J γ n
    (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J e A)

/-- `Stacks.SheafOfModules.exteriorPowerFreeIsoAnyIndex` for a sheaf of modules merely
*isomorphic* to a free one. -/
noncomputable def exteriorPowerFreeIsoOfIsoAnyIndex (γ : Type u) [LinearOrder γ] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    (e : F ≅ _root_.SheafOfModules.free (R := toRingCat J Osharp) γ) :
    A.exteriorPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) ↥(Set.powersetCard γ n) :=
  exteriorPowerFreeIsoAnyIndex J γ n
    (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J e A)

/-- **Every symmetric power of a sheaf of modules isomorphic to a free one is free**, with no
finiteness hypothesis on the index type. -/
theorem exists_nonempty_iso_free_symmetricPower (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (γ : Type u)
    (e : F ≅ _root_.SheafOfModules.free (R := toRingCat J Osharp) γ) :
    ∃ K : Type u, Nonempty (A.symmetricPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) K) := by
  classical
  exact ⟨{d : γ →₀ ℕ | d.degree = n}, ⟨symmetricPowerFreeIsoOfIsoAnyIndex J γ n A e⟩⟩

/-- **Every exterior power of a sheaf of modules isomorphic to a free one is free**, with no
finiteness hypothesis on the index type. The linear order Mathlib's exterior basis needs is
supplied by well-ordering the index type, so it does not appear in the statement. -/
theorem exists_nonempty_iso_free_exteriorPower (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (γ : Type u)
    (e : F ≅ _root_.SheafOfModules.free (R := toRingCat J Osharp) γ) :
    ∃ K : Type u, Nonempty (A.exteriorPower n ≅
      _root_.SheafOfModules.free (R := toRingCat J Osharp) K) := by
  let _ : LinearOrder γ := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨Set.powersetCard γ n, ⟨exteriorPowerFreeIsoOfIsoAnyIndex J γ n A e⟩⟩

end Stacks.SheafOfModules

end
