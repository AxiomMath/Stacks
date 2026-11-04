module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulTopCohomologySheaf
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product

/-!
# Sections over an affine open of the top cohomology sheaf of the Koszul complex

Let `X` be a scheme, let `a_1, …, a_r` be global sections of `𝒪_X` and let `ℱ` be a
quasi-coherent `𝒪_X`-module. `KoszulTopCohomologySheaf.lean` identifies the cohomology sheaf of
the Koszul complex `koszulPowerComplexOn X f ℱ n` in its top degree `r` with the cokernel of the
map `ℱ^r ⟶ ℱ`, `(x_i) ↦ ∑_i a_i^{n+1} x_i`. This file reads that identification **on the sections
over an affine open**: for `U ⊆ X` affine,

  `Γ(U, H^r(ℱ ⊗ K(𝒪_X, a_1^{n+1}, …, a_r^{n+1}))) = Γ(U, ℱ) / (a_1^{n+1}, …, a_r^{n+1}) Γ(U, ℱ)`,

the right-hand side being the module-level Koszul cohomology in the same degree, by
`AlgebraicGeometry.RingedSite.koszulGeneratorsMap` on the module `Γ(U, ℱ)`.

Two things make this work and both are quasi-coherence, used where the source of
[Stacks, Tag 0A0K] uses the equivalence `D(A) = D_{QCoh}(𝒪_X)` on an affine. First, taking
sections over an affine open is **right exact** on quasi-coherent modules, so it computes the
cokernel: the surjectivity of the sections of a quotient projection is
`AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen` and the exactness of the sections of
the defining sequence is `Stacks.Algebraization.affine_sections_cokernel_exact`. Second, the
source of the generator map is a finite product of copies of `ℱ`, which is again quasi-coherent
by `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi` — needed because the
right-exactness statement is about a morphism between two quasi-coherent modules.

The scheme enters through its small Zariski site: `koszulPowerComplexOn` is a construction on a
ringed site, and `Stacks.SheafOfModules.opensRingedSite X.sheaf` is the site of open subsets of
`X` carrying `𝒪_X`. Its sheaf of rings and `X.ringCatSheaf` are the same term, so a sheaf of
modules on one is a sheaf of modules on the other with no transport; the bridge lemmas below
record that.

## Main results

* `Stacks.Algebraization.cokernelEvaluationIsoOfIsAffineOpen` — **taking sections over an affine
  open computes the cokernel of a morphism of quasi-coherent modules.** This is
  `Stacks.Algebraization.affine_evaluation_preservesCokernel` at an arbitrary affine open of an
  arbitrary scheme rather than at `⊤` on an affine scheme, and it is stated as the isomorphism
  rather than as a `PreservesColimit` instance because the two presentations `X.Modules` and
  `SheafOfModules X.ringCatSheaf` of the ambient category carry separately declared instances,
  which instance resolution does not identify.
* `Stacks.Algebraization.homologyTopIsoCokernel` — the cohomology of a cochain complex in the
  degree above which the complex vanishes is the cokernel of the last differential.
* `Stacks.Algebraization.koszulSingle_comp_koszulGeneratorsMap` and
  `Stacks.Algebraization.koszulValue_koszulGenExp` — the generator map
  `AlgebraicGeometry.RingedSite.koszulGeneratorsMap` really is `(x_i) ↦ ∑_i f_i^{n+1} x_i`: its
  composite with the inclusion of the `i`-th factor is multiplication by the monomial of the
  `i`-th exponent vector, and that monomial is `f_i^{n+1}`.
* `Stacks.Algebraization.evaluation_koszulPowerFunctorOn_map_apply` and
  `Stacks.Algebraization.evaluationKoszulPowerComplexIso` — **the complex of sections over an
  open set is the module-level Koszul complex**: the alternating Čech complex of the constant
  system `S ↦ Γ(U, ℱ)` whose transition map along `S ⊆ T` is multiplication by
  `∏_{i ∈ T ∖ S} (a_i|_U)^{n+1}`.
* `Stacks.Algebraization.isQuasicoherent_X_koszulPowerComplexOn` — the terms of the Koszul
  complex with coefficients in a quasi-coherent module are quasi-coherent, each being a product
  of copies of that module over a finite index set.
* `Stacks.Algebraization.koszulTopCohomologySectionsIso` — **taking sections over an affine open
  commutes with the cohomology of the Koszul complex in its top degree.** With the two previous
  items this is the identification of the top cohomology sheaf, on an affine open, with the
  module-level Koszul cohomology in the same degree; with
  `AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap` of
  `KoszulTopCohomologySheaf.lean` it reads the quotient `ℱ/(a_1^{n+1}, …, a_r^{n+1})ℱ` on those
  sections.

## Implementation notes

The statements about the Koszul complex are at the index `r - 1 + 1` rather than `r`, as in
`KoszulTopCohomologySheaf.lean`, so that the degree is syntactically a successor; the two are
equal and `AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap` is the version
reindexed to `r`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Sections over an affine open compute a cokernel -/

/-- **The sections over an affine open of a cokernel of quasi-coherent modules are the cokernel
of the sections.** On those sections the morphism is exact onto the sections of its cokernel,
`Stacks.Algebraization.affine_sections_cokernel_exact`, and the quotient projection is surjective
there, `AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen`; that is exactly the cokernel
cofork in modules. -/
def cokernelEvaluationIsoOfIsAffineOpen {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (U : X.affineOpens) :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).obj
        (cokernel (C := X.Modules) φ) ≅
      cokernel ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map φ) :=
  haveI : (cokernel (C := X.Modules) φ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel φ
  IsColimit.coconePointUniqueUpToIso
    (ModuleCat.isColimitCokernelCofork
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map φ)
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
        (cokernel.π (C := X.Modules) φ))
      (affine_sections_cokernel_exact φ U)
      (surjective_app_of_epi_of_isAffineOpen (cokernel.π (C := X.Modules) φ) U))
    (colimit.isColimit _)

/-! ### The sections of the generator map -/

section Generators

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (n : ℕ) (M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

open scoped IsMulCommutative

/-- The section of the `r`-fold product of copies of `ℱ` supported in the `i`-th factor. -/
def koszulSingle (i : Fin r) : M ⟶ (∏ᶜ fun _ : Fin r => M) :=
  Pi.lift fun j => if j = i then 𝟙 M else 0

/-- Composing the `i`-th inclusion with the generator map is multiplication by `f_i^{n+1}`: all
other components of the inclusion vanish. -/
theorem koszulSingle_comp_koszulGeneratorsMap (i : Fin r) :
    koszulSingle X M i ≫ RingedSite.koszulGeneratorsMap X f n M =
      RingedSite.koszulScalarOn X f (RingedSite.koszulGenExp n i) M := by
  rw [RingedSite.koszulGeneratorsMap, Preadditive.comp_sum]
  refine Eq.trans (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_) ?_
  · intro j _ hj
    rw [← Category.assoc, koszulSingle, Pi.lift_π, ite_eq_right hj, zero_comp]
  · rw [← Category.assoc, koszulSingle, Pi.lift_π, ite_eq_left rfl, Category.id_comp]

/-- The monomial attached to the exponent vector of the `i`-th generator is `f_i^{n+1}`: every
other factor carries the exponent zero. -/
theorem koszulValue_koszulGenExp (U : X.Cᵒᵖ) (i : Fin r) :
    RingedSite.koszulValue X f (RingedSite.koszulGenExp n i) U =
      RingedSite.globalSectionVal (f i) U ^ (n + 1) := by
  rw [RingedSite.koszulValue]
  refine Finset.prod_eq_single_of_mem i (Finset.mem_univ i) ?_ |>.trans ?_
  · intro j _ hj
    rw [show RingedSite.koszulGenExp n i j = 0 from ite_eq_right hj, pow_zero]
  · rw [show RingedSite.koszulGenExp n i i = n + 1 from ite_eq_left rfl]

end Generators

/-! ### Top cohomology of a cochain complex as a cokernel -/

/-- **The cohomology of a cochain complex in the degree above which it vanishes is the cokernel
of the last differential.** -/
def homologyTopIsoCokernel {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] (C : CochainComplex 𝒜 ℤ)
    (p : ℤ) (h : IsZero (C.X (p + 1 + 1))) :
    C.homology (p + 1) ≅ cokernel (C.d p (p + 1)) :=
  C.isoHomologyι (p + 1) (p + 1 + 1) (CochainComplex.next ℤ _)
      (h.eq_of_tgt (C.d (p + 1) (p + 1 + 1)) 0) ≪≫
    IsColimit.coconePointUniqueUpToIso
      (C.opcyclesIsCokernel (i := p) (j := p + 1) ((ComplexShape.up ℤ).prev_eq' rfl))
      (colimit.isColimit _)

/-- An additive functor carries a zero object to a zero object. -/
theorem isZero_map_obj {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Preadditive 𝒜] [Preadditive ℬ]
    (G : 𝒜 ⥤ ℬ) [G.Additive] {A : 𝒜} (h : IsZero A) : IsZero (G.obj A) :=
  G.map_isZero h

/-! ### Sections of the top cohomology sheaf of the Koszul complex -/

section Koszul

variable (Y : Scheme.{u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (n : ℕ) (F : Y.Modules)

/-- Taking sections over an open set is an additive functor. -/
instance additive_evaluation (U : Y.Opens) :
    (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).Additive :=
  ⟨by intros; rfl⟩

/-- The value over an open set of a global section of `𝒪_X`, read in `Γ(X, U)`: this is
`AlgebraicGeometry.RingedSite.globalSectionVal` with its type given in the scheme's own spelling,
so that the ring structure of `Γ(X, U)` applies to it. -/
def globalSectionOver (s : Presheaf.globalSections
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
    (U : Y.Opens) : Γ(Y, U) :=
  RingedSite.globalSectionVal s (op U)

/-- The value over an open set of the monomial `∏_i f_i^{e_i}`, read in `Γ(X, U)`. -/
def koszulValueOver (e : Fin r → ℕ) (U : Y.Opens) : Γ(Y, U) :=
  RingedSite.koszulValue (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f e (op U)

/-- The monomial of the `i`-th generator is `f_i^{n+1}`. -/
theorem koszulValueOver_koszulGenExp (U : Y.Opens) (i : Fin r) :
    koszulValueOver Y f (RingedSite.koszulGenExp n i) U = globalSectionOver Y (f i) U ^ (n + 1) :=
  koszulValue_koszulGenExp (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f n (op U) i

/-- **The system of sections over an open set is the module-level Koszul system**: it is the
constant system `S ↦ Γ(U, ℱ)` whose transition map along `S ⊆ T` is multiplication by the
monomial `∏_{i ∈ T ∖ S} (f_i|_U)^{n+1}` in the restricted sections. -/
theorem evaluation_koszulPowerFunctorOn_map_apply (U : Y.Opens) {S T : Finset (Fin r)}
    (g : S ⟶ T) (x : Γ(F, U)) :
    ((RingedSite.koszulPowerFunctorOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n ⋙
        _root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).map g).hom x =
      koszulValueOver Y f (RingedSite.koszulExp n S T) U • x :=
  rfl

/-- **The complex of sections over an open set is the Koszul complex of the sections**: the
alternating Čech complex of the system of sections, which by
`Stacks.Algebraization.evaluation_koszulPowerFunctorOn_map_apply` is the Koszul complex on
`(f_1|_U)^{n+1}, …, (f_r|_U)^{n+1}` with coefficients in the `Γ(X, U)`-module `Γ(U, ℱ)`. -/
def evaluationKoszulPowerComplexIso (U : Y.Opens) :
    (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (RingedSite.koszulPowerComplexOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n)) ≅
      AlternatingCech.complex (RingedSite.koszulPowerFunctorOn
        (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n ⋙
          _root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)) :=
  AlternatingCech.mapComplexIso _ _

/-- The terms of the Koszul complex with coefficients in a quasi-coherent module are
quasi-coherent: each is a product, over a finite index set, of copies of that module. -/
theorem isQuasicoherent_X_koszulPowerComplexOn [F.IsQuasicoherent] (p : ℤ) :
    ((RingedSite.koszulPowerComplexOn
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).X p).IsQuasicoherent := by
  classical
  have : Finite (AlternatingCech.Idx r p) := Subtype.finite
  have : Fintype (AlternatingCech.Idx r p) := Fintype.ofFinite _
  have : HasFiniteBiproducts Y.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let g : AlternatingCech.Idx r p → Y.Modules := fun _ => F
  exact show (∏ᶜ g).IsQuasicoherent from
    (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((biproduct.isoCoproduct g).symm ≪≫ biproduct.isoProduct g)
      (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
        (Discrete.functor g) fun _ => (inferInstance : F.IsQuasicoherent))

/-- The term of the Koszul complex just above the top degree is a product over an empty index
set, hence a zero object. -/
theorem isZero_X_koszulPowerComplexOn_of_gt {p : ℤ} (hp : (r : ℤ) < p) :
    IsZero ((RingedSite.koszulPowerComplexOn
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).X p) := by
  rw [IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun S => (AlternatingCech.isEmpty_idx_of_lt (r := r) hp).elim S

/-- **Taking sections over an affine open commutes with the top cohomology of the Koszul complex
with coefficients in a quasi-coherent module.**

Both sides are the cokernel of the sections of the last differential: on the left because the
top cohomology sheaf is the cokernel of that differential and because taking sections over an
affine open computes a cokernel of quasi-coherent modules; on the right because the sections of
the complex again vanish above the top degree. Composed with
`CategoryTheory.AlternatingCech.mapComplexIso`, which identifies the complex of sections with the
alternating Čech complex of the system of sections — the Koszul complex on the restrictions
`(a_i|_U)^{n+1}` with coefficients in `Γ(U, ℱ)` — this is the identification of the cohomology
sheaves of the Koszul complex, on an affine open, with the module-level Koszul cohomology. -/
def koszulTopCohomologySectionsIso [F.IsQuasicoherent] (U : Y.affineOpens) :
    (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).obj
        ((RingedSite.koszulPowerComplexOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).homology ((r : ℤ) - 1 + 1)) ≅
      (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingedSite.koszulPowerComplexOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n)).homology ((r : ℤ) - 1 + 1) := by
  haveI hq₁ : ((RingedSite.koszulPowerComplexOn
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).X ((r : ℤ) - 1)).IsQuasicoherent :=
    isQuasicoherent_X_koszulPowerComplexOn Y f n F ((r : ℤ) - 1)
  haveI hq₂ : ((RingedSite.koszulPowerComplexOn
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).X
        ((r : ℤ) - 1 + 1)).IsQuasicoherent :=
    isQuasicoherent_X_koszulPowerComplexOn Y f n F ((r : ℤ) - 1 + 1)
  have hzero := isZero_X_koszulPowerComplexOn_of_gt Y f n F
    (p := (r : ℤ) - 1 + 1 + 1) (by omega)
  exact
    (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).mapIso
        (homologyTopIsoCokernel (RingedSite.koszulPowerComplexOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n) ((r : ℤ) - 1) hzero) ≪≫
      @cokernelEvaluationIsoOfIsAffineOpen _ _ _ hq₁ hq₂
        ((RingedSite.koszulPowerComplexOn
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n).d
            ((r : ℤ) - 1) ((r : ℤ) - 1 + 1)) U ≪≫
      (homologyTopIsoCokernel
        (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (RingedSite.koszulPowerComplexOn
              (Stacks.SheafOfModules.opensRingedSite Y.sheaf) f F n))
        ((r : ℤ) - 1)
        (isZero_map_obj (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) hzero)).symm

end Koszul

end Stacks.Algebraization
