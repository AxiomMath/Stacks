module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.LinearAlgebra.SymmetricPower.Free
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.Flat.Lazard
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.TensorAlgebra.Colimit
import StacksCore.Tactic.StacksAttribute

/-!
# Symmetric and exterior powers of module diagrams

The sectionwise symmetric and exterior powers of a diagram of modules over a constant ring,
the multiplication `F ⊗ Sym^k F → Sym^{k+1} F`, bounds for the derived tensor product, and the
flatness and projectivity of symmetric and exterior powers (via Lazard's theorem).

This file is one part of `SymmetricPowerVanishing`, which imports all of them.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Stacks.ChaoticSite

universe u v w


/-- **The Eilenberg–Zilber comparison of Tag 08QD**, as a hypothesis on the coefficient ring
`B` and the universe of the modules: for two degreewise flat simplicial `B`-modules the Moore
complex of the degreewise tensor product is quasi-isomorphic to the tensor product of the Moore
complexes. -/
def FlatEilenbergZilber.{t, s} (B : Type s) [CommRing B] : Prop :=
  ∀ M N : SimplicialObject (ModuleCat.{max t s} B),
    (∀ n : SimplexCategoryᵒᵖ, Module.Flat B (M.obj n)) →
    (∀ n : SimplexCategoryᵒᵖ, Module.Flat B (N.obj n)) →
    ∃ f : (alternatingFaceMapComplex (ModuleCat.{max t s} B)).obj
        (MonoidalCategory.tensorObj M N) ⟶
      HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex (ModuleCat.{max t s} B)).obj M)
        ((alternatingFaceMapComplex (ModuleCat.{max t s} B)).obj N),
      QuasiIso f

attribute [local instance] HasDerivedCategory.standard

/-- The map of symmetric algebras induced by the identity of `M` is the identity. -/
theorem symAlgMap_id (B : Type w) [CommRing B]
    (M : Type*) [AddCommGroup M] [Module B M] :
    SymPow.symAlgMap (LinearMap.id : M →ₗ[B] M) = AlgHom.id B _ := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [SymPow.symAlgMap]

/-- The map of symmetric algebras induced by a composite `g ∘ f` is the composite of the induced
maps. -/
theorem symAlgMap_comp (B : Type w) [CommRing B]
    {M N P : Type*} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]
    (f : M →ₗ[B] N) (g : N →ₗ[B] P) :
    SymPow.symAlgMap (g.comp f) = (SymPow.symAlgMap g).comp (SymPow.symAlgMap f) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [SymPow.symAlgMap]

/-- The canonical map `M → Sym_B(M)` is injective. -/
theorem symAlg_iota_inj (B : Type w) [CommRing B]
    (M : Type*) [AddCommGroup M] [Module B M] :
    Function.Injective (SymmetricAlgebra.ι B M) := by
  let : Module Bᵐᵒᵖ M := Module.compHom M
    (RingHom.fromOpposite (RingHom.id B) (by intro x y; exact Commute.all x y))
  let : IsCentralScalar B M := ⟨fun b m => rfl⟩
  let f : SymmetricAlgebra B M →ₐ[B] TrivSqZeroExt B M :=
    SymmetricAlgebra.lift (TrivSqZeroExt.inrHom B M)
  have hleft : Function.LeftInverse
      ((TrivSqZeroExt.sndHom B M).comp f.toLinearMap) (SymmetricAlgebra.ι B M) := by
    intro x
    change (TrivSqZeroExt.sndHom B M) (f (SymmetricAlgebra.ι B M x)) = x
    simp [f, TrivSqZeroExt.sndHom_apply]
  exact hleft.injective

/-- The linear map `M → Sym¹_B(M)` sending `m` to its image in the symmetric algebra. -/
noncomputable def symPowOneMap (B : Type w) [CommRing B]
    (M : Type*) [AddCommGroup M] [Module B M] :
    M →ₗ[B] SymPow.symmetricPower 1 B M where
  toFun m := ⟨SymmetricAlgebra.ι B M m, by
    rw [SymPow.symmetricPower, pow_one]
    exact ⟨m, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

/-- The linear isomorphism `M ≃ Sym¹_B(M)`. -/
noncomputable def symPowOneEquiv (B : Type w) [CommRing B]
    (M : Type*) [AddCommGroup M] [Module B M] :
    M ≃ₗ[B] SymPow.symmetricPower 1 B M := by
  apply LinearEquiv.ofBijective (symPowOneMap B M)
  constructor
  · intro x y h
    apply symAlg_iota_inj B M
    exact congrArg Subtype.val h
  · rintro ⟨x, hx⟩
    rw [SymPow.symmetricPower, pow_one] at hx
    rcases hx with ⟨m, rfl⟩
    exact ⟨m, rfl⟩

/-- The isomorphism `M ≃ Sym¹_B(M)` is natural: `Sym¹(f)` corresponds to `f`. -/
theorem symPowOneEquiv_symMap (B : Type w) [CommRing B]
    {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (m : M) :
    SymPow.symMap 1 f (symPowOneEquiv B M m) = symPowOneEquiv B N (f m) := by
  apply Subtype.ext
  change SymPow.symAlgMap f (SymmetricAlgebra.ι B M m) = _
  exact SymPow.symAlgMap_ι f m

/-- Sectionwise symmetric powers of a module diagram over a constant ring. -/
public noncomputable def symmetricPowerDiagram
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k : ℕ) :
    Cᵒᵖ ⥤ ModuleCat.{max u v w} B where
  obj X := ModuleCat.of B (SymPow.symmetricPower k B (F.obj X))
  map f := ModuleCat.ofHom (SymPow.symMap k (F.map f).hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show (F.map (𝟙 X)).hom = LinearMap.id from congrArg ModuleCat.Hom.hom (F.map_id X)]
    change SymPow.symMap k LinearMap.id x = x
    apply Subtype.ext
    change SymPow.symAlgMap LinearMap.id (x : SymPow.symmetricPower k B (F.obj X)) =
      (x : SymmetricAlgebra B (F.obj X))
    rw [symAlgMap_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show (F.map (f ≫ g)).hom = (F.map g).hom.comp (F.map f).hom from
      congrArg ModuleCat.Hom.hom (F.map_comp f g)]
    change SymPow.symMap k ((F.map g).hom.comp (F.map f).hom) x =
      SymPow.symMap k (F.map g).hom (SymPow.symMap k (F.map f).hom x)
    apply Subtype.ext
    change SymPow.symAlgMap ((F.map g).hom.comp (F.map f).hom) x =
      SymPow.symAlgMap (F.map g).hom (SymPow.symAlgMap (F.map f).hom x)
    rw [symAlgMap_comp]
    rfl

/-- **`Sym¹_{B̲}(F) = F`.** The first sectionwise symmetric power of a diagram of modules is the
diagram itself: in each degree `Sym¹_B(M) = M` by `Stacks.ChaoticSite.symPowOneEquiv`, and that
identification is natural because `Sym¹` of a linear map is the map. -/
public noncomputable def symPowOneDiagramIso
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) :
    F ≅ symmetricPowerDiagram C B F 1 := by
  refine NatIso.ofComponents (fun X => (symPowOneEquiv B (F.obj X)).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change symPowOneEquiv B (F.obj Y) ((F.map f).hom x) =
    SymPow.symMap 1 (F.map f).hom (symPowOneEquiv B (F.obj X) x)
  exact (symPowOneEquiv_symMap B (F.map f).hom x).symm

/-- `Sym^k` is functorial: `Sym^k(g) (Sym^k(f) x) = Sym^k(g ∘ f) x`. -/
theorem symMap_comp_apply
    {B M N P : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (k : ℕ)
    (f : M →ₗ[B] N) (g : N →ₗ[B] P) (x : SymPow.symmetricPower k B M) :
    SymPow.symMap k g (SymPow.symMap k f x) = SymPow.symMap k (g.comp f) x := by
  apply Subtype.ext
  exact (congrArg (fun h : SymmetricAlgebra B M →ₐ[B] SymmetricAlgebra B P => h x)
    (symAlgMap_comp B f g)).symm

/-- For `k > 0`, the `k`th symmetric power of the zero map is zero. -/
theorem symMap_zero_of_pos
    {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (k : ℕ) (hk : 0 < k) :
    SymPow.symMap k (0 : M →ₗ[B] N) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h : (SymPow.symmetricPower k B M).map
      (SymPow.symAlgMap (0 : M →ₗ[B] N)).toLinearMap = ⊥ := by
    rw [SymPow.symmetricPower, Submodule.map_pow]
    have hgen : (LinearMap.range (SymmetricAlgebra.ι B M)).map
        (SymPow.symAlgMap (0 : M →ₗ[B] N)).toLinearMap = ⊥ := by
      apply le_antisymm _ bot_le
      rintro y ⟨z, ⟨m, rfl⟩, rfl⟩
      simp [SymPow.symAlgMap_ι]
    rw [hgen]
    exact Submodule.bot_pow (Nat.ne_of_gt hk)
  have hx : SymPow.symAlgMap (0 : M →ₗ[B] N) x ∈
      (SymPow.symmetricPower k B M).map
        (SymPow.symAlgMap (0 : M →ₗ[B] N)).toLinearMap := ⟨x, x.property, rfl⟩
  rw [h] at hx
  exact hx

/-- If `f g : M → N` have a common section `s`, then `f - g` factors as `f ∘ t` with `g ∘ t = 0`. -/
private theorem exists_comp_eq_sub_of_common_section
    {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f g : M →ₗ[B] N) (s : N →ₗ[B] M)
    (hf : f.comp s = LinearMap.id) (hg : g.comp s = LinearMap.id) :
    ∃ t : M →ₗ[B] M, f.comp t = f - g ∧ g.comp t = 0 :=
  ⟨LinearMap.id - s.comp g, by
    rw [LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hf, LinearMap.id_comp],
    by rw [LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hg, LinearMap.id_comp,
      sub_self]⟩

/-- Let `f g : M → N` have a common section `s`, and suppose `f - g` is surjective. Then for
`k > 0` the map `Sym^k(f) - Sym^k(g)` is surjective. -/
theorem symMap_sub_surjective_of_common_section
    {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f g : M →ₗ[B] N) (s : N →ₗ[B] M)
    (hf : f.comp s = LinearMap.id) (hg : g.comp s = LinearMap.id)
    (hfg : Function.Surjective (f - g)) (k : ℕ) (hk : 0 < k) :
    Function.Surjective (SymPow.symMap k f - SymPow.symMap k g) := by
  obtain ⟨t, hft, hgt⟩ := exists_comp_eq_sub_of_common_section f g s hf hg
  intro x
  obtain ⟨y, hy⟩ := SymPow.symMap_surjective k (f - g) hfg x
  refine ⟨SymPow.symMap k t y, ?_⟩
  simp only [LinearMap.sub_apply, symMap_comp_apply, hft, hgt,
    symMap_zero_of_pos k hk, LinearMap.zero_apply, sub_zero, hy]

/-- The zeroth homology of the Moore complex of a simplicial module `X` vanishes if and only if
`d₀ - d₁ : X₁ → X₀` is surjective. -/
theorem alternatingFaceMap_homology_zero_iff
    {B : Type w} [CommRing B] (X : SimplicialObject (ModuleCat.{u} B)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj X).homology 0) ↔
      Function.Surjective ((X.δ (0 : Fin 2)).hom - (X.δ (1 : Fin 2)).hom) := by
  let D := (alternatingFaceMapComplex (ModuleCat.{u} B)).obj X
  change IsZero (D.homology 0) ↔ _
  rw [← D.exactAt_iff_isZero_homology,
    D.exactAt_iff' 1 0 ((ComplexShape.down ℕ).next 0) (by simp) rfl,
    ShortComplex.exact_iff_epi _ (by
      change D.d 0 _ = 0
      exact D.shape _ _ (by simp)),
    ModuleCat.epi_iff_surjective]
  change Function.Surjective ((AlternatingFaceMapComplex.obj X).d 1 0).hom ↔ _
  rw [AlternatingFaceMapComplex.obj_d_eq X 0]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- For `k > 0`, the `k`th exterior power of the zero map is zero. -/
theorem exteriorPower_map_zero_of_pos
    {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (k : ℕ) (hk : 0 < k) :
    exteriorPower.map k (0 : M →ₗ[B] N) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change exteriorPower.map k (0 : M →ₗ[B] N) (exteriorPower.ιMulti B k m) = 0
  rw [exteriorPower.map_apply_ιMulti]
  exact (exteriorPower.ιMulti B k).map_coord_zero ⟨0, hk⟩ rfl

/-- Let `f g : M → N` have a common section `s`, and suppose `f - g` is surjective. Then for
`k > 0` the map `∧^k(f) - ∧^k(g)` is surjective. -/
theorem exteriorPower_map_sub_surjective_of_common_section
    {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f g : M →ₗ[B] N) (s : N →ₗ[B] M)
    (hf : f.comp s = LinearMap.id) (hg : g.comp s = LinearMap.id)
    (hfg : Function.Surjective (f - g)) (k : ℕ) (hk : 0 < k) :
    Function.Surjective (exteriorPower.map k f - exteriorPower.map k g) := by
  obtain ⟨t, hft, hgt⟩ := exists_comp_eq_sub_of_common_section f g s hf hg
  intro x
  obtain ⟨y, hy⟩ := exteriorPower.map_surjective (n := k) hfg x
  refine ⟨exteriorPower.map k t y, ?_⟩
  change exteriorPower.map k f (exteriorPower.map k t y) -
    exteriorPower.map k g (exteriorPower.map k t y) = x
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hft,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp, hgt,
    exteriorPower_map_zero_of_pos k hk, LinearMap.zero_apply, sub_zero, hy]

/-- The sectionwise `k`th exterior power `∧^k F` of a diagram of modules `F`. -/
noncomputable def exteriorPowerDiagram
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k : ℕ) :
    Cᵒᵖ ⥤ ModuleCat.{max u v w} B where
  obj X := ModuleCat.of B (⋀[B]^k (F.obj X))
  map f := ModuleCat.ofHom (exteriorPower.map k (F.map f).hom)
  map_id X := by
    apply ModuleCat.hom_ext
    rw [show (F.map (𝟙 X)).hom = LinearMap.id from congrArg ModuleCat.Hom.hom (F.map_id X)]
    exact exteriorPower.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    rw [show (F.map (f ≫ g)).hom = (F.map g).hom.comp (F.map f).hom from
      congrArg ModuleCat.Hom.hom (F.map_comp f g)]
    exact exteriorPower.map_comp _ _

/-- If the Moore complex of `G` evaluated on the cosimplicial object `U` has vanishing `H₀`, then
so does that of `∧^k G` for every `k > 0`. -/
theorem exteriorPowerDiagram_homology_zero
    (C : Type u) [SmallCategory C] (B : Type w) [CommRing B]
    (U : CosimplicialObject C) (G : Cᵒᵖ ⥤ ModuleCat.{max u w} B)
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ G)).homology 0)) (k : ℕ) (hk : 0 < k) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ exteriorPowerDiagram C B G k)).homology 0) := by
  let X : SimplicialObject (ModuleCat.{max u w} B) := U.op ⋙ G
  apply (alternatingFaceMap_homology_zero_iff _).mpr
  apply exteriorPower_map_sub_surjective_of_common_section
    (X.δ (0 : Fin 2)).hom (X.δ (1 : Fin 2)).hom (X.σ (0 : Fin 1)).hom
    _ _ ((alternatingFaceMap_homology_zero_iff X).mp h₀) k hk
  · exact congrArg ModuleCat.Hom.hom (X.δ_comp_σ_self (i := (0 : Fin 1)))
  · exact congrArg ModuleCat.Hom.hom (X.δ_comp_σ_succ (i := (0 : Fin 1)))

/-- The multiplication map `M ⊗ Sym^k M → Sym^{k+1} M` is surjective. -/
theorem symmetricPower_multiplication_surjective
    {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] (k : ℕ) :
    Function.Surjective (SymPow.symMulMap k (LinearMap.id : M →ₗ[B] M)) := by
  intro x
  have hx : (x : SymmetricAlgebra B M) ∈
      SymPow.rangeSubmodule (LinearMap.id : M →ₗ[B] M) * SymPow.symmetricPower k B M := by
    simpa only [SymPow.rangeSubmodule, LinearMap.comp_id, SymPow.symmetricPower,
      pow_succ'] using x.property
  rw [← SymPow.range_symMulMap] at hx
  obtain ⟨y, ⟨z, rfl⟩, hz⟩ := hx
  exact ⟨z, Subtype.ext hz⟩

/-- The sectionwise multiplication `F ⊗ Sym^k F → Sym^{k+1} F`, as a natural transformation of
diagrams of modules. -/
noncomputable def symmetricPowerMultiplication
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k : ℕ) :
    F.prod' (symmetricPowerDiagram C B F k) ⋙
      Functor.uncurry.obj (CochainComplex.DerivedTensor.moduleTensor B) ⟶
        symmetricPowerDiagram C B F (k + 1) where
  app X := ModuleCat.ofHom (SymPow.symMulMap k LinearMap.id)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change SymPow.symmetricPower k B (F.obj X) at y
    apply Subtype.ext
    change SymmetricAlgebra.ι B (F.obj Y) ((F.map f).hom x) *
      SymPow.symAlgMap (F.map f).hom y =
      SymPow.symAlgMap (F.map f).hom (SymmetricAlgebra.ι B (F.obj X) x * y)
    rw [map_mul, SymPow.symAlgMap_ι]

/-- The multiplication `F ⊗ Sym^k F → Sym^{k+1} F` is an epimorphism. -/
theorem symmetricPowerMultiplication_epi
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k : ℕ) :
    Epi (symmetricPowerMultiplication C B F k) := by
  have (X : Cᵒᵖ) : Epi ((symmetricPowerMultiplication C B F k).app X) :=
    (ModuleCat.epi_iff_surjective _).mpr (symmetricPower_multiplication_surjective k)
  exact NatTrans.epi_of_epi_app _

/-- If `P` is strictly concentrated in degrees `≤ a` and `Q` in degrees `≤ b`, then their tensor
product complex is strictly concentrated in degrees `≤ a + b`. -/
theorem tensorComplex_isStrictlyLE
    {B : Type w} [CommRing B]
    (P Q : CochainComplex (ModuleCat.{max u w} B) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] :
    (CochainComplex.DerivedTensor.tensorComplex P Q).IsStrictlyLE (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((CochainComplex.DerivedTensor.moduleTensor B).obj (P.X p)).obj
      (Q.X q)) := by
    by_cases hp : a < p
    · exact ((CochainComplex.DerivedTensor.moduleTensor B).flip.obj (Q.X q)).map_isZero
        (P.isZero_of_isStrictlyLE a p hp)
    · exact ((CochainComplex.DerivedTensor.moduleTensor B).obj (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyLE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- An object of the derived category of `B`-modules with cohomology in degrees `≤ a` is
isomorphic to a complex of projective modules strictly concentrated in degrees `≤ a`. -/
theorem exists_projectiveRepresentative_of_isLE
    {B : Type w} [CommRing B] (K : DerivedCategory (ModuleCat.{max u w} B))
    (a : ℤ) [K.IsLE a] :
    ∃ P : CochainComplex (ModuleCat.{max u w} B) ℤ,
      P.IsStrictlyLE a ∧ (∀ i, Projective (P.X i)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K a
  obtain ⟨P, -⟩ := ProjectiveResolutionLemma.exists_epiResolution_of_strictlyLE a L hL
  have : QuasiIso P.α := P.quasiIso
  exact ⟨P.complex, P.boundedAbove, P.projective,
    ⟨e ≪≫ (asIso (DerivedCategory.Q.map P.α)).symm⟩⟩

/-- If `K` has cohomology in degrees `≤ a` and `L` in degrees `≤ b`, then the derived tensor
product `K ⊗ᴸ L` has cohomology in degrees `≤ a + b`. -/
theorem derivedTensor_isLE
    {B : Type w} [CommRing B]
    (T : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{w, u} B)
    (K L : DerivedCategory (ModuleCat.{max u w} B))
    (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    ((T.tensor.obj K).obj L).IsLE (a + b) := by
  obtain ⟨P, hP, hPproj, ⟨eP⟩⟩ := exists_projectiveRepresentative_of_isLE K a
  obtain ⟨Q, hQ, hQproj, ⟨eQ⟩⟩ := exists_projectiveRepresentative_of_isLE L b
  have := hP
  have := hQ
  have hPflat : CochainComplex.DerivedTensor.IsKFlat P := by
    apply (CochainComplex.DerivedTensor.isKFlat_iff_kFlat P).mpr
    have (i : ℤ) : Module.Flat B (P.X i) := by
      have := hPproj i
      infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat P a
  have hQflat : CochainComplex.DerivedTensor.IsKFlat Q := by
    apply (CochainComplex.DerivedTensor.isKFlat_iff_kFlat Q).mpr
    have (i : ℤ) : Module.Flat B (Q.X i) := by
      have := hQproj i
      infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat Q b
  have := tensorComplex_isStrictlyLE P Q a b
  let e : (T.tensor.obj K).obj L ≅
      DerivedCategory.Q.obj (CochainComplex.DerivedTensor.tensorComplex P Q) :=
    (T.tensor.mapIso eP).app L ≪≫ (T.tensor.obj _).mapIso eQ ≪≫
      T.comparison P Q hPflat hQflat
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (a + b)

/-- The projection `Sym_B(M) → Sym^k_B(M)` onto the homogeneous component of degree `k`. -/
noncomputable def symmetricPowerProjection
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (k : ℕ) :
    SymmetricAlgebra B M →ₗ[B] SymPow.symmetricPower k B M where
  toFun x := ⟨(SymPow.degreeMap x).coeff k, SymPow.coeff_degreeMap_mem x k⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' b x := by
    apply Subtype.ext
    simp

/-- The projection onto `Sym^k_B(M)` restricts to the identity on `Sym^k_B(M)`. -/
theorem symmetricPowerProjection_subtype
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (k : ℕ) :
    (symmetricPowerProjection B M k).comp (SymPow.symmetricPower k B M).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (SymPow.degreeMap (x : SymmetricAlgebra B M)).coeff k = x
  rw [SymPow.degreeMap_eq_of_mem (R := B) (M := M) k
    (x : SymmetricAlgebra B M) x.property]
  simp

/-- **Lazard's theorem.** A flat `R`-module is isomorphic to a direct limit, over a nonempty
directed preorder, of finite free `R`-modules. -/
lemma flat_exists_directLimit_finiteFree
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Flat R M] :
    ∃ (ι : Type (max u v)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
      (_ : Nonempty ι) (_ : DecidableEq ι) (G : ι → Type (max u v))
      (_ : (i : ι) → AddCommGroup (G i)) (_ : (i : ι) → Module R (G i))
      (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
      (_ : DirectedSystem G fun i j h => f i j h),
      (∀ i, Module.Free R (G i)) ∧ (∀ i, Module.Finite R (G i)) ∧
        Nonempty (Module.DirectLimit G f ≃ₗ[R] M) := by
  let S := ULift.{v} R
  let : Module S (ULift.{u} M) := Module.compHom _ ULift.ringEquiv.toRingHom
  have : Module.Flat S (ULift.{u} M) := Module.Flat.ulift_left_iff.mpr inferInstance
  obtain ⟨ι, hpre, hdir, hne, hdec, G, hag, hmod, f, hds, hfree, hfinite, ⟨e⟩⟩ :=
    flat_exists_directLimit_free_finite (R := S) (ULift.{u} M)
  let (i : ι) : Module R (G i) := Module.compHom _ ULift.ringEquiv.symm.toRingHom
  let g (i j : ι) (h : i ≤ j) : G i →ₗ[R] G j :=
    { __ := f i j h
      map_smul' := fun r x => (f i j h).map_smul (ULift.up r) x }
  have hgds : DirectedSystem G (fun i j h => g i j h) :=
    { map_self := fun {i} x => DirectedSystem.map_self (f := fun i j h => f i j h) x
      map_map := fun {i j k} hij hjk x => DirectedSystem.map_map
        (f := fun i j h => f i j h) hij hjk x }
  let e' : DirectLimit G g ≃ₗ[R] M :=
    { toFun := fun x => (e ((Module.DirectLimit.linearEquiv G f).symm x)).down
      invFun := fun x => (Module.DirectLimit.linearEquiv G f) (e.symm (ULift.up x))
      left_inv := by
        intro x
        change (Module.DirectLimit.linearEquiv G f)
          (e.symm (e ((Module.DirectLimit.linearEquiv G f).symm x))) = x
        simp
      right_inv := by intro x; simp
      map_add' := DirectLimit.induction₂ g (fun i x y => by
        rw [DirectLimit.add_def]
        change (e (Module.DirectLimit.of S ι G f i (x + y))).down = _
        rw [map_add, map_add]
        rfl)
      map_smul' := fun r => DirectLimit.induction g (fun i x => by
        rw [DirectLimit.smul_def]
        change (e (Module.DirectLimit.of S ι G f i ((ULift.up r : S) • x))).down = _
        rw [map_smul, map_smul]
        rfl) }
  refine ⟨ι, hpre, hdir, hne, hdec, G, hag, inferInstance, g, hgds, ?_, ?_,
    ⟨(Module.DirectLimit.linearEquiv G g).trans e'⟩⟩
  · intro i
    have := hfree i
    have : RingHomInvPair (ULift.ringEquiv : S ≃+* R).toRingHom
        (ULift.ringEquiv : S ≃+* R).symm.toRingHom := ⟨by ext x; rfl, by ext x; rfl⟩
    have : RingHomInvPair (ULift.ringEquiv : S ≃+* R).symm.toRingHom
        (ULift.ringEquiv : S ≃+* R).toRingHom := ⟨by ext x; rfl, by ext x; rfl⟩
    let eG : G i ≃ₛₗ[(ULift.ringEquiv : S ≃+* R).toRingHom] G i :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Free.of_equiv eG
  · intro i
    have := hfinite i
    let t : G i →ₛₗ[(ULift.ringEquiv : S ≃+* R).toRingHom] G i :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_surjective t Function.surjective_id

/-- A linear isomorphism `M ≃ N` induces an algebra isomorphism `Sym_R(M) ≃ Sym_R(N)`. -/
def symmetricAlgebraEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (symmetricAlgebraMap e.toLinearMap)
    (symmetricAlgebraMap e.symm.toLinearMap)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      simp [symmetricAlgebraMap_ι])
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      simp [symmetricAlgebraMap_ι])

/-- The direct limit of a directed system of flat algebras over `R` is a flat `R`-module. -/
private theorem flat_directLimit_of_algebra {R : Type*} [CommRing R]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (H : ι → Type*) [∀ i, Ring (H i)] [∀ i, Algebra R (H i)] [∀ i, Module.Flat R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₐ[R] H j) [DirectedSystem H (fun i j h => g i j h)] :
    Module.Flat R (DirectLimit H g) := by
  classical
  let g' (i j : ι) (h : i ≤ j) := (g i j h).toLinearMap
  have hgds : DirectedSystem H (fun i j h => g' i j h) :=
    { map_self := fun {i} x => DirectedSystem.map_self (f := fun i j h => g i j h) x
      map_map := fun {i j k} hij hjk x => DirectedSystem.map_map
        (f := fun i j h => g i j h) hij hjk x }
  have : Module.Flat R (Module.DirectLimit H g') := Module.Flat.directLimit
  let e₁ : DirectLimit H g' ≃ₗ[R] DirectLimit H g :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := DirectLimit.induction₂ g' (fun i x y => by
        simp only [id_eq]
        rw [DirectLimit.add_def]
        exact (DirectLimit.add_def (f := g) i x y).symm)
      map_smul' := fun r => DirectLimit.induction g' (fun i x => by
        simp only [id_eq, RingHom.id_apply, DirectLimit.smul_def]
        with_unfolding_all rfl) }
  exact Module.Flat.of_linearEquiv ((Module.DirectLimit.linearEquiv H g').trans e₁).symm

/-- The symmetric algebra of a flat module is flat. -/
lemma symmetricAlgebra_flat (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat R (SymmetricAlgebra R M) := by
  obtain ⟨ι, hpre, hdir, hne, hdec, G, hag, hmod, f, hds, hfree, -, ⟨e⟩⟩ :=
    flat_exists_directLimit_finiteFree R M
  have (i : ι) : Module.Flat R (SymmetricAlgebra R (G i)) := by
    have := hfree i
    infer_instance
  have : Module.Flat R (SymmetricColim f) := flat_directLimit_of_algebra _ (symmetricTrans f)
  exact Module.Flat.of_linearEquiv
    (((symmetricAlgebraEquiv e.symm).trans (SymmetricAlgebra.equivDirectLimit f)).toLinearEquiv)

/-- A linear isomorphism `M ≃ N` induces an algebra isomorphism `∧_R(M) ≃ ∧_R(N)`. -/
def exteriorAlgebraEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
    (ExteriorAlgebra.map e.symm.toLinearMap)
    (by
      apply ExteriorAlgebra.hom_ext
      ext x
      simp)
    (by
      apply ExteriorAlgebra.hom_ext
      ext x
      simp)

/-- The exterior algebra of a flat module is flat. -/
lemma exteriorAlgebra_flat (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat R (ExteriorAlgebra R M) := by
  obtain ⟨ι, hpre, hdir, hne, hdec, G, hag, hmod, f, hds, hfree, -, ⟨e⟩⟩ :=
    flat_exists_directLimit_finiteFree R M
  have (i : ι) : Module.Flat R (ExteriorAlgebra R (G i)) := by
    have := hfree i
    have : Module.Flat R (⨁ n : ℕ, ⋀[R]^n (G i)) := inferInstance
    exact Module.Flat.of_linearEquiv
      (DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[R]^n (G i)))
  have : Module.Flat R (ExteriorColim f) := flat_directLimit_of_algebra _ (exteriorTrans f)
  exact Module.Flat.of_linearEquiv
    (((exteriorAlgebraEquiv e.symm).trans (ExteriorAlgebra.equivDirectLimit f)).toLinearEquiv)

/-- Every exterior power of a flat module is flat. -/
lemma exteriorPower_flat (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (k : ℕ) :
    Module.Flat R (⋀[R]^k M) := by
  have := exteriorAlgebra_flat R M
  apply Module.Flat.of_retract (Submodule.subtype (⋀[R]^k M))
    ((DFinsupp.lapply k).comp
      (DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[R]^n M)).toLinearMap)
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, Submodule.subtype_apply, DirectSum.decomposeLinearEquiv_apply_coe]
  simp

/-- Every symmetric power of a flat module is flat. -/
lemma symmetricPower_flat (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (k : ℕ) :
    Module.Flat R (SymPow.symmetricPower k R M) := by
  have := symmetricAlgebra_flat R M
  exact Module.Flat.of_retract
    (SymPow.symmetricPower k R M).subtype
    (symmetricPowerProjection R M k)
    (symmetricPowerProjection_subtype R M k)

/-- Every symmetric power of a free module is projective. -/
theorem symmetricPower_projective_of_free
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Free B M] (k : ℕ) : Module.Projective B (SymPow.symmetricPower k B M) :=
  Module.Projective.of_split (SymPow.symmetricPower k B M).subtype
    (symmetricPowerProjection B M k) (symmetricPowerProjection_subtype B M k)

/-- Every symmetric power of a projective module is projective. -/
theorem symmetricPower_projective
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] (k : ℕ) : Module.Projective B (SymPow.symmetricPower k B M) := by
  obtain ⟨N, _, _, hN, i, r, hr⟩ :=
    (Module.Projective.iff_split (R := B) (P := M)).mp inferInstance
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup B
  have := hN
  have := symmetricPower_projective_of_free B N k
  apply Module.Projective.of_split (SymPow.symMap k i) (SymPow.symMap k r)
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, symMap_comp_apply, hr]
  apply Subtype.ext
  change SymPow.symAlgMap LinearMap.id (x : SymmetricAlgebra B M) = x
  rw [symAlgMap_id]
  rfl

end Stacks.ChaoticSite

end
