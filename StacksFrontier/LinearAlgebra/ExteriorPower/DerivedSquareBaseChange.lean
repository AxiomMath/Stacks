module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquare
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.Projective
public import StacksFrontier.LinearAlgebra.ExteriorPower.SquareFiltration
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso
public import StacksFrontier.Homology.ExtendScalars.Localization
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Support
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import StacksFrontier.Algebra.Homology.Resolution.Existence
import all StacksFrontier.Homology.KFlat.FreeResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change and reduction of the derived exterior square

Let `A` be a commutative ring and `M` an `A`-module, and let `LᵢΛ²_A(M) = Hᵢ(s(⋀²_A P))` be the
derived exterior square computed from a simplicial projective resolution `P` of `M`
(`Stacks.DerivedSquare.homology`). This file proves three properties of it.

* **Flat base change.** For a flat ring map `f : A → B`, the simplicial module `B ⊗_A P` is a
  simplicial projective resolution of `B ⊗_A M`, `⋀²_B(B ⊗_A Pₙ) ≅ B ⊗_A ⋀²_A(Pₙ)` naturally, and
  `B ⊗_A -` commutes with homology. Hence `B ⊗_A LᵢΛ²_A(M) ≅ LᵢΛ²_B(B ⊗_A M)`. This
  isomorphism is natural in `M`, compatible with the comparison isomorphisms between
  resolutions, trivial for the identity of `A`, and satisfies the cocycle condition for a
  composite `A → B → C` of flat maps. For a localization it reads
  `T⁻¹ LᵢΛ²_A(M) ≅ LᵢΛ²_{T⁻¹A}(T⁻¹A ⊗_A M)`.
* **Reduction modulo a regular element.** Let `r ∈ A` be a nonzerodivisor on `A` and on `M`.
  Then `Torᵢ^A(A ⧸ (r), M) = 0` for `i > 0`, so `P ⧸ rP` is a simplicial projective resolution
  of `M ⧸ rM` over `A ⧸ (r)`. Degreewise, `0 → ⋀²Pₙ →(r) ⋀²Pₙ → ⋀²_{A ⧸ (r)}(Pₙ ⧸ rPₙ) → 0` is
  short exact, because `⋀²Pₙ` is projective and `⋀²Pₙ ⧸ r ≅ ⋀²_{A ⧸ (r)}(Pₙ ⧸ rPₙ)`. This gives
  a long exact sequence
  `⋯ → LᵢΛ²_A(M) →(r) LᵢΛ²_A(M) → LᵢΛ²_{A ⧸ (r)}(M ⧸ rM) → Lᵢ₋₁Λ²_A(M) → ⋯`.
* **Finiteness and support.** Over a Noetherian ring, `LᵢΛ²_A(M)` is finitely generated when
  `M` is (compute it with a resolution by finite free modules), and for every `M`,
  `Supp LᵢΛ²_A(M) ⊆ Supp M` (localize at a prime outside `Supp M` and use flat base change).

The base change statements are instances of the comparison of simplicial derived functors along
a change of categories, `Stacks.SimplicialProjectiveResolution.mapDerivedHomologyIso`: for
functors `F : C ⥤ D`, `F' : C' ⥤ D'`, `G : C ⥤ C'` and `H : D ⥤ D'`, with `H` additive and
preserving homology, an isomorphism `F ⋙ H ≅ G ⋙ F'` induces `H(LᵢF(X)) ≅ LᵢF'(G(X))` whenever
`G` carries a simplicial projective resolution of `X` to one of `G(X)`, naturally in `X`,
transitively for pasted squares, naturally in the pair `(G, H)`, and trivially for the identity
square.

## Main definitions

* `Stacks.SimplicialProjectiveResolution.extendScalars` and
  `Stacks.SimplicialProjectiveResolution.reduce`: the resolutions `B ⊗_A P` and `P ⧸ rP`.
* `ModuleCat.exteriorPower.extendScalarsIso`: `⋀ⁿ` commutes with extension of scalars.
* `Stacks.DerivedSquare.baseChangeIso`: `B ⊗_A LᵢΛ²_A(M) ≅ LᵢΛ²_B(B ⊗_A M)`, and
  `Stacks.DerivedSquare.localizationIso` its localization case.
* `Stacks.DerivedSquare.reductionMap` and `Stacks.DerivedSquare.reductionδ`: the maps of the long
  exact sequence of the reduction modulo `r`.

## Main results

* `Stacks.DerivedSquare.map_derivedMap_comp_baseChangeIso_hom`,
  `Stacks.DerivedSquare.map_derivedIso_hom_comp_baseChangeIso_hom`,
  `Stacks.DerivedSquare.baseChangeIso_id_hom` and `Stacks.DerivedSquare.baseChangeIso_comp_hom`:
  naturality, compatibility with the comparison isomorphisms, the identity and the cocycle
  condition for flat base change.
* `Stacks.SimplicialProjectiveResolution.quasiIso_mapπ_reduction`: `P ⧸ rP` resolves `M ⧸ rM`.
* `Stacks.DerivedSquare.exact_smul_reductionMap`,
  `Stacks.DerivedSquare.exact_reductionMap_reductionδ` and
  `Stacks.DerivedSquare.exact_reductionδ_smul`: exactness of the long exact sequence at each spot.
* `Stacks.DerivedSquare.finite_homology` and `Stacks.DerivedSquare.support_homology_subset`.

## Implementation notes

The base change `B ⊗_A -` is `ModuleCat.extendScalars f` for a ring map `f`, and the reduction
`- ⧸ r` is extension of scalars along `A → A ⧸ (r)`. The comparison `⋀ⁿ_B(B ⊗_A N) ≅ B ⊗_A ⋀ⁿ_A N`
is `ExteriorAlgebra.exteriorPowerBaseChange` for the algebra structure `f.toAlgebra`, composed
with the identity of the underlying types, since the `B`-module structure of
`ModuleCat.extendScalars` agrees with that of the tensor product only after unfolding.

The long exact sequence of the reduction is one of `A`-modules: its third terms are the
`A ⧸ (r)`-modules `LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)` regarded as `A`-modules. Exactness is stated as
exactness of the underlying maps.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open scoped TensorProduct ChangeOfRings

universe v u v' u' v'' u''

/-! ### Exterior powers and extension of scalars -/

namespace ModuleCat.exteriorPower

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- **Exterior powers commute with extension of scalars**, as a linear equivalence
`B ⊗_A ⋀ⁿ_A N ≃ ⋀ⁿ_B (B ⊗_A N)` of the objects of `ModuleCat B`. This is
`ExteriorAlgebra.exteriorPowerBaseChange` for the algebra structure `f.toAlgebra`. -/
def extendScalarsEquiv (N : ModuleCat.{u} A) (n : ℕ) :
    (extendScalars f).obj ((functor A n).obj N) ≃ₗ[B]
      (functor B n).obj ((extendScalars f).obj N) :=
  letI := f.toAlgebra
  let e : ∀ X : ModuleCat.{u} A, (extendScalars f).obj X ≃ₗ[B] B ⊗[A] X := fun _ =>
    LinearEquiv.refl B _
  ((e (ModuleCat.of A (⋀[A]^n N))).trans (ExteriorAlgebra.exteriorPowerBaseChange A B N n)).trans
    (_root_.exteriorPower.mapEquiv (e N).symm n)

/-- The equivalence `extendScalarsEquiv` carries `b ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to
`b • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ))`. -/
lemma extendScalarsEquiv_tmul_ιMulti (N : ModuleCat.{u} A) (n : ℕ) (b : B) (v : Fin n → N) :
    extendScalarsEquiv f N n (b ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v) =
      b • _root_.exteriorPower.ιMulti B n (M := (extendScalars f).obj N)
        fun i => (1 : B) ⊗ₜ[A, f] v i := by
  let _ : Algebra A B := f.toAlgebra
  let e : ∀ X : ModuleCat.{u} A, (extendScalars f).obj X ≃ₗ[B] B ⊗[A] X := fun _ =>
    LinearEquiv.refl B _
  have h : e (ModuleCat.of A (⋀[A]^n N)) (b ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v) =
      b ⊗ₜ[A] _root_.exteriorPower.ιMulti A n v := rfl
  change _root_.exteriorPower.mapEquiv (e N).symm n
    (ExteriorAlgebra.exteriorPowerBaseChange A B N n (e (ModuleCat.of A (⋀[A]^n N))
      (b ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v))) = _
  rw [h, ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, map_smul,
    _root_.exteriorPower.mapEquiv_apply, _root_.exteriorPower.map_apply_ιMulti]
  rfl

/-- Two morphisms out of `B ⊗_A ⋀ⁿ_A N` agree as soon as they agree on the elements
`1 ⊗ (m₁ ∧ ⋯ ∧ mₙ)`. -/
lemma extendScalars_hom_ext {N : ModuleCat.{u} A} {n : ℕ} {Z : ModuleCat.{u} B}
    {φ ψ : (extendScalars f).obj ((functor A n).obj N) ⟶ Z}
    (h : ∀ v : Fin n → N, φ.hom ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v) =
      ψ.hom ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v)) : φ = ψ := by
  apply ((extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.exteriorPower.hom_ext
  ext v
  exact h v

/-- **Exterior powers commute with extension of scalars**, naturally:
`B ⊗_A ⋀ⁿ_A N ≅ ⋀ⁿ_B (B ⊗_A N)`. -/
def extendScalarsIso (n : ℕ) :
    functor A n ⋙ extendScalars f ≅ extendScalars f ⋙ functor B n :=
  NatIso.ofComponents (fun N => (extendScalarsEquiv f N n).toModuleIso) fun {N N'} g => by
    refine extendScalars_hom_ext f fun v => ?_
    have h1 : ((extendScalars f).map ((functor A n).map g)).hom
        ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v) =
          (1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n (g.hom ∘ v) :=
      (ExtendScalars.map_tmul f ((functor A n).map g) 1 _).trans
        (congrArg _ (ModuleCat.exteriorPower.map_mk g v))
    have h2 : ∀ i, ((extendScalars f).map g).hom ((1 : B) ⊗ₜ[A, f] v i) =
        (1 : B) ⊗ₜ[A, f] g.hom (v i) := fun i => ExtendScalars.map_tmul f g 1 (v i)
    have h3 := extendScalarsEquiv_tmul_ιMulti f N' n 1 (g.hom ∘ v)
    have h4 := extendScalarsEquiv_tmul_ιMulti f N n 1 v
    change extendScalarsEquiv f N' n (((extendScalars f).map ((functor A n).map g)).hom
        ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v)) =
      ((functor B n).map ((extendScalars f).map g)).hom
        (extendScalarsEquiv f N n ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v))
    refine (congrArg _ h1).trans (h3.trans (Eq.trans ?_ (congrArg _ h4.symm)))
    exact (congrArg (fun x => (1 : B) • x) ((congrArg _ (funext h2)).symm.trans
      (ModuleCat.exteriorPower.map_mk ((extendScalars f).map g) _).symm)).trans
        (map_smul _ _ _).symm

/-- The comparison `extendScalarsIso` carries `b ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to
`b • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ))`. -/
lemma extendScalarsIso_hom_app_tmul_ιMulti (n : ℕ) (N : ModuleCat.{u} A) (b : B)
    (v : Fin n → N) :
    ((extendScalarsIso f n).hom.app N).hom (b ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v) =
      b • _root_.exteriorPower.ιMulti B n (M := (extendScalars f).obj N)
        fun i => (1 : B) ⊗ₜ[A, f] v i :=
  extendScalarsEquiv_tmul_ιMulti f N n b v

/-- The comparison `extendScalarsIso` for the identity ring map is the identity, under the
identifications `ModuleCat.extendScalarsId`. -/
lemma extendScalarsId_hom_app_eq (n : ℕ) (N : ModuleCat.{u} A) :
    (extendScalarsId A).hom.app ((functor A n).obj N) =
      (extendScalarsIso (RingHom.id A) n).hom.app N ≫
        (functor A n).map ((extendScalarsId A).hom.app N) := by
  refine extendScalars_hom_ext (RingHom.id A) fun v => ?_
  have a := extendScalarsId_hom_app_one_tmul ((functor A n).obj N)
    (_root_.exteriorPower.ιMulti A n v)
  have b := extendScalarsEquiv_tmul_ιMulti (RingHom.id A) N n 1 v
  have c := fun i => extendScalarsId_hom_app_one_tmul N (v i)
  have d := ModuleCat.exteriorPower.map_mk ((extendScalarsId A).hom.app N)
    (fun i => ((1 : A) ⊗ₜ[A, RingHom.id A] v i : (extendScalars (RingHom.id A)).obj N))
  refine a.trans (Eq.trans ?_ (congrArg ((functor A n).map ((extendScalarsId A).hom.app N)).hom
    b.symm))
  refine Eq.trans ?_ (map_smul _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun x : (functor A n).obj N => (1 : A) • x) d.symm)
  refine (one_smul A _).symm.trans (congrArg (fun x : (functor A n).obj N => (1 : A) • x) ?_)
  exact congrArg (_root_.exteriorPower.ιMulti A n) (funext c).symm

/-- **Transitivity of `extendScalarsIso`.** For ring maps `f : A → B` and `g : B → C`, the
comparison for `g ∘ f` is the composite of the comparisons for `f` and `g`, under the
identifications `ModuleCat.extendScalarsComp`. -/
lemma extendScalarsComp_hom_app_comp {C : Type u} [CommRing C] (g : B →+* C) (n : ℕ)
    (N : ModuleCat.{u} A) :
    (extendScalarsComp f g).hom.app ((functor A n).obj N) ≫
        (extendScalars g).map ((extendScalarsIso f n).hom.app N) ≫
          (extendScalarsIso g n).hom.app ((extendScalars f).obj N) =
      (extendScalarsIso (g.comp f) n).hom.app N ≫
        (functor C n).map ((extendScalarsComp f g).hom.app N) := by
  refine extendScalars_hom_ext (g.comp f) fun v => ?_
  let w : Fin n → (extendScalars f).obj N := fun i => (1 : B) ⊗ₜ[A, f] v i
  have a1 := extendScalarsComp_hom_app_one_tmul f g ((functor A n).obj N)
    (_root_.exteriorPower.ιMulti A n v)
  have a2 := ExtendScalars.map_tmul g ((extendScalarsIso f n).hom.app N) 1
    ((1 : B) ⊗ₜ[A, f] _root_.exteriorPower.ιMulti A n v)
  have a2' := (extendScalarsIso_hom_app_tmul_ιMulti f n N 1 v).trans (one_smul _ _)
  have a3 := extendScalarsIso_hom_app_tmul_ιMulti g n ((extendScalars f).obj N) 1 w
  have b1 := extendScalarsIso_hom_app_tmul_ιMulti (g.comp f) n N 1 v
  have s1 := ((congrArg ((extendScalars g).map ((extendScalarsIso f n).hom.app N)).hom a1).trans
    a2).trans (congrArg (fun z : (functor B n).obj ((extendScalars f).obj N) =>
      (1 : C) ⊗ₜ[B, g] z) a2')
  have b2 := fun i => extendScalarsComp_hom_app_one_tmul f g N (v i)
  have b3 := ModuleCat.exteriorPower.map_mk ((extendScalarsComp f g).hom.app N)
    (fun i => ((1 : C) ⊗ₜ[A, g.comp f] v i : (extendScalars (g.comp f)).obj N))
  have s2 := (congrArg ((extendScalarsIso g n).hom.app ((extendScalars f).obj N)).hom s1).trans a3
  have s3 := congrArg ((functor C n).map ((extendScalarsComp f g).hom.app N)).hom b1
  refine s2.trans (Eq.trans ?_ s3.symm)
  refine Eq.trans ?_
    (map_smul ((functor C n).map ((extendScalarsComp f g).hom.app N)).hom (1 : C) _).symm
  exact congrArg (fun x : (functor C n).obj ((extendScalars g).obj
    ((extendScalars f).obj N)) => (1 : C) • x)
      ((congrArg (_root_.exteriorPower.ιMulti C n) (funext b2)).symm.trans b3.symm)

end ModuleCat.exteriorPower

/-- Extension of scalars preserves projective objects: it is left adjoint to restriction of
scalars, which preserves epimorphisms. -/
@[ega "III 6.3.8" "Projectivity clause"]
instance ModuleCat.preservesProjectiveObjects_extendScalars {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
  ⟨fun {P} hP => (ModuleCat.extendRestrictScalarsAdj f).map_projective P hP⟩

/-! ### Flat base change of the derived exterior square -/

namespace Stacks

namespace SimplicialProjectiveResolution

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
  {M : ModuleCat.{u} A}

/-- The base change `B ⊗_A P` of a simplicial projective resolution `P` of `M` along a flat ring
map `f : A → B`: a simplicial projective resolution of `B ⊗_A M`. -/
abbrev extendScalars (P : SimplicialProjectiveResolution M) :
    SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M) :=
  P.mapOfQuasiIso (ModuleCat.extendScalars f)
    (fun n => (ModuleCat.extendScalars f).projective_obj (P.obj _⦋n⦌))
    (haveI := extendScalars_preservesHomology_of_flat.{u, u} f hf; inferInstance)

end SimplicialProjectiveResolution

namespace DerivedSquare

open SimplicialProjectiveResolution

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
  {M N : ModuleCat.{u} A}

/-- **Flat base change for the derived exterior square.** For a flat ring map `f : A → B`, a
simplicial projective resolution `P` of an `A`-module `M` and a simplicial projective resolution
`Q` of `B ⊗_A M`, `B ⊗_A LᵢΛ²_A(M) ≅ LᵢΛ²_B(B ⊗_A M)`: `B ⊗_A P` is a resolution of `B ⊗_A M`,
`⋀²_B(B ⊗_A Pₙ) ≅ B ⊗_A ⋀²_A(Pₙ)`, and `B ⊗_A -` commutes with homology. -/
def baseChangeIso (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M)) (i : ℕ) :
    (ModuleCat.extendScalars f).obj (homology P i) ≅ homology Q i :=
  haveI := extendScalars_preservesHomology_of_flat.{u, u} f hf
  mapDerivedHomologyIso (ModuleCat.exteriorPower.extendScalarsIso f 2) P _ _ i ≪≫
    derivedIso _ (P.extendScalars f hf) Q i

/-- **Naturality of flat base change** in the module, for the maps induced on derived exterior
squares. -/
@[reassoc]
theorem map_derivedMap_comp_baseChangeIso_hom (g : M ⟶ N)
    (P : SimplicialProjectiveResolution M) (P' : SimplicialProjectiveResolution N)
    (Q : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M))
    (Q' : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj N)) (i : ℕ) :
    (ModuleCat.extendScalars f).map (derivedMap (exteriorSquare A) g P P' i) ≫
        (baseChangeIso f hf P' Q' i).hom =
      (baseChangeIso f hf P Q i).hom ≫
        derivedMap (exteriorSquare B) ((ModuleCat.extendScalars f).map g) Q Q' i := by
  have := extendScalars_preservesHomology_of_flat.{u, u} f hf
  simp only [baseChangeIso, Iso.trans_hom, derivedIso_hom]
  rw [map_derivedMap_comp_mapDerivedHomologyIso_hom_assoc, Category.assoc, derivedMap_comp,
    derivedMap_comp, Category.comp_id, Category.id_comp]

/-- Flat base change is compatible with the comparison isomorphisms between resolutions. -/
@[reassoc]
theorem map_derivedIso_hom_comp_baseChangeIso_hom (P P' : SimplicialProjectiveResolution M)
    (Q Q' : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M)) (i : ℕ) :
    (ModuleCat.extendScalars f).map (derivedIso (exteriorSquare A) P P' i).hom ≫
        (baseChangeIso f hf P' Q' i).hom =
      (baseChangeIso f hf P Q i).hom ≫ (derivedIso (exteriorSquare B) Q Q' i).hom := by
  rw [derivedIso_hom, map_derivedMap_comp_baseChangeIso_hom, derivedIso_hom,
    CategoryTheory.Functor.map_id]

/-- Flat base change is compatible with the comparison isomorphisms between resolutions of the
base change. -/
@[simp]
theorem baseChangeIso_trans_derivedIso (P : SimplicialProjectiveResolution M)
    (Q Q' : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M)) (i : ℕ) :
    baseChangeIso f hf P Q i ≪≫ derivedIso (exteriorSquare B) Q Q' i =
      baseChangeIso f hf P Q' i := by
  simp [baseChangeIso, Iso.trans_assoc]

/-- **Flat base change along the identity** is the identification `A ⊗_A LᵢΛ²(M) ≅ LᵢΛ²(M)`
given by `ModuleCat.extendScalarsId`. -/
theorem baseChangeIso_id_hom (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution ((ModuleCat.extendScalars (RingHom.id A)).obj M))
    (i : ℕ) :
    (baseChangeIso (RingHom.id A) (RingHom.Flat.id A) P Q i).hom ≫
        derivedMap (exteriorSquare A) ((ModuleCat.extendScalarsId A).hom.app M) Q P i =
      (ModuleCat.extendScalarsId A).hom.app (homology P i) := by
  have := extendScalars_preservesHomology_of_flat.{u, u} (RingHom.id A) (RingHom.Flat.id A)
  have hc : Functor.whiskerLeft (exteriorSquare A) (ModuleCat.extendScalarsId A).hom ≫
      ((exteriorSquare A).rightUnitor ≪≫ (exteriorSquare A).leftUnitor.symm).hom =
        (ModuleCat.exteriorPower.extendScalarsIso (RingHom.id A) 2).hom ≫
          Functor.whiskerRight (ModuleCat.extendScalarsId A).hom (exteriorSquare A) := by
    ext N : 2
    simpa using ModuleCat.exteriorPower.extendScalarsId_hom_app_eq 2 N
  have hP' : ∀ n, Projective ((𝟭 (ModuleCat.{u} A)).obj (P.obj _⦋n⦌)) := fun n => P.projective n
  have hT := app_comp_mapDerivedHomologyIso_hom _ _ _ _ hc P
    (fun n => (ModuleCat.extendScalars (RingHom.id A)).projective_obj (P.obj _⦋n⦌))
    inferInstance hP' inferInstance i
  have hI := mapDerivedHomologyIso_refl_hom P hP' inferInstance (F₀ := exteriorSquare A) i
  have key := (reassoc_of% hT) (derivedIso _ (P.mapOfQuasiIso (𝟭 _) hP' inferInstance) P i).hom
  rw [hI] at key
  rw [(Category.comp_id _).symm.trans key]
  simp only [baseChangeIso, Iso.trans_hom, derivedIso_hom, Category.assoc, derivedMap_comp,
    Category.id_comp]
  exact congrArg (fun φ => _ ≫ derivedMap (exteriorSquare A) φ _ P i) (Category.comp_id _).symm

/-- **The cocycle condition for flat base change.** For flat ring maps `f : A → B` and
`g : B → C`, base change along `g ∘ f` is base change along `f` followed by base change along
`g`, under the identifications `C ⊗_A - ≅ C ⊗_B (B ⊗_A -)` of `ModuleCat.extendScalarsComp`. -/
theorem baseChangeIso_comp_hom {C : Type u} [CommRing C] (g : B →+* C) (hg : g.Flat)
    (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution ((ModuleCat.extendScalars f).obj M))
    (S : SimplicialProjectiveResolution
      ((ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)))
    (S' : SimplicialProjectiveResolution ((ModuleCat.extendScalars (g.comp f)).obj M)) (i : ℕ) :
    (baseChangeIso (g.comp f) (hf.comp hg) P S' i).hom ≫
        derivedMap (exteriorSquare C) ((ModuleCat.extendScalarsComp f g).hom.app M) S' S i =
      (ModuleCat.extendScalarsComp f g).hom.app (homology P i) ≫
        (ModuleCat.extendScalars g).map (baseChangeIso f hf P Q i).hom ≫
          (baseChangeIso g hg Q S i).hom := by
  have := extendScalars_preservesHomology_of_flat.{u, u} f hf
  have := extendScalars_preservesHomology_of_flat.{u, u} g hg
  have := extendScalars_preservesHomology_of_flat.{u, u} (g.comp f) (hf.comp hg)
  have hc : Functor.whiskerLeft (exteriorSquare A) (ModuleCat.extendScalarsComp f g).hom ≫
      (pasteIso (ModuleCat.exteriorPower.extendScalarsIso f 2)
        (ModuleCat.exteriorPower.extendScalarsIso g 2)).hom =
        (ModuleCat.exteriorPower.extendScalarsIso (g.comp f) 2).hom ≫
          Functor.whiskerRight (ModuleCat.extendScalarsComp f g).hom (exteriorSquare C) := by
    ext N : 2
    simpa using ModuleCat.exteriorPower.extendScalarsComp_hom_app_comp f g 2 N
  have hP₁₂ : ∀ n, Projective ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj
      (P.obj _⦋n⦌)) := fun n => (ModuleCat.extendScalars g).projective_obj _
  have hT := app_comp_mapDerivedHomologyIso_hom _ _ _ _ hc P
    (fun n => (ModuleCat.extendScalars (g.comp f)).projective_obj (P.obj _⦋n⦌))
    inferInstance hP₁₂ inferInstance i
  have hC := mapDerivedHomologyIso_pasteIso_hom (ModuleCat.exteriorPower.extendScalarsIso f 2)
    (ModuleCat.exteriorPower.extendScalarsIso g 2) P hP₁₂ inferInstance
    (fun n => (ModuleCat.extendScalars f).projective_obj (P.obj _⦋n⦌)) inferInstance
    (fun n => (ModuleCat.extendScalars g).projective_obj _) inferInstance i
  have hN := map_derivedMap_comp_mapDerivedHomologyIso_hom
    (ModuleCat.exteriorPower.extendScalarsIso g 2) (𝟙 _) (P.extendScalars f hf) Q
    (fun n => (ModuleCat.extendScalars g).projective_obj _) inferInstance
    (fun n => (ModuleCat.extendScalars g).projective_obj _) inferInstance i
  simp only [baseChangeIso, Iso.trans_hom, derivedIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hN, ← reassoc_of% hC, reassoc_of% hT]
  simp only [derivedIso_hom, derivedMap_comp, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]


/-- The localization map `A → T⁻¹A` is flat. -/
lemma flat_algebraMap_localization (T : Submonoid A) :
    (algebraMap A (Localization T)).Flat :=
  RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ T)

/-- **Localization of the derived exterior square.** For a submonoid `T` of `A`,
`T⁻¹ LᵢΛ²_A(M) ≅ LᵢΛ²_{T⁻¹A}(T⁻¹A ⊗_A M)`. -/
def localizationIso (T : Submonoid A) (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution
      ((ModuleCat.extendScalars (algebraMap A (Localization T))).obj M)) (i : ℕ) :
    (homology P i).localizedModule T ≅ homology Q i :=
  ((extendScalars_iso_localizedModuleFunctor.{u, u} T).app (homology P i)).symm ≪≫
    baseChangeIso _ (flat_algebraMap_localization T) P Q i

end DerivedSquare

end Stacks

/-! ### Reduction modulo a regular element -/

namespace Stacks

variable {A : Type u} [CommRing A] (r : A)

/-- Multiplication by `r : A` on a functor with values in `A`-modules. -/
@[simps]
def smulNatTrans {J : Type*} [Category J] (F : J ⥤ ModuleCat.{u} A) : F ⟶ F where
  app X := r • 𝟙 (F.obj X)
  naturality _ _ g := by simp

/-- The natural map `⋀ⁿ_A N → ⋀ⁿ_{A ⧸ (r)}((A ⧸ (r)) ⊗_A N)`, `x ↦ 1 ⊗ x` followed by the
identification of `ModuleCat.exteriorPower.extendScalarsIso`. -/
def exteriorPowerReduction (n : ℕ) :
    ModuleCat.exteriorPower.functor A n ⟶
      ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r})) ⋙
        ModuleCat.exteriorPower.functor (A ⧸ Ideal.span {r}) n ⋙
          ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (Ideal.span {r}))).unit ≫
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (ModuleCat.exteriorPower.extendScalarsIso _ n).hom
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))) ≫
          (Functor.associator _ _ _).hom

/-- The unit `N → (A ⧸ (r)) ⊗_A N`, `m ↦ 1 ⊗ m`, followed by the identification
`(A ⧸ I) ⊗_A N ≃ N ⧸ I N`, is the quotient map. -/
lemma quotTensorEquivQuotSMul_unit_app (N : ModuleCat.{u} A) (m : N) :
    (TensorProduct.quotTensorEquivQuotSMul N (Ideal.span {r}) :
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj N) ≃ₗ[A]
          N ⧸ Ideal.span {r} • (⊤ : Submodule A N))
      (((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (Ideal.span {r}))).unit.app N).hom m)
        = Submodule.Quotient.mk m :=
  (congrArg _ (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ N m)).trans
    (LinearMap.congr_fun (TensorProduct.quotTensorEquivQuotSMul_comp_mk (Ideal.span {r})) m)

/-- The composite `N →(r) N → (A ⧸ (r)) ⊗_A N` vanishes. -/
lemma smul_comp_unit_app (N : ModuleCat.{u} A) :
    (r • 𝟙 N) ≫
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (Ideal.span {r}))).unit.app N = 0 := by
  ext m
  refine (TensorProduct.quotTensorEquivQuotSMul N (Ideal.span {r}) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj N) ≃ₗ[A]
        N ⧸ Ideal.span {r} • (⊤ : Submodule A N)).injective ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, ModuleCat.hom_id,
    LinearMap.smul_apply, LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  refine (quotTensorEquivQuotSMul_unit_app r N (r • m)).trans ?_
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans (map_zero _).symm
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top

/-- For `r` regular on `N`, the sequence `0 → N →(r) N → (A ⧸ (r)) ⊗_A N → 0` is short exact. -/
theorem shortExact_smul_unit_app (N : ModuleCat.{u} A) (hN : IsSMulRegular N r) :
    (ShortComplex.mk (r • 𝟙 N)
      ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (Ideal.span {r}))).unit.app N)
      (smul_comp_unit_app r N)).ShortExact := by
  let E : (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj N) ≃ₗ[A]
        N ⧸ Ideal.span {r} • (⊤ : Submodule A N) :=
    TensorProduct.quotTensorEquivQuotSMul N (Ideal.span {r})
  have key := quotTensorEquivQuotSMul_unit_app r N
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro m hm
    have h0 : (Submodule.Quotient.mk m : N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) = 0 := by
      rw [← key m]
      exact (congrArg E hm).trans (map_zero E)
    rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h0
    obtain ⟨n, -, hn⟩ := h0
    exact ⟨n, hn⟩
  · exact (ModuleCat.mono_iff_injective _).2 hN
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (E y)
    exact ⟨m, E.injective ((key m).trans hm)⟩

/-- The composite `⋀ⁿ N →(r) ⋀ⁿ N → ⋀ⁿ_{A ⧸ (r)}((A ⧸ (r)) ⊗_A N)` vanishes. -/
lemma smul_comp_exteriorPowerReduction_app (n : ℕ) (N : ModuleCat.{u} A) :
    (r • 𝟙 _) ≫ (exteriorPowerReduction r n).app N = 0 := by
  simp only [exteriorPowerReduction, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, smul_comp_unit_app r ((ModuleCat.exteriorPower.functor A n).obj N),
    zero_comp]

/-- For `r` regular on `⋀ⁿ N`, the sequence
`0 → ⋀ⁿ_A N →(r) ⋀ⁿ_A N → ⋀ⁿ_{A ⧸ (r)}((A ⧸ (r)) ⊗_A N) → 0` is short exact. -/
theorem shortExact_smul_exteriorPowerReduction_app (n : ℕ) (N : ModuleCat.{u} A)
    (hN : IsSMulRegular ((ModuleCat.exteriorPower.functor A n).obj N) r) :
    (ShortComplex.mk (r • 𝟙 _) ((exteriorPowerReduction r n).app N)
      (smul_comp_exteriorPowerReduction_app r n N)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (shortExact_smul_unit_app r _ hN)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((ModuleCat.restrictScalars _).mapIso
      ((ModuleCat.exteriorPower.extendScalarsIso (Ideal.Quotient.mk (Ideal.span {r})) n).app N))
    (by simp) ?_
  simp [exteriorPowerReduction]

namespace SimplicialProjectiveResolution

variable {r} {M : ModuleCat.{u} A}

/-- The exterior powers of a projective `A`-module are regular for every nonzerodivisor of
`A`. -/
lemma isSMulRegular_exteriorPower (hr : r ∈ nonZeroDivisors A) (N : ModuleCat.{u} A)
    [Projective N] (n : ℕ) : IsSMulRegular ((ModuleCat.exteriorPower.functor A n).obj N) r := by
  have : Module.Projective A N := (IsProjective.iff_projective N).2 ‹_›
  have : Module.Projective A (⋀[A]^n N) := exteriorPower.instProjective n
  have : Module.Flat A (⋀[A]^n N) := Module.Flat.of_projective
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ⋀[A]^n N) hr

/-- A projective `A`-module is regular for every nonzerodivisor of `A`. -/
lemma isSMulRegular_of_projective (hr : r ∈ nonZeroDivisors A) (N : ModuleCat.{u} A)
    [Projective N] : IsSMulRegular N r := by
  have : Module.Projective A N := (IsProjective.iff_projective N).2 ‹_›
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr

variable (r) in
/-- The degreewise short exact sequence `0 → P →(r) P → (A ⧸ (r)) ⊗_A P → 0` of simplicial
modules. -/
def reductionShortComplex₀ (P : SimplicialProjectiveResolution M) :
    ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk (smulNatTrans r P.obj)
    (Functor.whiskerLeft P.obj
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (Ideal.span {r}))).unit)
    (NatTrans.ext (funext fun _ => smul_comp_unit_app r _))

/-- The homology of the complex of a simplicial projective resolution of `M` vanishes in positive
degrees. -/
private lemma isZero_homology_succ (P : SimplicialProjectiveResolution M) (j : ℕ) :
    IsZero (((alternatingFaceMapComplex _).obj P.obj).homology (j + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((quasiIsoAt_iff_exactAt' P.π (j + 1) (ChainComplex.exactAt_succ_single_obj M j)).1
      inferInstance)

/-- Multiplication by an `M`-regular element is injective on the homology of a simplicial
projective resolution of `M`. -/
lemma mono_homologyMap_smul (P : SimplicialProjectiveResolution M) (hM : IsSMulRegular M r)
    (j : ℕ) :
    Mono (HomologicalComplex.homologyMap (r • 𝟙 ((alternatingFaceMapComplex _).obj P.obj)) j) := by
  rw [HomologicalComplex.homologyMap_smul_id_of_linear]
  cases j with
  | zero =>
    have := P.quasiIso
    let e : ((alternatingFaceMapComplex _).obj P.obj).homology 0 ≅ M :=
      isoOfQuasiIsoAt P.π 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    apply e.toLinearEquiv.injective
    apply hM
    have h := congrArg e.hom.hom hxy
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul] at h
    exact h
  | succ j =>
    exact ⟨fun g h _ => (isZero_homology_succ P j).eq_of_tgt g h⟩

/-- **Reduction of a resolution modulo a regular element.** If `r` is a nonzerodivisor on `A`
and on `M`, the image of the augmentation of `(A ⧸ (r)) ⊗_A P` is a quasi-isomorphism:
`Torᵢ^A(A ⧸ (r), M) = 0` for `i > 0`. -/
theorem quasiIso_mapπ_reduction (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) :
    QuasiIso (P.mapπ (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r})))) := by
  let G := ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (Ideal.span {r}))
  let R := ModuleCat.restrictScalars.{u, u, u} (Ideal.Quotient.mk (Ideal.span {r}))
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (Ideal.Quotient.mk (Ideal.span {r}))
  let S := (reductionShortComplex₀ r P).map (alternatingFaceMapComplex _)
  have hS : S.ShortExact := ShortComplex.ShortExact.map_alternatingFaceMapComplex_of_app fun n =>
    shortExact_smul_unit_app r (P.obj _⦋n⦌) (isSMulRegular_of_projective hr (P.obj _⦋n⦌))
  have hK : ∀ j : ℕ, IsZero (S.X₁.homology (j + 1)) := isZero_homology_succ P
  have hmono : ∀ j : ℕ, Mono (HomologicalComplex.homologyMap S.f j) :=
    mono_homologyMap_smul P hM
  have hX₃ : ∀ j : ℕ, IsZero (S.X₃.homology (j + 1)) := fun j => by
    have h₃ := hS.homology_exact₃ (j + 1) j rfl
    have h₁ := hS.homology_exact₁ (j + 1) j rfl
    have : Mono (hS.δ (j + 1) j rfl) := h₃.mono_g ((hK j).eq_of_src _ _)
    have hδ : hS.δ (j + 1) j rfl = 0 := h₁.mono_g_iff.1 (hmono j)
    rw [hδ] at this
    exact IsZero.of_mono_zero (S.X₃.homology (j + 1)) (S.X₁.homology j)
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    obtain ⟨hex, hepi⟩ := P.exact_ε
    have : PreservesColimitsOfSize.{0, 0} G := adj.leftAdjoint_preservesColimits
    have h := hex.map_of_epi_of_preservesCokernel G hepi inferInstance
    have hre : IsRightExactOn G P := by
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h ⊢
        have hd : (P.derivedComplex G).d 1 0 =
            G.map (((alternatingFaceMapComplex _).obj P.obj).d 1 0) := by
          rw [derivedComplex_d_one_zero, alternatingFaceMapComplex_obj_d_one_zero, G.map_sub]
        change LinearMap.range ((P.derivedComplex G).d 1 0).hom = LinearMap.ker (G.map P.ε).hom
        rwa [hd]
      · have := adj.isLeftAdjoint
        infer_instance
    have heq : P.mapπ G = P.derivedComplexπ G :=
      HomologicalComplex.to_single_hom_ext (by simp)
    rw [heq]
    exact quasiIsoAt_derivedComplexπ_zero G hre
  | succ j =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ j),
      HomologicalComplex.exactAt_iff_isZero_homology]
    have h₂ := (hX₃ j).of_iso (HomologicalComplex.homologyMapIso
      (alternatingFaceMapComplexCompIso (P.obj ⋙ G) R) (j + 1)).symm
    have h₃ := h₂.of_iso
      (HomologicalComplex.mapHomologyIso ((alternatingFaceMapComplex _).obj (P.obj ⋙ G)) R
        (j + 1)).symm
    have h₄ := ModuleCat.isZero_iff_subsingleton.1 h₃
    exact ModuleCat.isZero_iff_subsingleton.2 h₄

variable (r) in
/-- **The reduction modulo a regular element** of a simplicial projective resolution `P` of `M`:
for `r` a nonzerodivisor on `A` and on `M`, `(A ⧸ (r)) ⊗_A P` is a simplicial projective
resolution of `M ⧸ rM = (A ⧸ (r)) ⊗_A M` over `A ⧸ (r)`. -/
abbrev reduce (P : SimplicialProjectiveResolution M) (hr : r ∈ nonZeroDivisors A)
    (hM : IsSMulRegular M r) :
    SimplicialProjectiveResolution
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj M) :=
  P.mapOfQuasiIso _ (fun n => (ModuleCat.extendScalars _).projective_obj (P.obj _⦋n⦌))
    (P.quasiIso_mapπ_reduction hr hM)

end SimplicialProjectiveResolution

namespace DerivedSquare

open SimplicialProjectiveResolution

variable {r} {M : ModuleCat.{u} A}

/-- The degreewise short exact sequence of simplicial `A`-modules
`0 → ⋀²P →(r) ⋀²P → ⋀²_{A ⧸ (r)}((A ⧸ (r)) ⊗_A P) → 0`. -/
def reductionShortComplex (P : SimplicialProjectiveResolution M) (hr : r ∈ nonZeroDivisors A)
    (hM : IsSMulRegular M r) : ShortComplex (SimplicialObject (ModuleCat.{u} A)) where
  X₁ := P.obj ⋙ exteriorSquare A
  X₂ := P.obj ⋙ exteriorSquare A
  X₃ := ((P.reduce r hr hM).obj ⋙ exteriorSquare (A ⧸ Ideal.span {r})) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))
  f := smulNatTrans r (P.obj ⋙ exteriorSquare A)
  g := Functor.whiskerLeft P.obj (exteriorPowerReduction r 2)
  zero := NatTrans.ext (funext fun _ => smul_comp_exteriorPowerReduction_app r 2 _)

/-- The sequence of complexes `0 → LΛ²(P) →(r) LΛ²(P) → LΛ²_{A ⧸ (r)}(P ⧸ rP) → 0` is short
exact: degreewise, `⋀²Pₙ` is projective, hence `r`-regular, and
`⋀²Pₙ ⧸ r ≅ ⋀²_{A ⧸ (r)}(Pₙ ⧸ rPₙ)`. -/
theorem reductionShortComplex_shortExact (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) :
    ((reductionShortComplex P hr hM).map (alternatingFaceMapComplex _)).ShortExact :=
  ShortComplex.ShortExact.map_alternatingFaceMapComplex_of_app fun n =>
    shortExact_smul_exteriorPowerReduction_app r 2 (P.obj _⦋n⦌)
      (isSMulRegular_exteriorPower hr (P.obj _⦋n⦌) 2)

/-- The homology of the third term of `reductionShortComplex` is `LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)`,
regarded as an `A`-module. -/
def reductionHomologyIso (P : SimplicialProjectiveResolution M) (hr : r ∈ nonZeroDivisors A)
    (hM : IsSMulRegular M r) (i : ℕ) :
    ((alternatingFaceMapComplex _).obj (reductionShortComplex P hr hM).X₃).homology i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
        (homology (P.reduce r hr hM) i) :=
  HomologicalComplex.homologyMapIso (alternatingFaceMapComplexCompIso
    ((P.reduce r hr hM).obj ⋙ exteriorSquare (A ⧸ Ideal.span {r})) _) i ≪≫
      HomologicalComplex.mapHomologyIso (complex (P.reduce r hr hM)) _ i

/-- The reduction map `LᵢΛ²_A(M) → LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)`. -/
def reductionMap (P : SimplicialProjectiveResolution M) (hr : r ∈ nonZeroDivisors A)
    (hM : IsSMulRegular M r) (i : ℕ) :
    homology P i ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      (homology (P.reduce r hr hM) i) :=
  HomologicalComplex.homologyMap ((reductionShortComplex P hr hM).map
    (alternatingFaceMapComplex _)).g i ≫ (reductionHomologyIso P hr hM i).hom

/-- The connecting map `Lᵢ₊₁Λ²_{A ⧸ (r)}(M ⧸ rM) → LᵢΛ²_A(M)`. -/
def reductionδ (P : SimplicialProjectiveResolution M) (hr : r ∈ nonZeroDivisors A)
    (hM : IsSMulRegular M r) (i : ℕ) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      (homology (P.reduce r hr hM) (i + 1)) ⟶ homology P i :=
  (reductionHomologyIso P hr hM (i + 1)).inv ≫
    (reductionShortComplex_shortExact P hr hM).δ (i + 1) i rfl

/-- The first map of `reductionShortComplex` induces multiplication by `r` on `LᵢΛ²(M)`. -/
lemma homologyMap_reductionShortComplex_f (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ) :
    HomologicalComplex.homologyMap ((reductionShortComplex P hr hM).map
      (alternatingFaceMapComplex _)).f i = r • 𝟙 (homology P i) :=
  HomologicalComplex.homologyMap_smul_id_of_linear (complex P) i r

/-- The connecting map of `reductionShortComplex_shortExact` is `reductionδ` after the
identification `reductionHomologyIso`. -/
private lemma reductionδ_hom_reductionHomologyIso_hom (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ)
    (x : ((alternatingFaceMapComplex _).obj (reductionShortComplex P hr hM).X₃).homology (i + 1)) :
    (reductionδ P hr hM i).hom ((reductionHomologyIso P hr hM (i + 1)).hom x) =
      ((reductionShortComplex_shortExact P hr hM).δ (i + 1) i rfl).hom x :=
  congrArg ((reductionShortComplex_shortExact P hr hM).δ (i + 1) i rfl).hom
    (congrArg (fun φ => φ.hom x) (reductionHomologyIso P hr hM (i + 1)).hom_inv_id)

/-- **Exactness at `LᵢΛ²_A(M)`** of `LᵢΛ²_A(M) →(r) LᵢΛ²_A(M) → LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)`. -/
theorem exact_smul_reductionMap (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ) :
    Function.Exact (fun x : homology P i => r • x) (reductionMap P hr hM i).hom := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((reductionShortComplex_shortExact P hr hM).homology_exact₂ i)
  dsimp only at h
  have hfun := fun x => congrArg (fun φ => φ.hom x) (homologyMap_reductionShortComplex_f P hr hM i)
  have h' : Function.Exact (fun x : homology P i => r • x) (HomologicalComplex.homologyMap
      ((reductionShortComplex P hr hM).map (alternatingFaceMapComplex _)).g i).hom := by
    intro y
    rw [h y]
    constructor <;> rintro ⟨x, rfl⟩
    · exact ⟨x, (hfun x).symm⟩
    · exact ⟨x, hfun x⟩
  exact h'.comp_injective _ (reductionHomologyIso P hr hM i).toLinearEquiv.injective (map_zero _)

/-- **Exactness at `LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)`** of
`Lᵢ₊₁Λ²_A(M) → Lᵢ₊₁Λ²_{A ⧸ (r)}(M ⧸ rM) → LᵢΛ²_A(M)`. -/
theorem exact_reductionMap_reductionδ (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ) :
    Function.Exact (reductionMap P hr hM (i + 1)).hom (reductionδ P hr hM i).hom := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((reductionShortComplex_shortExact P hr hM).homology_exact₃ (i + 1) i rfl)
  dsimp only at h
  refine (Function.Exact.iff_of_ladder_linearEquiv (e₁ := LinearEquiv.refl A _)
    (e₂ := (reductionHomologyIso P hr hM (i + 1)).toLinearEquiv) (e₃ := LinearEquiv.refl A _)
    ?_ ?_).2 h
  · ext x
    rfl
  · ext x
    exact reductionδ_hom_reductionHomologyIso_hom P hr hM i x

/-- **Exactness at `LᵢΛ²_A(M)`** of
`Lᵢ₊₁Λ²_{A ⧸ (r)}(M ⧸ rM) → LᵢΛ²_A(M) →(r) LᵢΛ²_A(M)`. -/
theorem exact_reductionδ_smul (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ) :
    Function.Exact (reductionδ P hr hM i).hom (fun x : homology P i => r • x) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((reductionShortComplex_shortExact P hr hM).homology_exact₁ (i + 1) i rfl)
  dsimp only at h
  have hfun := fun x => congrArg (fun φ => φ.hom x) (homologyMap_reductionShortComplex_f P hr hM i)
  have h' : Function.Exact ((reductionShortComplex_shortExact P hr hM).δ (i + 1) i rfl).hom
      (fun x : homology P i => r • x) := by
    intro y
    rw [← h y]
    exact ⟨fun hy => (hfun y).trans hy, fun hy => (hfun y).symm.trans hy⟩
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (reductionHomologyIso P hr hM (i + 1)).toLinearEquiv) (e₂ := LinearEquiv.refl A _)
    (e₃ := LinearEquiv.refl A _) (g₂₃ := (r • 𝟙 (homology P i)).hom)
    (f₂₃ := (r • 𝟙 (homology P i)).hom) ?_ ?_).2 h'
  · ext x
    exact reductionδ_hom_reductionHomologyIso_hom P hr hM i x
  · ext x
    rfl

end DerivedSquare

/-! ### Finiteness and support -/

namespace SimplicialProjectiveResolution

/-- **Existence of finite free simplicial resolutions.** Over a Noetherian ring, a finitely
generated module `M` has a simplicial projective resolution whose terms are finite free modules:
the Dold–Kan functor `Γ` applied to a resolution of `M` by finite free modules. -/
@[ega "IV 12.3.2" "(i), special case", sga "4 IX 2.3" "partial"]
theorem exists_finite_free [IsNoetherianRing A] (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ P : SimplicialProjectiveResolution M,
      ∀ n, Module.Free A (P.obj _⦋n⦌) ∧ Module.Finite A (P.obj _⦋n⦌) := by
  classical
  obtain ⟨D, hD, hFF⟩ := exists_finite_free_resolution A M
  have hFree : D.IsFree := fun n => (hFF n).1
  refine ⟨ofProjectiveResolution
    (CochainComplex.KFlat.freeProjectiveResolution D hD hFree), fun n => ?_⟩
  have : ∀ i, Module.Free A (DoldKan.Γ₀.Obj.summand (C := ModuleCat.{u} A)
      (CochainComplex.KFlat.freeProjectiveResolution D hD hFree).complex (op ⦋n⦌) i) :=
    fun i => (hFF _).1
  have : ∀ i, Module.Finite A (DoldKan.Γ₀.Obj.summand (C := ModuleCat.{u} A)
      (CochainComplex.KFlat.freeProjectiveResolution D hD hFree).complex (op ⦋n⦌) i) :=
    fun i => (hFF _).2
  exact ⟨Module.Free.of_equiv (ModuleCat.coprodIsoDirectSum _).symm.toLinearEquiv,
    Module.Finite.equiv (ModuleCat.coprodIsoDirectSum _).symm.toLinearEquiv⟩

end SimplicialProjectiveResolution

namespace DerivedSquare

open SimplicialProjectiveResolution

variable {M : ModuleCat.{u} A}

/-- If the terms of `P` are finitely generated over a Noetherian ring, so is each `LᵢΛ²(P)`. -/
theorem finite_homology_of_finite [IsNoetherianRing A] (P : SimplicialProjectiveResolution M)
    (hP : ∀ n, Module.Finite A (P.obj _⦋n⦌)) (i : ℕ) : Module.Finite A (homology P i) := by
  have := hP i
  have : Module.Finite A ((complex P).X i) :=
    exteriorPower.instFinite (M := P.obj _⦋i⦌) (n := 2)
  have : Module.Finite A ((complex P).cycles i) :=
    Module.Finite.of_injective ((complex P).iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective ((complex P).homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- **Finiteness of the derived exterior square.** Over a Noetherian ring, `LᵢΛ²(M)` is finitely
generated for a finitely generated module `M`, whatever the resolution used to compute it. -/
theorem finite_homology [IsNoetherianRing A] [Module.Finite A M]
    (Q : SimplicialProjectiveResolution M) (i : ℕ) : Module.Finite A (homology Q i) := by
  obtain ⟨P, hP⟩ := exists_finite_free M
  have := finite_homology_of_finite P (fun n => (hP n).2) i
  exact Module.Finite.equiv (derivedIso _ P Q i).toLinearEquiv

/-- The derived exterior squares of a zero module vanish: the zero map lifts the identity, and
`⋀²` of the zero map is zero. -/
theorem isZero_homology (hM : IsZero M) (Q : SimplicialProjectiveResolution M) (i : ℕ) :
    IsZero (homology Q i) := by
  have hl : IsLift Q Q (𝟙 M) 0 := (isLift_iff _ _).2 (hM.eq_of_tgt _ _)
  have h0 : derivedComplexMap (exteriorSquare A) (0 : Q.obj ⟶ Q.obj) = 0 := by
    ext n : 1
    refine ModuleCat.hom_ext ?_
    change exteriorPower.map 2 (0 : Q.obj _⦋n⦌ →ₗ[A] Q.obj _⦋n⦌) = 0
    simpa using exteriorPower.map_smul_eq_pow_smul 2 (0 : A)
      (0 : Q.obj _⦋n⦌ →ₗ[A] Q.obj _⦋n⦌)
  rw [IsZero.iff_id_eq_zero, ← derivedMap_id (exteriorSquare A) Q i, hl.derivedMap_eq, h0,
    HomologicalComplex.homologyMap_zero]

/-- **Support of the derived exterior square.** `Supp LᵢΛ²(M) ⊆ Supp M`: at a prime `p` outside
the support of `M`, `(LᵢΛ²(M))_p ≅ LᵢΛ²_{A_p}(M_p) = 0` by flat base change to `A_p`. -/
theorem support_homology_subset (P : SimplicialProjectiveResolution M) (i : ℕ) :
    Module.support A (homology P i) ⊆ Module.support A M := by
  intro p
  contrapose
  intro hpM
  rw [Module.notMem_support_iff] at hpM ⊢
  let T := p.asIdeal.primeCompl
  let Q := P.extendScalars _ (flat_algebraMap_localization T)
  have eM := @IsLocalizedModule.iso _ _ T _ _ _ _ _ _ _
    (ModuleCat.localizedModule_isLocalizedModule M T)
  have hZ : IsZero ((ModuleCat.extendScalars (algebraMap A (Localization T))).obj M) :=
    IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.2 eM.symm.toEquiv.subsingleton)
      ((extendScalars_iso_localizedModuleFunctor.{u, u} T).app M)
  have hL := ModuleCat.isZero_iff_subsingleton.1 ((isZero_homology hZ Q i).of_iso
    (localizationIso T P Q i))
  exact (@IsLocalizedModule.iso _ _ T _ _ _ _ _ _ _
    (ModuleCat.localizedModule_isLocalizedModule (homology P i) T)).toEquiv.subsingleton

end DerivedSquare

end Stacks
