module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Modules and complexes over a product ring are detected by the two factors

Let `B` and `C` be commutative rings and write `D = B × C`. The two projections make `B` and `C`
into `D`-algebras, and `D = B ⊕ C` as a `D`-module, so a `D`-module `M` is the direct sum of
`e • M` and `(1 - e) • M` for the idempotent `e = (1, 0)`; the first summand is `B ⊗_D M` and the
second is `C ⊗_D M`. Consequently a map of `D`-modules is an isomorphism as soon as its two base
changes are, and — the two base changes being exact, `B` and `C` being flat over `D` — a map of
complexes of `D`-modules is a quasi-isomorphism as soon as its two base changes are.

The second statement is what a comparison over a product ring consumes: it reduces a statement
about `D` to the same statement about each factor, which is how [Stacks, Tag 08SC] reduces the
cotangent complex of `B × C` to those of `B` and of `C`.

## Main results

* `RingHom.surjective_fst` and `RingHom.surjective_snd`: the two projections of a product ring
  are surjective. With `Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app` this says the
  counit `B ⊗_{B×C} M ⟶ M` is invertible on a `B`-module `M` read over `B × C`.
* `RingHom.flat_fst` and `RingHom.flat_snd`: the two projections of a product ring are flat.
* `ModuleCat.isZero_extendScalars_of_smul_eq_zero`: a base change vanishes when an element acting
  as zero has image `1`; `ModuleCat.isZero_extendScalars_fst_restrictScalars_snd` and
  `ModuleCat.isZero_extendScalars_snd_restrictScalars_fst` are the two instances at the
  orthogonal idempotents of `B × C`, so that `B ⊗_{B×C} N = 0` for a `C`-module `N` and
  `C ⊗_{B×C} M = 0` for a `B`-module `M`.
* `Module.bijective_of_bijective_baseChange_of_sections`: the module-level statement, for a pair
  of algebras carrying linear sections whose values at `1` add up to `1`. It is stated at that
  generality because the two cases `B` and `C` are not symmetric in Lean's syntax, while they are
  two instances of this one statement.
* `CategoryTheory.Functor.isIso_map_homologyMap`: for a functor preserving homology, the homology
  of the image of a map of complexes is invertible exactly when the image of its homology is.
* `ModuleCat.isIso_of_isIso_extendScalars_prod`: a map of `B × C`-modules whose two base changes
  are isomorphisms is an isomorphism.
* `ModuleCat.quasiIso_of_quasiIso_extendScalars_prod`: a map of complexes of `B × C`-modules whose
  two base changes are quasi-isomorphisms is a quasi-isomorphism.

## Implementation notes

The `B × C`-algebra structures on `B` and on `C` are the local instances
`ModuleCat.algebraProdFst` and `ModuleCat.algebraProdSnd`, which are the ring homomorphisms
`RingHom.fst` and `RingHom.snd` read as algebra structures — the same ones
`ModuleCat.extendScalars` uses internally. They are local because a global instance
`Algebra (B × C) B` is not wanted; the public statements below mention only
`ModuleCat.extendScalars` and so do not depend on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace ModuleCat

/-- `B` as a `B × C`-algebra along the first projection. -/
@[instance_reducible]
def algebraProdFst (B C : Type u) [CommRing B] [CommRing C] : Algebra (B × C) B :=
  (RingHom.fst B C).toAlgebra

/-- `C` as a `B × C`-algebra along the second projection. -/
@[instance_reducible]
def algebraProdSnd (B C : Type u) [CommRing B] [CommRing C] : Algebra (B × C) C :=
  (RingHom.snd B C).toAlgebra

attribute [local instance] algebraProdFst algebraProdSnd

variable (B C : Type u) [CommRing B] [CommRing C]

/-- Along the first projection, `B × C` acts on `B` through the first component. -/
lemma smul_prodFst (d : B × C) (b : B) : d • b = d.1 * b := rfl

/-- Along the second projection, `B × C` acts on `C` through the second component. -/
lemma smul_prodSnd (d : B × C) (c : C) : d • c = d.2 * c := rfl

/-- The `B × C`-linear section `b ↦ (b, 0)` of the first projection. Its value at `1` is the
idempotent cutting out the factor `B`. -/
def prodSectionFst : B →ₗ[B × C] (B × C) where
  toFun b := (b, 0)
  map_add' _b _b' := Prod.ext rfl (add_zero (0 : C)).symm
  map_smul' d b := Prod.ext (smul_prodFst B C d b) (mul_zero d.2).symm

/-- The `B × C`-linear section `c ↦ (0, c)` of the second projection. Its value at `1` is the
idempotent cutting out the factor `C`. -/
def prodSectionSnd : C →ₗ[B × C] (B × C) where
  toFun c := (0, c)
  map_add' _c _c' := Prod.ext (add_zero (0 : B)).symm rfl
  map_smul' d c := Prod.ext (mul_zero d.1).symm (smul_prodSnd B C d c)

/-- The two idempotents `(1, 0)` and `(0, 1)` add up to `1`. -/
lemma prodSectionFst_one_add_prodSectionSnd_one :
    prodSectionFst B C 1 + prodSectionSnd B C 1 = 1 :=
  Prod.ext (add_zero (1 : B)) (zero_add (1 : C))

/-- The `B × C`-linear retraction `x ↦ x.1` of `ModuleCat.prodSectionFst`. -/
def prodRetractionFst : (B × C) →ₗ[B × C] B where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' d x := (smul_prodFst B C d x.1).symm

/-- The `B × C`-linear retraction `x ↦ x.2` of `ModuleCat.prodSectionSnd`. -/
def prodRetractionSnd : (B × C) →ₗ[B × C] C where
  toFun x := x.2
  map_add' _ _ := rfl
  map_smul' d x := (smul_prodSnd B C d x.2).symm

end ModuleCat

/-! ### Flatness and surjectivity of the two projections -/

namespace RingHom

open ModuleCat

attribute [local instance] algebraProdFst algebraProdSnd

variable (B C : Type u) [CommRing B] [CommRing C]

/-- The first projection of a product ring is surjective: `b` is the image of `(b, 0)`. -/
theorem surjective_fst : Function.Surjective (RingHom.fst B C) := fun b => ⟨(b, 0), rfl⟩

/-- The second projection of a product ring is surjective: `c` is the image of `(0, c)`. -/
theorem surjective_snd : Function.Surjective (RingHom.snd B C) := fun c => ⟨(0, c), rfl⟩

/-- **The first projection of a product ring is flat.** As a `B × C`-module, `B` is the direct
summand `B × 0` of the free module `B × C`. -/
theorem flat_fst : (RingHom.fst B C).Flat :=
  Module.Flat.of_retract (R := B × C) (M := B × C) (prodSectionFst B C) (prodRetractionFst B C)
    (LinearMap.ext fun _ => rfl)

/-- **The second projection of a product ring is flat.** As a `B × C`-module, `C` is the direct
summand `0 × C` of the free module `B × C`. -/
theorem flat_snd : (RingHom.snd B C).Flat :=
  Module.Flat.of_retract (R := B × C) (M := B × C) (prodSectionSnd B C) (prodRetractionSnd B C)
    (LinearMap.ext fun _ => rfl)

end RingHom

/-! ### Base change along an algebra carrying a linear section -/

namespace Module

variable {D : Type u} [CommRing D] {R : Type u} [CommRing R] [Algebra D R]

/-- The `D`-linear map `R ⊗[D] M ⟶ M` attached to a `D`-linear map `s : R ⟶ D`, sending
`r ⊗ m` to `s r • m`. For `D = B × C`, `R = B` and `s b = (b, 0)` it is the projection of `M`
onto the summand `s 1 • M`, read on `B ⊗_D M`. -/
def scalarSection (s : R →ₗ[D] D) (M : Type u) [AddCommGroup M] [Module D M] :
    R ⊗[D] M →ₗ[D] M :=
  TensorProduct.lift ((LinearMap.lsmul D M).comp s)

variable {M N : Type u} [AddCommGroup M] [Module D M] [AddCommGroup N] [Module D N]

/-- `Module.scalarSection s M` sends `r ⊗ m` to `s r • m`. -/
@[simp]
lemma scalarSection_tmul (s : R →ₗ[D] D) (r : R) (m : M) :
    scalarSection s M (r ⊗ₜ m) = s r • m :=
  rfl

/-- `Module.scalarSection` is natural in the module: it intertwines the base change of a
`D`-linear map with the map itself. -/
lemma scalarSection_baseChange (s : R →ₗ[D] D) (g : M →ₗ[D] N) (x : R ⊗[D] M) :
    scalarSection s N (LinearMap.baseChange R g x) = g (scalarSection s M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rw [LinearMap.baseChange_tmul, scalarSection_tmul, scalarSection_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R' : Type u} [CommRing R'] [Algebra D R']

/-- **A map of `D`-modules is bijective as soon as its two base changes are**, provided the two
algebras carry `D`-linear sections whose values at `1` add up to `1`. For `D = B × C` the two
sections are `b ↦ (b, 0)` and `c ↦ (0, c)`, whose values at `1` are the two orthogonal
idempotents.

Injectivity: if `g m = 0` then `1 ⊗ m` is killed by both base changes, hence vanishes, hence
`s 1 • m = 0` for both sections and `m = (s 1 + s' 1) • m = 0`. Surjectivity: a preimage of
`1 ⊗ n` under each base change is carried by the section to a preimage of `s 1 • n`. -/
theorem bijective_of_bijective_baseChange_of_sections (s : R →ₗ[D] D) (s' : R' →ₗ[D] D)
    (hs : s 1 + s' 1 = 1) (g : M →ₗ[D] N)
    (hR : Function.Bijective (LinearMap.baseChange R g))
    (hR' : Function.Bijective (LinearMap.baseChange R' g)) :
    Function.Bijective g := by
  have inj {R : Type u} [CommRing R] [Algebra D R] (s : R →ₗ[D] D)
      (hR : Function.Bijective (LinearMap.baseChange R g)) (m : M) (hm : g m = 0) :
      s 1 • m = 0 := by
    have : (1 : R) ⊗ₜ[D] m = 0 := hR.1 (by simp [hm])
    rw [← scalarSection_tmul s (1 : R) m, this, map_zero]
  have surj {R : Type u} [CommRing R] [Algebra D R] (s : R →ₗ[D] D)
      (hR : Function.Bijective (LinearMap.baseChange R g)) (n : N) : ∃ y, g y = s 1 • n := by
    obtain ⟨x, hx⟩ := hR.2 ((1 : R) ⊗ₜ[D] n)
    exact ⟨_, by rw [← scalarSection_baseChange s, hx, scalarSection_tmul]⟩
  refine ⟨(injective_iff_map_eq_zero g).2 fun m hm => ?_, fun n => ?_⟩
  · rw [← one_smul D m, ← hs, add_smul, inj s hR m hm, inj s' hR' m hm, add_zero]
  · obtain ⟨y, hy⟩ := surj s hR n
    obtain ⟨y', hy'⟩ := surj s' hR' n
    exact ⟨y + y', by rw [map_add, hy, hy', ← add_smul, hs, one_smul]⟩

end Module

/-! ### Homology of the image of a complex under a functor preserving homology -/

namespace CategoryTheory

/-- In a commutative square whose two vertical arrows are isomorphisms, the bottom arrow is an
isomorphism as soon as the top one is. -/
private theorem isIso_of_isIso_of_commSq {A : Type*} [Category A] {X₁ X₂ Y₁ Y₂ : A}
    (α : X₁ ≅ Y₁) (β : X₂ ≅ Y₂) (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (hu : IsIso u)
    (h : u ≫ β.hom = α.hom ≫ v) : IsIso v := by
  rw [show v = α.inv ≫ u ≫ β.hom by rw [h, Iso.inv_hom_id_assoc]]
  infer_instance

namespace Functor

variable {A₁ A₂ : Type*} [Category A₁] [Category A₂] [Abelian A₁] [Abelian A₂]
  (F : A₁ ⥤ A₂) [F.Additive] [F.PreservesHomology]

/-- For an additive functor preserving homology, the map it induces on the homology of a complex
is the homology of the map it induces on the complex, conjugated by
`ShortComplex.homologyFunctorIso`. So the latter being invertible forces the former to be. -/
theorem isIso_map_homologyMap {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex A₁ c} (f : K ⟶ L) (i : ι)
    (hf : IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map f) i)) :
    IsIso (F.map (HomologicalComplex.homologyMap f i)) :=
  isIso_of_isIso_of_commSq
    ((ShortComplex.homologyFunctorIso F).app
      ((HomologicalComplex.shortComplexFunctor A₁ c i).obj K))
    ((ShortComplex.homologyFunctorIso F).app
      ((HomologicalComplex.shortComplexFunctor A₁ c i).obj L))
    (HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map f) i)
    (F.map (HomologicalComplex.homologyMap f i)) hf
    ((ShortComplex.homologyFunctorIso F).hom.naturality
      ((HomologicalComplex.shortComplexFunctor A₁ c i).map f))

end Functor

end CategoryTheory

/-! ### Vanishing of a base change killed by an element with image `1` -/

namespace ModuleCat

open scoped ChangeOfRings

/-- A tensor product `S ⊗_R N` is trivial as soon as some `r : R` acts as the identity on `S`
and as zero on `N`: a pure tensor is `s ⊗ n = (r • s) ⊗ n = s ⊗ (r • n) = 0`. -/
private theorem subsingleton_tensorProduct_of_smul {R S : Type u} [CommRing R] [CommRing S]
    [Module R S] {N : Type u} [AddCommGroup N] [Module R N] (r : R)
    (hS : ∀ s : S, r • s = s) (hN : ∀ n : N, r • n = 0) :
    Subsingleton (S ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul s n => rw [← hS s, TensorProduct.smul_tmul, hN n, TensorProduct.tmul_zero]
  | add u v hu hv => rw [hu, hv, add_zero]

/-- **A base change vanishes when some element acting as zero has image `1`.** If `r : R` kills
the `R`-module `N` and `f r = 1`, then `S ⊗_R N = 0`: the image of `r` acts as the identity on
`S`, so on a pure tensor `s ⊗ n = (r • s) ⊗ n = s ⊗ (r • n) = 0`. -/
theorem isZero_extendScalars_of_smul_eq_zero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (N : ModuleCat.{u} R) (r : R) (hr : f r = 1) (hN : ∀ n : N, r • n = 0) :
    IsZero ((ModuleCat.extendScalars f).obj N) := by
  let _ : Module R S := Module.compHom S f
  exact ModuleCat.isZero_iff_subsingleton.2 (subsingleton_tensorProduct_of_smul (S := S)
    (N := (N : Type u)) r (fun s => show f r * s = s by rw [hr, one_mul]) hN)

end ModuleCat

/-! ### The two base changes along the projections of a product ring -/

namespace ModuleCat

attribute [local instance] algebraProdFst algebraProdSnd

variable {B C : Type u} [CommRing B] [CommRing C]

/-- **`B ⊗_{B×C} N = 0` for a `C`-module `N` read over `B × C`.** The idempotent `(1, 0)` has
image `1` under the first projection and acts as `0` on `N`. -/
theorem isZero_extendScalars_fst_restrictScalars_snd (N : ModuleCat.{u} C) :
    IsZero ((ModuleCat.extendScalars (RingHom.fst B C)).obj
      ((ModuleCat.restrictScalars (RingHom.snd B C)).obj N)) :=
  isZero_extendScalars_of_smul_eq_zero (RingHom.fst B C) _ ((1 : B), (0 : C)) rfl
    fun n => by rw [show ((1 : B), (0 : C)) • n = (0 : C) • n from rfl, zero_smul]

/-- **`C ⊗_{B×C} M = 0` for a `B`-module `M` read over `B × C`.** The idempotent `(0, 1)` has
image `1` under the second projection and acts as `0` on `M`. -/
theorem isZero_extendScalars_snd_restrictScalars_fst (M : ModuleCat.{u} B) :
    IsZero ((ModuleCat.extendScalars (RingHom.snd B C)).obj
      ((ModuleCat.restrictScalars (RingHom.fst B C)).obj M)) :=
  isZero_extendScalars_of_smul_eq_zero (RingHom.snd B C) _ ((0 : B), (1 : C)) rfl
    fun m => by rw [show ((0 : B), (1 : C)) • m = (0 : B) • m from rfl, zero_smul]

/-- **A map of `B × C`-modules whose two base changes are isomorphisms is an isomorphism.** The
`B × C`-module `M` is the direct sum of `B ⊗ M` and `C ⊗ M`, the two summands being cut out by
the orthogonal idempotents `(1, 0)` and `(0, 1)`. -/
theorem isIso_of_isIso_extendScalars_prod {M N : ModuleCat.{u} (B × C)} (g : M ⟶ N)
    (hB : IsIso ((ModuleCat.extendScalars (RingHom.fst B C)).map g))
    (hC : IsIso ((ModuleCat.extendScalars (RingHom.snd B C)).map g)) :
    IsIso g :=
  (ConcreteCategory.isIso_iff_bijective g).2
    (Module.bijective_of_bijective_baseChange_of_sections (prodSectionFst B C)
      (prodSectionSnd B C) (prodSectionFst_one_add_prodSectionSnd_one B C) g.hom
      ((ConcreteCategory.isIso_iff_bijective _).1 hB)
      ((ConcreteCategory.isIso_iff_bijective _).1 hC))

variable {ι : Type*} {c : ComplexShape ι}

/-- **A map of complexes of `B × C`-modules whose two base changes are quasi-isomorphisms is a
quasi-isomorphism.** Both base changes are exact, `B` and `C` being flat over `B × C`, so they
carry the homology of a complex to the base change of its homology; and a map of `B × C`-modules
whose two base changes are invertible is invertible. -/
theorem quasiIso_of_quasiIso_extendScalars_prod
    {K L : HomologicalComplex (ModuleCat.{u} (B × C)) c} (f : K ⟶ L)
    (hB : QuasiIso (((ModuleCat.extendScalars (RingHom.fst B C)).mapHomologicalComplex c).map f))
    (hC : QuasiIso (((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex c).map f)) :
    QuasiIso f := by
  have : (ModuleCat.extendScalars.{u, u, u} (RingHom.fst B C)).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} _ (RingHom.flat_fst B C)
  have : (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} _ (RingHom.flat_snd B C)
  exact ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap f i).2
    (isIso_of_isIso_extendScalars_prod _
      ((ModuleCat.extendScalars (RingHom.fst B C)).isIso_map_homologyMap f i
        ((quasiIsoAt_iff_isIso_homologyMap _ i).1 (hB.quasiIsoAt i)))
      ((ModuleCat.extendScalars (RingHom.snd B C)).isIso_map_homologyMap f i
        ((quasiIsoAt_iff_isIso_homologyMap _ i).1 (hC.quasiIsoAt i))))⟩

end ModuleCat

end
