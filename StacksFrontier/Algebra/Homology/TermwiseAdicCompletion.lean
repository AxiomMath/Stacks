module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksFrontier.Algebra.Homology.DoubleQuasiIso

/-!
# The termwise adic completion of a complex of modules

For an ideal `I` of a commutative ring `A`, the `I`-adic completion `M ↦ M^∧` is an additive
endofunctor of the category of `A`-modules, with a natural map `M ⟶ M^∧`. Applying it to each
term of a complex `K` gives the *termwise completion* `K^∧`, together with a map of complexes
`K ⟶ K^∧`.

The termwise completion of a complex is the limit of the complexes `K / Iⁿ K`. The form of this
used here is a lifting statement for cocycles in degree `1`. Let `(Kₙ)` be an inverse system of
complexes with compatible maps `πₙ : K ⟶ Kₙ`, each of which is surjective in every degree with
kernel `Iⁿ K`, so that `Kₙ = K / Iⁿ K`. If every cocycle of `K^∧` in degree `1` comes from a
cocycle of `K`, then every compatible family of degree-one cocycles of the `Kₙ` comes from a
single cocycle of `K`.

In the proof of Stacks 0EIF, `K` is the extended Čech complex of a finite module `M` on
generators of an ideal `J`, `Kₙ` is that of `M / IⁿM`, and the degree-one cocycles are the
sections over `Spec(A) ∖ V(J)`. So this is the step that turns a compatible family of sections
of the `F / IⁿF` into a single section of `F`.

## Main definitions

* `AdicCompletion.moduleCatFunctor`: the `I`-adic completion as an endofunctor of `A`-modules.
* `AdicCompletion.moduleCatOf`: the natural map `M ⟶ M^∧`.
* `HomologicalComplex.termwiseAdicCompletion`: the termwise completion `K^∧` of a complex.
* `HomologicalComplex.toTermwiseAdicCompletion`: the map of complexes `K ⟶ K^∧`.

## Main results

* `HomologicalComplex.exists_cyclesMap_eq_of_surjective_cyclesMap_toTermwiseAdicCompletion`:
  the lifting statement for degree-one cocycles described above.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AdicCompletion

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The `I`-adic completion as an endofunctor of `A`-modules.** It sends `M` to `M^∧` and a
linear map to its completion, with scalars restricted from `A^∧` to `A`. -/
def moduleCatFunctor : ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := ModuleCat.of A (AdicCompletion I M)
  map f := ModuleCat.ofHom ((AdicCompletion.map I f.hom).restrictScalars A)
  map_id M := by
    ext x
    simp [AdicCompletion.map_id]
  map_comp f g := by
    ext x
    simp

/-- The completion of a linear map `f` acts on `M^∧` as `AdicCompletion.map I f`. -/
@[simp]
theorem moduleCatFunctor_map_apply {M N : ModuleCat.{v} A} (f : M ⟶ N) (x : AdicCompletion I M) :
    ((moduleCatFunctor I).map f).hom x = AdicCompletion.map I f.hom x :=
  rfl

/-- The `I`-adic completion is an additive functor. -/
instance : (moduleCatFunctor.{v} I).Additive where
  map_add {M N f g} := by
    ext (x : AdicCompletion I M)
    change AdicCompletion.map I (f + g).hom x =
      AdicCompletion.map I f.hom x + AdicCompletion.map I g.hom x
    rw [ModuleCat.hom_add, map_add]
    rfl

/-- **The natural map `M ⟶ M^∧`** from a module to its `I`-adic completion. -/
def moduleCatOf : 𝟭 (ModuleCat.{v} A) ⟶ moduleCatFunctor I where
  app M := ModuleCat.ofHom (AdicCompletion.of I M)
  naturality M N f := by
    ext x
    change AdicCompletion.of I N (f.hom x) = AdicCompletion.map I f.hom (AdicCompletion.of I M x)
    rw [AdicCompletion.map_of]

/-- The natural map `M ⟶ M^∧` sends `x` to `AdicCompletion.of I M x`. -/
@[simp]
theorem moduleCatOf_app_apply (M : ModuleCat.{v} A) (x : M) :
    ((moduleCatOf I).app M).hom x = AdicCompletion.of I M x :=
  rfl

end AdicCompletion

namespace HomologicalComplex

variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type*} {c : ComplexShape ι}

/-- **The termwise `I`-adic completion `K^∧` of a complex of `A`-modules**: the completion of
every term, with the completions of the differentials. -/
abbrev termwiseAdicCompletion (K : HomologicalComplex (ModuleCat.{v} A) c) :
    HomologicalComplex (ModuleCat.{v} A) c :=
  ((AdicCompletion.moduleCatFunctor I).mapHomologicalComplex c).obj K

/-- **The map `K ⟶ K^∧` from a complex to its termwise completion**: in each degree the natural
map from a module to its `I`-adic completion. -/
def toTermwiseAdicCompletion (K : HomologicalComplex (ModuleCat.{v} A) c) :
    K ⟶ termwiseAdicCompletion I K where
  f i := (AdicCompletion.moduleCatOf I).app (K.X i)
  comm' i j _ := ((AdicCompletion.moduleCatOf I).naturality (K.d i j)).symm

/-- In degree `i`, the map `K ⟶ K^∧` sends `x` to `AdicCompletion.of I (K.X i) x`. -/
@[simp]
theorem toTermwiseAdicCompletion_f_apply (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι)
    (x : K.X i) :
    ((toTermwiseAdicCompletion I K).f i).hom x = AdicCompletion.of I (K.X i) x :=
  rfl

/-! ### Lifting compatible families of cocycles -/

section Lift

variable {K : CochainComplex (ModuleCat.{v} A) ℤ}
  (T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) (π : ∀ n : ℕ, K ⟶ T.obj (op n))

/-- **A compatible family of degree-one cocycles of the quotients `K / Iⁿ K` comes from a
cocycle of `K`**, as soon as every degree-one cocycle of the termwise completion `K^∧` comes from
a cocycle of `K`.

Here `(Kₙ)` is an inverse system of complexes indexed by `ℕᵒᵖ` and `πₙ : K ⟶ Kₙ` are compatible
maps, each surjective in every degree with kernel `Iⁿ K`.

The proof: choose preimages `yₙ` in `K¹` of the given cocycles. Their classes modulo `Iⁿ` are
compatible, so they form an element `x` of `(K¹)^∧`. Its differential vanishes modulo every
`Iⁿ`, because `πₙ` carries `d yₙ` to the differential of a cocycle, so `x` is a cocycle of
`K^∧`. A cocycle `w` of `K` lifting `x` agrees with `yₙ` modulo `Iⁿ`, so `πₙ w = πₙ yₙ`. -/
theorem exists_cyclesMap_eq_of_surjective_cyclesMap_toTermwiseAdicCompletion
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), π n ≫ T.map (homOfLE h).op = π m)
    (hsurj : ∀ (n : ℕ) (p : ℤ), Function.Surjective ((π n).f p).hom)
    (hker : ∀ (n : ℕ) (p : ℤ), LinearMap.ker ((π n).f p).hom = I ^ n • ⊤)
    (hZ : Function.Surjective (cyclesMap (toTermwiseAdicCompletion I K) 1).hom)
    (z : ∀ n : ℕ, (T.obj (op n)).cycles 1)
    (hz : ∀ (m n : ℕ) (h : m ≤ n), (cyclesMap (T.map (homOfLE h).op) 1).hom (z n) = z m) :
    ∃ w : K.cycles 1, ∀ n : ℕ, (cyclesMap (π n) 1).hom w = z n := by
  classical
  -- the transition maps of the system, read on the representatives
  have hπf (m n : ℕ) (h : m ≤ n) (p : ℤ) (y : K.X p) :
      ((T.map (homOfLE h).op).f p).hom (((π n).f p).hom y) = ((π m).f p).hom y := by
    rw [← hπ m n h]
    rfl
  have hiCycles {L L' : CochainComplex (ModuleCat.{v} A) ℤ} (φ : L ⟶ L') (a : L.cycles 1) :
      (L'.iCycles 1).hom ((cyclesMap φ 1).hom a) = (φ.f 1).hom ((L.iCycles 1).hom a) := by
    change ((cyclesMap φ 1) ≫ L'.iCycles 1).hom a = (L.iCycles 1 ≫ φ.f 1).hom a
    rw [cyclesMap_i]
  have hinj (L : CochainComplex (ModuleCat.{v} A) ℤ) :
      Function.Injective (L.iCycles 1).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hmem (n : ℕ) (p : ℤ) (y y' : K.X p) :
      ((π n).f p).hom y = ((π n).f p).hom y' ↔
        Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule A (K.X p))) y =
          Submodule.Quotient.mk y' := by
    rw [Submodule.Quotient.eq, ← hker n p, LinearMap.mem_ker, map_sub, sub_eq_zero]
  -- preimages of the given cocycles
  choose y hy using fun n => hsurj n 1 (((T.obj (op n)).iCycles 1).hom (z n))
  -- their classes form an element of the completion of `K¹`
  let x : AdicCompletion I (K.X 1) :=
    ⟨fun n => Submodule.Quotient.mk (y n), fun {m n} hmn => by
      change Submodule.Quotient.mk (y n) = Submodule.Quotient.mk (y m)
      refine (hmem m 1 (y n) (y m)).1 ?_
      rw [← hπf m n hmn, hy, hy, ← hiCycles, hz]⟩
  -- it is a cocycle of the termwise completion
  have hdx : ((termwiseAdicCompletion I K).d 1 2).hom x = 0 := by
    refine AdicCompletion.ext fun n => ?_
    change (AdicCompletion.map I (K.d 1 2).hom x).val n = 0
    rw [AdicCompletion.map_val_apply]
    change Submodule.Quotient.mk ((K.d 1 2).hom (y n)) = 0
    rw [← Submodule.Quotient.mk_zero]
    refine (hmem n 2 _ 0).1 ?_
    rw [map_zero]
    change ((K.d 1 2 ≫ (π n).f 2)).hom (y n) = 0
    rw [← (π n).comm 1 2]
    change ((T.obj (op n)).d 1 2).hom (((π n).f 1).hom (y n)) = 0
    rw [hy]
    change ((T.obj (op n)).iCycles 1 ≫ (T.obj (op n)).d 1 2).hom (z n) = 0
    rw [iCycles_d]
    rfl
  obtain ⟨c, hc⟩ := exists_iCycles_eq (termwiseAdicCompletion I K) 1 x
    (by rw [CochainComplex.next]; exact hdx)
  obtain ⟨w, hw⟩ := hZ c
  refine ⟨w, fun n => hinj _ ?_⟩
  rw [hiCycles, ← hy n]
  refine (hmem n 1 _ _).2 ?_
  have hx : AdicCompletion.of I (K.X 1) ((K.iCycles 1).hom w) = x := by
    rw [← toTermwiseAdicCompletion_f_apply, ← hiCycles, hw, hc]
  exact (congrArg (fun t : AdicCompletion I (K.X 1) => t.val n) hx :)

end Lift

end HomologicalComplex

end
