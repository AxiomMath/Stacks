module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.TensorComplex.Monoidal

/-!
# The derived tensor product of modules is right t-exact, with no lower bound

Let `R` be a commutative ring and let `K`, `L` be objects of `D(R)` with `H^i(K) = 0` for
`i > a` and `H^j(L) = 0` for `j > b`.  Then `H^i(K ⊗ᴸ_R L) = 0` for `i > a + b`.  **Neither
factor is assumed bounded below**, and that is the whole point of the statement: it is the
*way-out right exactness* of `K ⊗ᴸ_R -` which
`StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut` asks of a functor in order to
count the top cohomological degree of an object that is bounded above only.

The companion statement for the modules of a ringed site is
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`; this is its module-category
reading, and the proof is the same two steps.  A bounded above object of `D(R)` is represented
by a complex of projective modules vanishing strictly above the bound ([stacks 05T7] for the
class of projective modules), such a complex is K-flat ([stacks 064K], projective modules being
flat), and the termwise tensor product of two complexes vanishing strictly above `a` and above
`b` vanishes strictly above `a + b`.

## The shape of the statement

The repository carries several derived tensor products of `ModuleCat R` — the construction of
[stacks 064M], the canonical bifunctor of [stacks 0BYI], and the tensor of a
`StacksDraft.DerivedHom.DerivedHomData` — and each of them used to prove this bound again for
itself.  What all of those proofs share is not a functor but a single object together with a
*comparison*: the value `T` of the operation at `K` and `L` is identified with `Q(P ⊗ Q)` for
K-flat representatives `P` of `K` and `Q` of `L`.  So the statement below takes `T` and that
comparison, and nothing else: no functoriality in either variable, no exactness, no shift
commutation.  Each of the three operations supplies the comparison in one line.

## Main results

* `CochainComplex.DerivedTensor.exists_projective_isStrictlyLE_representative` — [stacks 05T7]
  for the class of projective modules: an object of `D^{≤ a}(R)` is represented by a complex of
  projectives vanishing strictly above `a`.
* `CochainComplex.DerivedTensor.kFlat_of_projective_isStrictlyLE` — [stacks 064K] for such a
  complex: it is K-flat.
* `CochainComplex.DerivedTensor.isLE_of_kFlatComparison` — **the bound**: an object compared
  with the termwise tensor product of K-flat representatives of an object of `D^{≤ a}` and one
  of `D^{≤ b}` lies in `D^{≤ a + b}`.

## Implementation notes

The module universe `max u v` is independent of the ring's universe `u`, as in
`StacksFrontier.Algebra.Homology.KFlat`: a derived tensor product along a ring map `R → A` has to
accommodate the modules of both rings at once.  Taking `v := u` recovers the same-universe
reading, at which the comparison's `HomologicalComplex.tensorObj` is the monoidal product for
`ModuleCat.liftedModuleMonoidalStruct.{u, u}` — the instance that the same-universe call sites
pin by `attribute [local instance]`, so their own spellings of the comparison match this one on
the nose rather than merely up to `rfl`.

`HasDerivedCategory` is an instance binder at a free universe rather than
`HasDerivedCategory.standard` fixed locally, so that a call site which carries its own
instance can use the statement without transporting across an identification of two derived
categories.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v d

namespace CochainComplex.DerivedTensor

variable {R : Type u} [CommRing R]

/-- **[stacks 05T7] for the class of projective modules.**  An object of `D^{≤ a}(R)` is
represented by a complex of projective modules whose terms vanish strictly above `a`.

The class of projective modules contains a zero object and every module is a quotient of a
projective one, which is all [stacks 05T7] asks of it. -/
theorem exists_projective_isStrictlyLE_representative
    [HasDerivedCategory.{d} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ) [K.IsLE a] :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE a ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, e, hL⟩ := ‹K.IsLE a›
  let W : ObjectProperty (ModuleCat.{max u v} R) := fun X => Projective X
  let : W.ContainsZero := ⟨ModuleCat.of R (Fin 0 → ULift.{v} R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  obtain ⟨P, g, hq, hP, hPa⟩ := (CochainComplex.exists_quasiIso_prop W
    (fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩) a).2 L
  have := hq
  exact ⟨P, hP, hPa, ⟨e ≪≫ (asIso (DerivedCategory.Q.map g)).symm⟩⟩

/-- **[stacks 064K] for a bounded above complex of projectives.**  Projective modules are flat,
so such a complex is K-flat. -/
theorem kFlat_of_projective_isStrictlyLE (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    [P.IsStrictlyLE a] (hproj : ∀ i, Projective (P.X i)) : P.KFlat := by
  have hflat : ∀ i : ℤ, Module.Flat R (P.X i) := fun i => by
    have := hproj i
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat P a

/-- **The derived tensor product of modules is right t-exact, with no lower bound on either
factor.**

Let `K` be an object of `D^{≤ a}(R)` and `L` an object of `D^{≤ b}(R)`, and let `T` be an
object of `D(R)` which, for *some* pair of K-flat representatives `P` of `K` and `Q` of `L`, is
isomorphic to `Q(P ⊗ Q)` — the image of their termwise tensor product.  Then `T` lies in
`D^{≤ a + b}(R)`.

This is the bound every derived tensor product of `ModuleCat R` in the repository needs, stated
once: the comparison hypothesis is exactly what each of them has, and the bound is read off a
pair of representatives that the statement produces itself.  No lower bound appears anywhere,
which is what makes it the *way-out* right exactness that
`StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut` asks for.

The representatives produced are complexes of projectives vanishing strictly above `a`
respectively `b` ([stacks 05T7]), hence K-flat ([stacks 064K]), and their termwise tensor
product vanishes strictly above `a + b`, so `Q` of it lies in `D^{≤ a + b}`. -/
theorem isLE_of_kFlatComparison [HasDerivedCategory.{d} (ModuleCat.{max u v} R)]
    (T K L : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) [K.IsLE a] [L.IsLE b]
    (comparison : ∀ P Q : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (K ≅ DerivedCategory.Q.obj P) → (L ≅ DerivedCategory.Q.obj Q) → P.KFlat → Q.KFlat →
        Nonempty (T ≅ DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q))) :
    T.IsLE (a + b) := by
  obtain ⟨P, hP, hPa, ⟨eP⟩⟩ := exists_projective_isStrictlyLE_representative K a
  obtain ⟨Q, hQ, hQb, ⟨eQ⟩⟩ := exists_projective_isStrictlyLE_representative L b
  have := hPa
  have := hQb
  obtain ⟨e⟩ := comparison P Q eP eQ (kFlat_of_projective_isStrictlyLE P a hP)
    (kFlat_of_projective_isStrictlyLE Q b hQ)
  have := TotalTensorComplex.tensor_isStrictlyLE P Q a b
  have hmodel : (DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q)).IsLE (a + b) := by
    rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
    intro i hi
    exact ShortComplex.exact_of_isZero_X₂ _
      (CochainComplex.isZero_of_isStrictlyLE (HomologicalComplex.tensorObj P Q) (a + b) i hi)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (a + b)

end CochainComplex.DerivedTensor

end
