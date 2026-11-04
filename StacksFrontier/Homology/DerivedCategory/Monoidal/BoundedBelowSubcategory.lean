module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The bounded below derived category as a full monoidal subcategory

`CochainComplex.KFlatMonoidal.derivedMonoidal` makes the *unbounded* derived category `D(A)` of
a monoidal abelian category monoidal under the derived tensor product.  `DerivedCategory.Plus A`
is, by its Mathlib definition, the full subcategory
`(DerivedCategory.TStructure.t).plus.FullSubcategory` of `D(A)` on the objects whose cohomology
vanishes in all sufficiently negative degrees, so the only honest monoidal structure on it is
the one `CategoryTheory.ObjectProperty.fullMonoidalSubcategory` induces, and that needs
`CategoryTheory.ObjectProperty.IsMonoidal` for the object property
`(DerivedCategory.TStructure.t).plus`: the unit is bounded below, and a tensor product of two
bounded below objects is bounded below.

**The first half is unconditional and is proved here.**  The second half is not, and it is not a
formality: it is *false* for a general monoidal abelian category.  Over `A = ModuleCat k[x]/(x²)`
the residue field `k` sits in `D^{≥ 0}` while `H^{-i}(k ⊗ᴸ k) = Tor_i(k, k) ≠ 0` for every
`i ≥ 0`, so `k ⊗ᴸ k` lies in no `D^{≥ n}` at all.  The derived tensor product is right t-exact,
not left t-exact; the direction that holds with no extra hypothesis is the *bounded above* one,
`D^{≤ a} ⊗ᴸ D^{≤ b} ⊆ D^{≤ a + b}`, which this library records as
`CochainComplex.DerivedTensor.isLE_tensor` for modules and as
`Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor` for the modules of a ringed site.  In
the bounded below direction the same library states the bound only with a Tor-amplitude
hypothesis on one factor, in
`Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE`, and that is the
shape the mathematics forces.

What makes the gap precise is the step where a bounded below *complex* becomes a bounded below
*derived* object.  Degreewise the bound is trivial — `isStrictlyGE_tensorObj` below — but the
derived tensor product of two classes is computed from **K-flat** representatives, and a complex
that is bounded below need not have a K-flat resolution that is bounded below.  So the content of
the missing half is exactly the existence of such resolutions, and that is the hypothesis `hGE`
of `tensorLE_plus`: everything else is discharged here.  For abelian sheaves `hGE` is true, with
`a' = a - 1`, because an abelian sheaf is a quotient of a sheafified direct sum of copies of
`ℤ_U`, a subsheaf of a torsion-free abelian sheaf is torsion-free, and a torsion-free abelian
sheaf is flat — so abelian sheaves have flat dimension at most one.  None of that is formalized
here or anywhere in this library, and it is what separates `DerivedCategory.Plus` from
`DerivedCategory` for the derived tensor product.

## Main results

* `CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj`: **the degreewise bound** — the total
  tensor complex of a complex vanishing below `a` and a complex vanishing below `b` vanishes
  below `a + b`.  Every summand `Kᵖ ⊗ Lᵖ'` of a term in a degree below `a + b` has `p < a` or
  `p' < b`, so one factor vanishes.
* `CochainComplex.KFlatMonoidal.isGE_tensorUnit`,
  `CochainComplex.KFlatMonoidal.containsUnit_plus`: **the unit of `D(A)` is bounded below**,
  being the image of the unit of `Comp(A)`, which is `𝟙_ A` placed in degree `0`.  This is the
  half of `ObjectProperty.IsMonoidal` that holds unconditionally.
* `CochainComplex.KFlatMonoidal.isGE_tensor_Q_obj_of_kFlat`: **the bound at K-flat
  representatives** — for K-flat complexes the derived tensor product of their classes is the
  class of their total tensor complex, so the degreewise bound transports to `D(A)`.  This is
  unconditional, and it is the whole of the bounded below bound that does not need resolutions.
* `CochainComplex.KFlatMonoidal.tensorLE_plus`,
  `CochainComplex.KFlatMonoidal.isMonoidal_plus`: the remaining half and the conjunction, from
  the existence of bounded below K-flat resolutions.
* `CochainComplex.KFlatMonoidal.derivedPlusMonoidal`: **`DerivedCategory.Plus A` is monoidal**,
  as the full monoidal subcategory of `D(A)` on the bounded below objects, under the same
  hypothesis.
* `CochainComplex.KFlatMonoidal.derivedPlusMonoidalι`: the inclusion
  `DerivedCategory.Plus.ι` is a monoidal functor for that structure, which is what says the
  tensor product constructed is the derived tensor product of `D(A)` and not some other
  operation.

## Implementation notes

`CochainComplex.KFlatMonoidal.derivedMonoidal` takes the existence of K-flat resolutions as an
explicit argument, so the monoidal structure on `D(A)` cannot be seated globally and every
statement below carries `letI := derivedMonoidal A hres` in its type and again in its body — a
`letI` in a type is not in scope in the body.  That is also why `derivedPlusMonoidal` is a
`@[instance_reducible] def` taking its hypotheses explicitly rather than an instance: a global
`MonoidalCategory (DerivedCategory.Plus A)` would in any case clash with structures induced from
other monoidal structures on `A`.

`isStrictlyGE_tensorObj` is stated at the spelling `K ⊗ L` of
`HomologicalComplex.Monoidal.tensorObj` rather than at
`HomologicalComplex.mapBifunctor K L (curriedTensor A) (ComplexShape.up ℤ)`.  The two are the
same by `rfl` but not syntactically, and mixing them inside one file makes `rw` fail on a goal
that prints correctly; `HomologicalComplex.mapBifunctor.hom_ext` applies through the `abbrev`
without help.

## References

* [The Stacks Project, Tag 06YI](https://stacks.math.columbia.edu/tag/06YI)
* [The Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Triangulated

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-! ### The degreewise bound -/

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The total tensor complex of a complex vanishing below `a` and a complex vanishing below `b`
vanishes below `a + b`.**  Each summand `K.X p ⊗ L.X q` of the term in a degree `i < a + b` has
`p < a` or `q < n`, so one of its factors vanishes and the summand vanishes with it. -/
theorem isStrictlyGE_tensorObj (K L : CochainComplex A ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE b] :
    (K ⊗ L).IsStrictlyGE (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((curriedTensor A).obj (K.X p)).obj (L.X q)) := by
    by_cases hp : p < a
    · exact ((curriedTensor A).map_isZero (K.isZero_of_isStrictlyGE a p hp)).obj _
    · exact ((curriedTensor A).obj (K.X p)).map_isZero
        (L.isZero_of_isStrictlyGE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

section Monoidal

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-! ### The unit is bounded below -/

/-- **The unit of the derived tensor product of `D(A)` is bounded below**, with bound `0`: by
`CochainComplex.KFlatMonoidal.derivedUnitIso` it is the image of the unit of `Comp(A)`, which is
`𝟙_ A` placed in degree `0`. -/
theorem isGE_tensorUnit :
    letI := derivedMonoidal A hres
    (𝟙_ (DerivedCategory A)).IsGE 0 := by
  let := derivedMonoidal A hres
  let : CochainComplex.IsStrictlyGE (𝟙_ (CochainComplex A ℤ)) 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (𝟙_ A)) 0)
  exact DerivedCategory.TStructure.t.isGE_of_iso (derivedUnitIso A hres).symm 0

/-- **The bounded below objects of `D(A)` contain the unit of the derived tensor product.**  This
is the half of `CategoryTheory.ObjectProperty.IsMonoidal` for `t.plus` that needs no hypothesis
beyond the ones `CochainComplex.KFlatMonoidal.derivedMonoidal` already asks for. -/
theorem containsUnit_plus :
    letI := derivedMonoidal A hres
    (DerivedCategory.TStructure.t (C := A)).plus.ContainsUnit := by
  let := derivedMonoidal A hres
  exact ⟨⟨0, isGE_tensorUnit A hres⟩⟩

/-! ### The bound at K-flat representatives -/

/-- **The derived tensor product of the classes of two K-flat complexes vanishing below `a` and
below `b` is bounded below by `a + b`.**  On K-flat complexes the derived tensor product is the
image of the total tensor complex
(`CochainComplex.KFlatMonoidal.derivedTensorIso`), so this is `isStrictlyGE_tensorObj` read in
`D(A)`.  No resolution is used, and no hypothesis beyond K-flatness of the two complexes: this
is the whole of the bounded below bound that does not need a bounded below K-flat resolution. -/
theorem isGE_tensor_Q_obj_of_kFlat {K L : CochainComplex A ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE b]
    (hK : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L).IsGE (a + b) := by
  let := derivedMonoidal A hres
  let := isStrictlyGE_tensorObj A K L a b
  exact DerivedCategory.TStructure.t.isGE_of_iso (derivedTensorIso A hres hK hL).symm (a + b)

/-! ### The remaining half, and the full monoidal subcategory -/

/-- **The bounded below objects of `D(A)` are stable under the derived tensor product, as soon as
a complex which is bounded below admits a K-flat resolution which is bounded below.**

That hypothesis is the only input: a bounded below object of `D(A)` is the class of a complex
vanishing below some `a`, `hGE` replaces that complex by a K-flat one vanishing below some `a'`,
`CochainComplex.KFlatMonoidal.derivedTensorIso` computes the derived tensor product of the two
classes as the class of the total tensor complex, and `isStrictlyGE_tensorObj` bounds that below
by `a' + b'`.

The hypothesis is *not* vacuous and *not* automatic.  For `A = ModuleCat k[x]/(x²)` it fails,
and so does the conclusion: `k` lies in `D^{≥ 0}` and `k ⊗ᴸ k` lies in no `D^{≥ n}`.  For
abelian sheaves it holds with `a' = a - 1`, abelian sheaves having flat dimension at most one. -/
theorem tensorLE_plus
    (hGE : ∀ (a : ℤ) (G : CochainComplex A ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex A ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f) :
    letI := derivedMonoidal A hres
    (DerivedCategory.TStructure.t (C := A)).plus.TensorLE
      (DerivedCategory.TStructure.t (C := A)).plus
      (DerivedCategory.TStructure.t (C := A)).plus := by
  let := derivedMonoidal A hres
  refine ⟨fun X Y hX hY => ?_⟩
  obtain ⟨a, hXa⟩ := hX
  obtain ⟨b, hYb⟩ := hY
  obtain ⟨K, hKge, ⟨eX⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE X a
  obtain ⟨L, hLge, ⟨eY⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE Y b
  obtain ⟨a', P, f, hPge, hPflat, hf⟩ := hGE a K hKge
  obtain ⟨b', P', g, hP'ge, hP'flat, hg⟩ := hGE b L hLge
  let := hf
  let := hg
  let := hPge
  let := hP'ge
  let := isGE_tensor_Q_obj_of_kFlat A hres (K := P) (L := P') a' b' hPflat hP'flat
  refine ⟨a' + b', DerivedCategory.TStructure.t.isGE_of_iso
    ((asIso (DerivedCategory.Q.map f) ≪≫ eX.symm) ⊗ᵢ
      (asIso (DerivedCategory.Q.map g) ≪≫ eY.symm)) (a' + b')⟩

/-- **The bounded below objects of `D(A)` are a monoidal object property**, given bounded below
K-flat resolutions: `containsUnit_plus` for the unit, `tensorLE_plus` for the tensor product. -/
theorem isMonoidal_plus
    (hGE : ∀ (a : ℤ) (G : CochainComplex A ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex A ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f) :
    letI := derivedMonoidal A hres
    (DerivedCategory.TStructure.t (C := A)).plus.IsMonoidal := by
  let := derivedMonoidal A hres
  let := containsUnit_plus A hres
  let := tensorLE_plus A hres hGE
  exact { }

/-- **The bounded below derived category of `A` is monoidal**, under the derived tensor product
of `D(A)`, given bounded below K-flat resolutions.

`DerivedCategory.Plus A` is the full subcategory of `D(A)` on the bounded below objects, so this
is `CategoryTheory.ObjectProperty.fullMonoidalSubcategory` at the object property
`(DerivedCategory.TStructure.t).plus`, whose monoidality is `isMonoidal_plus`.  The tensor
product of the result is therefore the derived tensor product of `D(A)` on the nose —
`derivedPlusMonoidalι` records that as the monoidality of the inclusion. -/
@[instance_reducible] def derivedPlusMonoidal
    (hGE : ∀ (a : ℤ) (G : CochainComplex A ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex A ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory.Plus A) :=
  letI := derivedMonoidal A hres
  letI := isMonoidal_plus A hres hGE
  ObjectProperty.fullMonoidalSubcategory (DerivedCategory.TStructure.t (C := A)).plus

/-- **The inclusion of the bounded below derived category into `D(A)` is a monoidal functor**
for `derivedPlusMonoidal`.  This is what identifies the structure of `derivedPlusMonoidal` as
the derived tensor product rather than as some other monoidal structure on the same category:
the comparison isomorphisms are identities. -/
@[instance_reducible] def derivedPlusMonoidalι
    (hGE : ∀ (a : ℤ) (G : CochainComplex A ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex A ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f) :
    letI := derivedMonoidal A hres
    letI := derivedPlusMonoidal A hres hGE
    (DerivedCategory.Plus.ι (C := A)).Monoidal :=
  letI := derivedMonoidal A hres
  letI := isMonoidal_plus A hres hGE
  ObjectProperty.monoidalι (DerivedCategory.TStructure.t (C := A)).plus

end Monoidal

end CochainComplex.KFlatMonoidal

end
