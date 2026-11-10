module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# Contravariant functoriality of the Hom complex, read on its homology

Let `C` be a preadditive category and let `K`, `L` be cochain complexes in `C` indexed by `ℤ`.
A morphism `f : K' ⟶ K` induces a morphism of Hom complexes `Hom^•(K, L) ⟶ Hom^•(K', L)` by
precomposition of cochains.  The degree-`n` homology of the Hom complex is the group of
degree-`n` cohomology classes, and this file records that the identification is compatible with
that morphism: the map it induces on homology is the map `cohomologyClassPrecomp` on cohomology
classes.

This is the contravariant half of the pair; the covariant half is `homComplexPostcomp` and
`homologyAddEquiv_postcomp` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/RightDerivedSheafToPresheaf.lean`, and the two
are stated in the root namespace next to `cohomologyClassPrecomp` and `cohomologyClassPostcomp`
for the same reason.

## Main definitions

* `homComplexPrecomp` is the morphism of Hom complexes induced by a morphism in the first
  variable.

## Main results

* `homologyAddEquiv_precomp`: `CochainComplex.HomComplex.homologyAddEquiv` turns the map induced
  on homology by `homComplexPrecomp f L` into `cohomologyClassPrecomp f L n`.

## Implementation notes

The proof is the one of `homologyAddEquiv_postcomp`: the projection from the cycles of a complex
onto its homology is an epimorphism of abelian groups, hence surjective, so it is enough to check
the two sides on the class of a cycle; the cycles of the Hom complex in degree `n` are the
degree-`n` cocycles by `CochainComplex.HomComplex.leftHomologyData`, and
`CategoryTheory.ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom` says that the
identification carries the class of a cycle to the cohomology class of the corresponding cocycle.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition with `f : K' ⟶ K` on cochains, as an additive map
`Cochain K L n →+ Cochain K' L n`. -/
def cochainPrecompAddMonoidHom {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n →+ CochainComplex.HomComplex.Cochain K' L n where
  toFun z := (Cochain.ofHom f).comp z (zero_add n)
  map_zero' := Cochain.comp_zero _ (zero_add n)
  map_add' z w := Cochain.comp_add (Cochain.ofHom f) z w (zero_add n)

/-- Precomposition with `f : K' ⟶ K`, as a morphism of Hom complexes
`Hom^•(K, L) ⟶ Hom^•(K', L)`.  On cohomology classes it induces `cohomologyClassPrecomp`. -/
def homComplexPrecomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K) (L : CochainComplex C ℤ) :
    K.HomComplex L ⟶ K'.HomComplex L where
  f n := AddCommGrpCat.ofHom (cochainPrecompAddMonoidHom f L n)
  comm' _ m _ := by
    ext z
    exact δ_ofHom_comp f z m

/-- The degree-`n` component of `homComplexPrecomp f L` precomposes a cochain with `f`. -/
lemma homComplexPrecomp_f_apply {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : CochainComplex.HomComplex.Cochain K L n) :
    (homComplexPrecomp f L).f n z = (Cochain.ofHom f).comp z (zero_add n) := rfl

/-- `homologyAddEquiv` sends the class of a cycle to the cohomology class of the cocycle. -/
private theorem homologyAddEquiv_homologyπ (K L : CochainComplex C ℤ) (n : ℤ)
    (z : (K.HomComplex L).cycles n) :
    homologyAddEquiv K L n ((K.HomComplex L).homologyπ n z) =
      CohomologyClass.mk ((leftHomologyData K L n).cyclesIso.hom z) :=
  ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom ((K.HomComplex L).sc n)
      (leftHomologyData K L n)) z

/-- **The identification `Hⁿ(Hom^•(K, L)) ≃+ CohomologyClass K L n` of
`CochainComplex.HomComplex.homologyAddEquiv` turns the map induced on homology by
`homComplexPrecomp f L` into `cohomologyClassPrecomp f L n`.** -/
theorem homologyAddEquiv_precomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (η : (K.HomComplex L).homology n) :
    cohomologyClassPrecomp f L n (homologyAddEquiv K L n η) =
      homologyAddEquiv K' L n
        ((HomologicalComplex.homologyMap (homComplexPrecomp f L) n) η) := by
  let h := leftHomologyData K L n
  let h' := leftHomologyData K' L n
  have hπ : Function.Surjective (ConcreteCategory.hom ((K.HomComplex L).homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ η
  let a : CochainComplex.HomComplex.Cocycle K L n := h.cyclesIso.hom z
  have hmap :
      h'.cyclesIso.hom ((HomologicalComplex.cyclesMap (homComplexPrecomp f L) n) z) =
        a.precomp f := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (homComplexPrecomp f L) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexPrecomp f L) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans ?_
    refine h2.trans ?_
    change (Cochain.ofHom f).comp ((HomologicalComplex.iCycles (K.HomComplex L) n) z)
        (zero_add n) = (Cochain.ofHom f).comp a.1 (zero_add n)
    congr 1
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexPrecomp f L) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat, homologyAddEquiv_homologyπ, homologyAddEquiv_homologyπ, hmap]
  exact cohomologyClassPrecomp_mk ..

end
