module

public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Algebra.Homology.ComplexShapeSignsNat
public import Mathlib.Algebra.Homology.Embedding.Extend
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.ImageFiltration
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# The wedge filtration of a complex with a multiplication

Let `𝒜` be an abelian category, let `F : 𝒜 ⥤ 𝒜 ⥤ 𝒜` be a bifunctor whose total complexes on
`ℕ`-indexed cochain complexes exist, let `Ω^•` be an `ℕ`-indexed cochain complex of `𝒜` and let

`μ : Tot(Ω^• ⊗ Ω^•) ⟶ Ω^•`

be a multiplication on it, where `⊗` is written for `F`.  Given a further complex `P^•` and a
morphism `ι : P^• ⟶ Ω^•`, the *wedge filtration of `Ω^•` along `ι`* has `k`-th step

`F^k Ω^• = Im (Tot(σ^{≥k}P^• ⊗ Ω^•) ⟶ Ω^•)`,

the image of `μ` restricted along `ι` on the `k`-th brutal truncation of `P^•`.  Because the
truncations are subcomplexes the source is a complex and the restricted multiplication is a
morphism of complexes, so each image is automatically a *sub*complex — which is the whole point of
describing the filtration this way: the Leibniz rule is implicit in it.

This module assembles exactly that datum, as a `CochainComplex.ImageSystem` over the `ℤ`-indexed
extension by zero of `Ω^•`.  The filtration itself — the images, their decreasingness, the step at
`k ≤ 0`, the exhaustion clause and the degreewise finiteness — is the generic construction of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.ImageFiltration`.

## Why it is stated for an arbitrary bifunctor

Two developments need this filtration and they do not share a tensor product.  Stacks Section
50.12, [Stacks, Tag 0FMK], needs it for sheaves of modules on a ringed site with `F` the tensor
product over the base ring sheaf; that instance is
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`.  The completed de Rham complexes of the
crystalline chapter, [Stacks, Tag 07LD] and [Stacks, Tag 07LG], need it for complexes whose terms
are objects of `AddCommGrpCat` — the completed modules with their module structure forgotten,
because the completed de Rham differential is not linear — with `F` the tensor product of abelian
groups.  There the wedge of a form of `Ω̂^i_D` against one of `M ⊗̂_D Ω̂^j_{D'}` is biadditive, so
it factors through the tensor product of abelian groups, and its image is the subgroup generated
by the products, which is the step of the filtration.  Stating the assembly once is what keeps
the second from being a copy of the first.

## Main definitions

* `CochainComplex.brutal`, `CochainComplex.ιBrutal` and `CochainComplex.brutalMap`: the brutal
  truncation `σ^{≥k}` of an `ℕ`-indexed cochain complex, as the subcomplex cut out by the
  subobjects `⊤` in degrees `≥ k` and `⊥` below, with its inclusion into the complex and the
  inclusions between successive truncations.
* `CochainComplex.wedgeAlong`: the wedge map `Tot(P^• ⊗ Ω^•) ⟶ Ω^•` attached to a morphism
  `ι : P^• ⟶ Ω^•`, namely `μ` with its left-hand factor restricted along `ι`.
* `CochainComplex.wedgeImageSystem`: **the system of wedge maps out of the brutal truncations of
  `P^•`**, as a `CochainComplex.ImageSystem` over the extension by zero of `Ω^•`.

## Main results

* `CochainComplex.brutalMap_ι`: the inclusions between truncations are compatible with the
  inclusions into the complex, which is what makes the images decrease.
* `CochainComplex.wedgeAlong_comp`: restricting the left-hand factor further factors the wedge
  map — the identity the `step_hom` field of the system is.
* `CochainComplex.isZero_wedgeSourceInt_X`: the `k`-th member `Tot(σ^{≥k}P^• ⊗ Ω^•)` of the
  system vanishes in every degree below `k`, the brutal truncation being stupid.
* `CochainComplex.isDegreewiseFinite_pairingImageSystem` and
  `CochainComplex.isDegreewiseFinite_wedgeImageSystem`: **the wedge filtration is degreewise
  finite**, with no hypothesis beyond those building the system.  This is what
  [Stacks, Tag 05S3] asks of a filtration before it will conclude from the graded pieces to the
  underlying morphism, and the last generic ingredient the wedge filtration of a de Rham complex
  owes it.

## Implementation notes

The ambient complex is the `ℤ`-indexed extension by zero
`ComplexShape.embeddingUpNat.extendFunctor`, because filtered complexes and the spectral sequence
of a filtered complex are stated for `ℤ`-indexed cochain complexes while the de Rham complexes and
their multiplications are `ℕ`-indexed.  The extension is a functor, so the images of the wedge maps
transport to it and the factorisations transport with them.

The step at `k ≤ 0` is `⊤` by definition rather than by a computation; this is
`CochainComplex.ImageSystem.filtrationStep`, and the docstring there records why.  Here it means
that the construction needs nothing of `μ` beyond its being a morphism of complexes — in
particular not that it is unital, which is what would otherwise be required to identify the image
at `k = 0` with the whole complex.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 012L](https://stacks.math.columbia.edu/tag/012L)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### The brutal truncation -/

/-- The subobject cutting out the degree-`n` term of the brutal truncation `σ^{≥k}`: everything
in degrees `≥ k`, and zero below. -/
public def brutalStep (L : CochainComplex C ℕ) (k n : ℕ) : Subobject (L.X n) :=
  if k ≤ n then ⊤ else ⊥

/-- The brutal truncation is stable under the differential: in degrees `≥ k` the condition is
vacuous, and below `k` either the source is zero or the differential is. -/
public theorem brutalStep_factors (L : CochainComplex C ℕ) (k i j : ℕ) :
    (brutalStep L k j).Factors ((brutalStep L k i).arrow ≫ L.d i j) := by
  by_cases hj : k ≤ j
  · simpa [brutalStep, hj] using Subobject.top_factors
      ((brutalStep L k i).arrow ≫ L.d i j)
  · have hz : (brutalStep L k i).arrow ≫ L.d i j = 0 := by
      by_cases hi : k ≤ i
      · rw [L.shape i j (by simp only [ComplexShape.up_Rel]; omega), comp_zero]
      · rw [brutalStep, if_neg hi, Subobject.bot_arrow, zero_comp]
    rw [hz]
    exact Subobject.factors_zero

/-- **The brutal truncation `σ^{≥k}L^•`** of an `ℕ`-indexed cochain complex: the subcomplex
which agrees with `L^•` in degrees `≥ k` and vanishes below `k`. -/
public def brutal (L : CochainComplex C ℕ) (k : ℕ) : CochainComplex C ℕ :=
  HomologicalComplex.subcomplexOfSubobjects L (brutalStep L k) (brutalStep_factors L k)

/-- The inclusion `σ^{≥k}L^• ⟶ L^•`. -/
public def ιBrutal (L : CochainComplex C ℕ) (k : ℕ) : brutal L k ⟶ L :=
  HomologicalComplex.subcomplexOfSubobjectsι L (brutalStep L k) (brutalStep_factors L k)

/-- The inclusion `σ^{≥k'}L^• ⟶ σ^{≥k}L^•` of brutal truncations, for `k ≤ k'`. -/
public def brutalMap (L : CochainComplex C ℕ) {k k' : ℕ} (h : k ≤ k') :
    brutal L k' ⟶ brutal L k :=
  HomologicalComplex.subcomplexOfSubobjectsMap L (brutalStep_factors L k')
    (brutalStep_factors L k) (fun n => by
      by_cases hn : k' ≤ n
      · simp [brutalStep, hn, show k ≤ n from le_trans h hn]
      · simp [brutalStep, hn])

/-- The inclusions between brutal truncations are compatible with the inclusions into `L^•`. -/
public theorem brutalMap_ι (L : CochainComplex C ℕ) {k k' : ℕ} (h : k ≤ k') :
    brutalMap L h ≫ ιBrutal L k = ιBrutal L k' :=
  HomologicalComplex.subcomplexOfSubobjectsMap_ι L _ _ _

/-! ### The brutal truncation vanishes below its index -/

/-- Below its index the brutal truncation vanishes: the subobject cutting out that degree is
`⊥`. -/
public theorem isZero_brutal_X (L : CochainComplex C ℕ) {k n : ℕ} (h : ¬ k ≤ n) :
    IsZero ((brutal L k).X n) := by
  show IsZero ((brutalStep L k n : C))
  rw [brutalStep, if_neg h]
  exact (isZero_zero C).of_iso Subobject.botCoeIsoZero

/-- **A bifunctor that preserves zero morphisms kills a zero object in its first variable.**
If `Z` is a zero object then `𝟙 Z = 0`, so `𝟙 (G.obj Z) = G.map (𝟙 Z) = G.map 0 = 0` in the
functor category, and a natural transformation that is zero is zero in every component.

Only `G.PreservesZeroMorphisms` is used, which is strictly weaker than the additivity assumed by
the same statement at `CochainComplex.KFlatBifunctor.isZero_obj_obj_of_isZero`; the wedge
filtration is built for a bifunctor that is merely biadditive on the nose, so the stronger form
is not available here and importing the K-flatness development for it would be out of
proportion. -/
private theorem isZero_obj_obj_of_isZero (G : C ⥤ C ⥤ C) [G.PreservesZeroMorphisms]
    {Z : C} (hZ : IsZero Z) (Y : C) : IsZero ((G.obj Z).obj Y) := by
  have hGZ : IsZero (G.obj Z) := by
    rw [IsZero.iff_id_eq_zero, ← G.map_id, hZ.eq_of_src (𝟙 Z) 0, G.map_zero]
  rw [IsZero.iff_id_eq_zero]
  exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hGZ) Y

/-! ### The wedge map along a morphism -/

section Wedge

variable (F : C ⥤ C ⥤ C) [F.PreservesZeroMorphisms]
  [∀ X : C, (F.obj X).PreservesZeroMorphisms]
  [∀ (K₁ K₂ : CochainComplex C ℕ), HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℕ)]

/-- The bifunctor `F` read on `ℕ`-indexed cochain complexes, by total complexes. -/
public abbrev bifunctorNat :
    CochainComplex C ℕ ⥤ CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  F.map₂HomologicalComplex (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)

variable {Ω : CochainComplex C ℕ} (mu : ((bifunctorNat F).obj Ω).obj Ω ⟶ Ω)

/-- **The wedge map `Tot(P^• ⊗ Ω^•) ⟶ Ω^•` along a morphism of complexes `ι : P^• ⟶ Ω^•`**: the
multiplication `μ` with its left-hand factor restricted along `ι`. -/
public def wedgeAlong (P : CochainComplex C ℕ) (iota : P ⟶ Ω) :
    ((bifunctorNat F).obj P).obj Ω ⟶ Ω :=
  ((bifunctorNat F).map iota).app Ω ≫ mu

/-- Restricting the left-hand factor further factors the wedge map. -/
public theorem wedgeAlong_comp {P Q : CochainComplex C ℕ} (psi : P ⟶ Q) (iota : Q ⟶ Ω) :
    wedgeAlong F mu P (psi ≫ iota) =
      ((bifunctorNat F).map psi).app Ω ≫ wedgeAlong F mu Q iota := by
  rw [wedgeAlong, wedgeAlong, Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- `Tot(σ^{≥k}P^• ⊗ Ω^•)`, extended by zero to a `ℤ`-indexed complex.  Named so that the types
of the maps out of it stay small.

`Ω^•` is an explicit argument here, unlike in the maps below: it does not occur in the other
arguments, so nothing would determine it. -/
public def wedgeSourceInt (Om P : CochainComplex C ℕ) (k : ℕ) : CochainComplex C ℤ :=
  (ComplexShape.embeddingUpNat.extendFunctor C).obj
    (((bifunctorNat F).obj (brutal P k)).obj Om)

/-- **The `k`-th member of the system vanishes in every degree below `k`.** This is what makes
the wedge filtration degreewise finite, and the reason is that the brutal truncation is a
*stupid* truncation: a summand of `Tot(σ^{≥k}P^• ⊗ Ω^•)` in total degree `m` is
`F(σ^{≥k}P^a, Ω^b)` with `a + b = m`, so `a ≤ m < k` and the left-hand factor is already a zero
object; `F` then kills it. In degrees `< 0` there is nothing to prove, the extension by zero
being zero off the image of `ComplexShape.embeddingUpNat`. -/
public theorem isZero_wedgeSourceInt_X (Om P : CochainComplex C ℕ) {k : ℕ} {n : ℤ}
    (h : n < k) : IsZero ((wedgeSourceInt F Om P k).X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · exact HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
      simp only [ComplexShape.embeddingUpNat_f] at hi
      omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine IsZero.of_iso ?_ (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
      (i := m) (by simp))
    refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ m fun a b hab => ?_
    have hab' : a + b = m := hab
    exact isZero_obj_obj_of_isZero F (isZero_brutal_X P (by omega)) _

/-- The extension by zero of the wedge map on the `k`-th brutal truncation of `P^•`, a morphism of
`ℤ`-indexed complexes into the extension by zero of `Ω^•`. -/
public def wedgeAlongBrutalInt (P : CochainComplex C ℕ) (iota : P ⟶ Ω) (k : ℕ) :
    wedgeSourceInt F Ω P k ⟶ (ComplexShape.embeddingUpNat.extendFunctor C).obj Ω :=
  (ComplexShape.embeddingUpNat.extendFunctor C).map
    (wedgeAlong F mu (brutal P k) (ιBrutal P k ≫ iota))

/-- **The system of wedge maps out of the brutal truncations of `P^•`**, as a
`CochainComplex.ImageSystem` over the extension by zero of `Ω^•`: the `k`-th member is
`Tot(σ^{≥k}P^• ⊗ Ω^•)`, its morphism is the wedge map, and the factorisations are the inclusions
`σ^{≥k'}P^• ⟶ σ^{≥k}P^•` tensored with `Ω^•`.  The wedge filtration is the filtration by the
images of this system, `CochainComplex.ImageSystem.filtered`. -/
public def wedgeImageSystem (P : CochainComplex C ℕ) (iota : P ⟶ Ω) :
    ImageSystem ((ComplexShape.embeddingUpNat.extendFunctor C).obj Ω) where
  source k := wedgeSourceInt F Ω P k
  hom k := wedgeAlongBrutalInt F mu P iota k
  step {_ _} h :=
    (ComplexShape.embeddingUpNat.extendFunctor C).map
      (((bifunctorNat F).map (brutalMap P h)).app Ω)
  step_hom {k k'} h := by
    have h0 : wedgeAlong F mu (brutal P k') (ιBrutal P k' ≫ iota) =
        ((bifunctorNat F).map (brutalMap P h)).app Ω ≫
          wedgeAlong F mu (brutal P k) (ιBrutal P k ≫ iota) := by
      rw [← brutalMap_ι P h, Category.assoc, wedgeAlong_comp]
    rw [wedgeAlongBrutalInt, wedgeAlongBrutalInt, h0, Functor.map_comp]
    rfl

/-! ### A pairing of two complexes, rather than a multiplication restricted along a map -/

/-- The restriction of a pairing `P^• ⊗ Ω^• ⟶ Ω^•` to the `k`-th brutal truncation of `P^•`,
extended by zero. -/
public def pairingBrutalInt (P : CochainComplex C ℕ)
    (pair : ((bifunctorNat F).obj P).obj Ω ⟶ Ω) (k : ℕ) :
    wedgeSourceInt F Ω P k ⟶ (ComplexShape.embeddingUpNat.extendFunctor C).obj Ω :=
  (ComplexShape.embeddingUpNat.extendFunctor C).map
    (((bifunctorNat F).map (ιBrutal P k)).app Ω ≫ pair)

/-- **The system of maps out of the brutal truncations of `P^•` cut out by a pairing**
`P^• ⊗ Ω^• ⟶ Ω^•`: the `k`-th member is `Tot(σ^{≥k}P^• ⊗ Ω^•)`, its morphism is the pairing
restricted to that truncation, and the factorisations are the inclusions
`σ^{≥k'}P^• ⟶ σ^{≥k}P^•` paired with `Ω^•`.

This is `CochainComplex.wedgeImageSystem` with the hypothesis that the pairing comes from a
*multiplication on `Ω^•` itself*, restricted along a morphism `ι : P^• ⟶ Ω^•`, dropped — and
that hypothesis is exactly what the crystalline chapter cannot supply.  There the ambient
complex is `M ⊗̂_D Ω̂^*_{D'}` of [Stacks, Tag 07LG] and the complex being filtered by is
`Ω̂^*_D`; the pairing wedges a form of the second against an element of the first and lands in
the first, which is a map out of a tensor product of two *different* complexes and is not the
restriction of any multiplication on one of them.  Writing the system in terms of the pairing
makes [Stacks, Tag 07LD] an instance of this module rather than a copy of it; `wedgeImageSystem`
is in turn the instance `pair = ((bifunctorNat F).map ι).app Ω ≫ μ`, which is what Section 50.12
supplies. -/
public def pairingImageSystem (P : CochainComplex C ℕ)
    (pair : ((bifunctorNat F).obj P).obj Ω ⟶ Ω) :
    ImageSystem ((ComplexShape.embeddingUpNat.extendFunctor C).obj Ω) where
  source k := wedgeSourceInt F Ω P k
  hom k := pairingBrutalInt F P pair k
  step {_ _} h :=
    (ComplexShape.embeddingUpNat.extendFunctor C).map
      (((bifunctorNat F).map (brutalMap P h)).app Ω)
  step_hom {k k'} h := by
    have h0 : ((bifunctorNat F).map (brutalMap P h)).app Ω ≫
          (((bifunctorNat F).map (ιBrutal P k)).app Ω ≫ pair) =
        ((bifunctorNat F).map (ιBrutal P k')).app Ω ≫ pair := by
      rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, brutalMap_ι P h]
    exact (Functor.map_comp (ComplexShape.embeddingUpNat.extendFunctor C) _ _).symm.trans
      (congrArg (ComplexShape.embeddingUpNat.extendFunctor C).map h0)

/-- **The wedge system is the pairing system of the restricted multiplication.**  The two
constructions agree member by member; this is the identity that makes `wedgeImageSystem` a
special case of `pairingImageSystem` rather than a second construction of the same shape. -/
public theorem pairingBrutalInt_wedgeAlong (P : CochainComplex C ℕ) (iota : P ⟶ Ω) (k : ℕ) :
    pairingBrutalInt F P (wedgeAlong F mu P iota) k = wedgeAlongBrutalInt F mu P iota k := by
  rw [pairingBrutalInt, wedgeAlongBrutalInt, wedgeAlong, wedgeAlong, ← Category.assoc,
    ← NatTrans.comp_app, ← Functor.map_comp]

/-! ### Degreewise finiteness -/

/-- In each degree `n`, the member of index `n.toNat + 1` of the wedge systems vanishes. -/
private theorem exists_isZero_wedgeSourceInt_X (Om P : CochainComplex C ℕ) (n : ℤ) :
    ∃ k : ℕ, IsZero ((wedgeSourceInt F Om P (k + 1)).X n) :=
  ⟨n.toNat, isZero_wedgeSourceInt_X F Om P (by omega)⟩

/-- **The filtration cut out by a pairing is degreewise finite**, with no hypothesis beyond those
building the system.  This is the last generic ingredient the wedge filtration of a de Rham
complex owes [Stacks, Tag 05S3] in the form
`CochainComplex.quasiIso_hom_of_filteredQuasiIso`, which concludes from the graded pieces of a
filtered complex to the underlying morphism only for filtrations finite in each degree — and the
counterexample in that declaration's docstring shows the hypothesis cannot be dropped.  Half of
it is free, the step at `0` being the whole complex by definition
(`CochainComplex.ImageSystem.isIso_filtered_ι_of_nonpos`); the other half is
`CochainComplex.isZero_wedgeSourceInt_X`, applied at `k = n.toNat`, so that the member of index
`k + 1` is already past the degree `n` whatever the sign of `n`.

It is stated here rather than in either consumer because both of them need it: Section 50.12,
[Stacks, Tag 0FMK], for sheaves of modules, and the completed de Rham complexes of
[Stacks, Tag 07LD]. -/
public theorem isDegreewiseFinite_pairingImageSystem (P : CochainComplex C ℕ)
    (pair : ((bifunctorNat F).obj P).obj Ω ⟶ Ω) :
    (pairingImageSystem F P pair).filtered.filtration.IsDegreewiseFinite :=
  ImageSystem.isDegreewiseFinite_filtered _
    (exists_isZero_wedgeSourceInt_X F Ω P)

/-- **The wedge filtration is degreewise finite.**  The wedge system has the same members as the
pairing system of `CochainComplex.isDegreewiseFinite_pairingImageSystem`, namely
`Tot(σ^{≥k}P^• ⊗ Ω^•)`, so the vanishing used there applies unchanged; only the morphisms out of
them differ, and degreewise finiteness does not see them. -/
public theorem isDegreewiseFinite_wedgeImageSystem (P : CochainComplex C ℕ) (iota : P ⟶ Ω) :
    (wedgeImageSystem F mu P iota).filtered.filtration.IsDegreewiseFinite :=
  ImageSystem.isDegreewiseFinite_filtered _
    (exists_isZero_wedgeSourceInt_X F Ω P)

end Wedge

end CochainComplex

end
