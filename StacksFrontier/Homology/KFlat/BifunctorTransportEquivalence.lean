module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.KFlat.BifunctorTransport

/-!
# Transporting a derived bifunctor, and invertibility, along an equivalence

Let `e : A ≌ A'` be an equivalence of abelian categories, let `F : A ⥤ A ⥤ A` and
`F' : A' ⥤ A' ⥤ A'` be additive bifunctors admitting K-flat resolutions in both variables, and
suppose `e` carries `F` to `F'`,

`e(F(a, b)) ≅ F'(e a, e b)`,

naturally in `a` and in `b` *at the level of the abelian categories*. Then

* `e` carries (left) K-flat complexes to (left) K-flat complexes, so the transport engine
  `CochainComplex.KFlatBifunctor.derivedTransportIso` applies and gives
  `e(F^𝐋(K, L)) ≅ F'^𝐋(e K, e L)` on arbitrary objects of the derived categories;
* `e` **reflects invertibility**: if `e K` is an invertible object of `D(A')` for a monoidal
  structure whose tensor product is `F'^𝐋` up to a pairwise comparison, then `K` is an
  invertible object of `D(A)` for one whose tensor product is `F^𝐋` up to a pairwise
  comparison, and `e` **preserves invertibility** in the opposite direction, from the same
  inputs. Which of the two a consumer needs depends only on which side its object lives on.

## Why an equivalence makes the K-flat hypotheses free

`CochainComplex.KFlatBifunctor.derivedTransportIso` asks its functors to carry K-flat complexes
to K-flat complexes, and that is not a formal consequence of carrying `F` to `F'`:
K-flatness of `L` quantifies over *all* acyclic complexes, and the acyclic complexes of the
target are not in general images of acyclic complexes of the source. For an equivalence they
are — an acyclic `G` of `A'` is `e(e⁻¹G)` with `e⁻¹G` acyclic, both functors being exact — and
the comparison at the single pair `(e⁻¹G, L)` then identifies `Tot(F'(G, e L))` with
`e(Tot(F(e⁻¹G, L)))`, which is acyclic. That is the whole proof of
`CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence`, and the mirror predicate is the same
argument in the other slot. So along an equivalence the *abelian*-level comparison alone
suffices to produce the derived one.

## Reflecting invertibility: why the abelian comparison is enough

`CategoryTheory.MonoidalCategory.isInvertible_of_isInvertible_obj_of_tensorComparison` reflects
invertibility along a full, faithful, essentially surjective functor carrying a pairwise tensor
comparison — no coherence, and in particular no monoidal structure on the functor. The three
properties hold here because `e.functor.mapDerivedCategory` is an equivalence
(`Stacks.Injectives.mapDerivedCategory_isEquivalence`), and the pairwise comparison is the
derived transport. So the only input a consumer has to produce is the abelian-level `ε`
together with the identification of the units.

**This is a shorter reduction than the one previously recorded.** The module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/GlobalInvertible.lean` named, as the
input the converse of [Stacks, Tag 0BFQ] clause (1)(a) is waiting on, "a pairwise tensor
comparison and a unit isomorphism for `AlgebraicGeometry.Scheme.Modules.overEquiv`" *on derived
categories*. Along an equivalence the derived comparison is not an extra input: it is produced
from the abelian one by the two statements below. The abelian-level comparison for
`overEquiv` — which for a restriction along a continuous and cocontinuous functor of sites is
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` — is
`Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso`, and the transport it feeds is
`Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv`. No bridge is
needed: `(overEquiv U).functor` *is* `whiskerRestriction` by `rfl`.

## Main definitions

* `CochainComplex.KFlatBifunctor.equivalenceCounitComplexIso`: the counit of `e`, read on
  cochain complexes.
* `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence` and
  `derivedTransportObjIsoOfEquivalence`: `e(F^𝐋(K, L)) ≅ F'^𝐋(e K, e L)`, as an isomorphism of
  bifunctors on the derived categories and at a pair of objects.

## Main results

* `CochainComplex.KFlatBifunctor.hasTotal_mapBicomplex_of_equivalence`: the transported double
  complex has a total complex, so that instance is not a burden on the consumer either.
* `CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence` and
  `kFlatLeft_map_of_equivalence`: an equivalence carrying `F` to `F'` carries K-flat complexes
  to K-flat complexes, in either variable.
* `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`: **the existence of
  K-flat resolutions transports along such an equivalence** — which is the hypothesis `hres` of
  `CochainComplex.KFlatMonoidal.derivedMonoidal`, so the derived monoidal structure transports
  with it.
* `CochainComplex.KFlatBifunctor.isInvertible_of_isInvertible_mapDerivedCategory`: **the
  transport of invertibility, in the reflecting direction.**
* `CochainComplex.KFlatBifunctor.isInvertible_mapDerivedCategory_of_isInvertible`: **the same
  transport in the preserving direction**, with the braiding asked of the target rather than of
  the source. Along an equivalence both directions are available from the same inputs, and a
  consumer carrying an object *into* the target needs this one.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.KFlatBifunctor

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ A' ⥤ A') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (e : A ≌ A') [e.functor.Additive] [e.inverse.Additive]

/-- **The counit of `e`, read on cochain complexes**: applying `e` to the image of a complex
under `e⁻¹` gives the complex back. The commutation with the differentials is the naturality of
the counit, so nothing is checked degreewise beyond that. -/
def equivalenceCounitComplexIso (G : CochainComplex A' ℤ) :
    (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj G) ≅ G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => e.counitIso.app (G.X i))
    (fun i j _ => by simp)

/-- A complex isomorphic to the image of an acyclic complex under `Φ` is acyclic. -/
private theorem acyclic_of_iso_map (Φ : A ⥤ A') [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ]
    {X : CochainComplex A ℤ} {Y : CochainComplex A' ℤ} (hX : X.Acyclic)
    (i : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj X ≅ Y) : Y.Acyclic :=
  fun n => HomologicalComplex.ExactAt.of_iso (hX.map Φ n) i

variable (ε : ∀ a b : A, e.functor.obj ((F.obj a).obj b) ≅
    (F'.obj (e.functor.obj a)).obj (e.functor.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    e.functor.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (e.functor.map f)).app (e.functor.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (g : b ⟶ b'),
    e.functor.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (e.functor.obj a)).map (e.functor.map g))

include ε hε₁ hε₂

omit [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] [e.inverse.Additive] in
/-- **The transported tensor double complex has a total complex.** It is isomorphic, degreewise
by `ε`, to the double complex computing `F'(e K, e L)`, which has one. A consumer therefore does
not have to supply this instance: it follows from the comparison, as does the preservation of
the antidiagonal coproducts, which holds because an equivalence preserves all colimits. -/
theorem hasTotal_mapBicomplex_of_equivalence (K L : CochainComplex A ℤ) :
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex e.functor
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso
    (Functor.mapBifunctorBicomplexIso F F' e.functor e.functor e.functor ε
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (fun f b => hε₁ f b)
      (fun a {_ _} g => hε₂ a g) K L).symm (ComplexShape.up ℤ)

/-- **An equivalence carrying `F` to `F'` carries K-flat complexes to K-flat complexes.**

K-flatness of `L` quantifies over the acyclic complexes of the source of `F`; along an
equivalence every acyclic complex `G` of `A'` is `e(e⁻¹G)` with `e⁻¹G` acyclic, and the
comparison at the pair `(e⁻¹G, L)` identifies `Tot(F'(G, e L))` with `e(Tot(F(e⁻¹G, L)))`. -/
theorem kFlat_map_of_equivalence (L : CochainComplex A ℤ) (hL : KFlat F L) :
    KFlat F' ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  let := fun K L => hasTotal_mapBicomplex_of_equivalence F F' e ε hε₁ hε₂ K L
  intro G hG
  exact acyclic_of_iso_map e.functor (hL _ (hG.map e.inverse))
    (transportComplexIso F F' e.functor e.functor e.functor ε hε₁ hε₂ _ L ≪≫
      ((F'.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).mapIso (equivalenceCounitComplexIso e G)).app _)

/-- **An equivalence carrying `F` to `F'` carries left K-flat complexes to left K-flat
complexes**, the mirror of `CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence` in the other
slot of the bifunctor, by the same argument. -/
theorem kFlatLeft_map_of_equivalence (K : CochainComplex A ℤ) (hK : KFlatLeft F K) :
    KFlatLeft F' ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let := fun K L => hasTotal_mapBicomplex_of_equivalence F F' e ε hε₁ hε₂ K L
  intro G hG
  exact acyclic_of_iso_map e.functor (hK _ (hG.map e.inverse))
    (transportComplexIso F F' e.functor e.functor e.functor ε hε₁ hε₂ K _ ≪≫
      ((F'.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj _).mapIso (equivalenceCounitComplexIso e G))

/-- **The existence of K-flat resolutions transports along an equivalence carrying `F` to `F'`.**

If every cochain complex over `A` receives a quasi-isomorphism from a complex K-flat for `F`,
then every cochain complex over `A'` receives one from a complex K-flat for `F'`. Given `G` over
`A'`, resolve `e⁻¹G` over `A` and apply `e`: the resolving complex stays K-flat by
`CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence`, the image of a quasi-isomorphism under
an exact functor is a quasi-isomorphism, and the counit
`CochainComplex.KFlatBifunctor.equivalenceCounitComplexIso` lands the result on `G` itself.

This is the hypothesis `hres` of `CochainComplex.KFlatMonoidal.derivedMonoidal`, so an
equivalence carries that hypothesis across and with it the derived monoidal structure. -/
theorem exists_kFlat_resolution_of_equivalence
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f)
    (G : CochainComplex A' ℤ) :
    ∃ (P : CochainComplex A' ℤ) (f : P ⟶ G), KFlat F' P ∧ QuasiIso f := by
  obtain ⟨P₀, f₀, hP₀, hf₀⟩ := hres ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
  exact ⟨_, (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
      (equivalenceCounitComplexIso e G).hom,
    kFlat_map_of_equivalence F F' e ε hε₁ hε₂ P₀ hP₀, inferInstance⟩

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory A']
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  [(kFlatQLeft F').IsLocalization (kFlatQuasiIsoLeft F')]
  [(kFlatQ F').IsLocalization (kFlatQuasiIso F')]

/-- **The derived bifunctor transported along an equivalence**: `e(F^𝐋(K, L)) ≅ F'^𝐋(e K, e L)`,
as an isomorphism of bifunctors on the derived categories.

This is `CochainComplex.KFlatBifunctor.derivedTransportIso` with its two K-flatness hypotheses
discharged by `kFlatLeft_map_of_equivalence` and `kFlat_map_of_equivalence`, which is what makes
the abelian-level comparison `ε` the only input. -/
def derivedTransportIsoOfEquivalence :
    derivedTransportSource F e.functor ≅ derivedTransportTarget F' e.functor e.functor :=
  letI := fun K L => hasTotal_mapBicomplex_of_equivalence F F' e ε hε₁ hε₂ K L
  derivedTransportIso F F' e.functor e.functor e.functor ε hε₁ hε₂
    (fun K hK => kFlatLeft_map_of_equivalence F F' e ε hε₁ hε₂ K hK)
    (fun L hL => kFlat_map_of_equivalence F F' e ε hε₁ hε₂ L hL)

/-- `e(F^𝐋(K, L)) ≅ F'^𝐋(e K, e L)` at a pair of objects of the derived categories, read off
`CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`. -/
def derivedTransportObjIsoOfEquivalence (K L : DerivedCategory A) :
    e.functor.mapDerivedCategory.obj (((derivedBifunctor F).obj K).obj L) ≅
      ((derivedBifunctor F').obj (e.functor.mapDerivedCategory.obj K)).obj
        (e.functor.mapDerivedCategory.obj L) :=
  ((derivedTransportIsoOfEquivalence F F' e ε hε₁ hε₂).app K).app L

/-- **An equivalence carrying `F` to `F'` reflects invertibility on the derived categories.**

The two monoidal structures are explicit arguments, each identified by a pairwise comparison of
its tensor product with the derived bifunctor; `unitε` identifies the images of the units. If
`e K` is an invertible object of `D(A')` then `K` is an invertible object of `D(A)`.

The reflecting direction is the one a transport along an equivalence needs. It is
`CategoryTheory.MonoidalCategory.isInvertible_of_isInvertible_obj_of_tensorComparison`, whose
full faithfulness and essential surjectivity hold because `e.functor.mapDerivedCategory` is an
equivalence, and whose pairwise comparison is
`CochainComplex.KFlatBifunctor.derivedTransportObjIsoOfEquivalence`. No coherence of the
comparison and no monoidal structure on the functor is used. -/
theorem isInvertible_of_isInvertible_mapDerivedCategory
    (mA : MonoidalCategory (DerivedCategory A))
    (mA' : MonoidalCategory (DerivedCategory A'))
    (bA : letI := mA; BraidedCategory (DerivedCategory A))
    (cmpA : letI := mA; ∀ X Y : DerivedCategory A,
      X ⊗ Y ≅ ((derivedBifunctor F).obj X).obj Y)
    (cmpA' : letI := mA'; ∀ X Y : DerivedCategory A',
      X ⊗ Y ≅ ((derivedBifunctor F').obj X).obj Y)
    (unitε : letI := mA; letI := mA';
      e.functor.mapDerivedCategory.obj (𝟙_ (DerivedCategory A)) ≅ 𝟙_ (DerivedCategory A'))
    (K : DerivedCategory A)
    (hK : letI := mA'; MonoidalCategory.IsInvertible
      (e.functor.mapDerivedCategory.obj K)) :
    letI := mA; MonoidalCategory.IsInvertible K :=
  let := mA
  let := mA'
  let := bA
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  MonoidalCategory.isInvertible_of_isInvertible_obj_of_tensorComparison
    e.functor.mapDerivedCategory
    (fun X Y => e.functor.mapDerivedCategory.mapIso (cmpA X Y) ≪≫
      derivedTransportObjIsoOfEquivalence F F' e ε hε₁ hε₂ X Y ≪≫ (cmpA' _ _).symm)
    unitε hK

/-- **An equivalence carrying `F` to `F'` preserves invertibility on the derived categories.**

This is the companion of
`CochainComplex.KFlatBifunctor.isInvertible_of_isInvertible_mapDerivedCategory` in the forward
direction: if `K` is an invertible object of `D(A)` then `e K` is an invertible object of
`D(A')`. The arguments are the same two monoidal structures with their pairwise comparisons
against the derived bifunctor and the identification of the units, except that the braiding is
now needed on the *target*: the forward transport is
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided`, which asks only
for the pairwise comparison — supplied by
`CochainComplex.KFlatBifunctor.derivedTransportObjIsoOfEquivalence` — and uses the braiding of
the target to turn a one-sided tensor inverse into a two-sided one. Full faithfulness and
essential surjectivity of `e.functor.mapDerivedCategory`, which the reflecting direction needs,
play no part here; the equivalence is used only to produce the derived comparison from the
abelian one. -/
theorem isInvertible_mapDerivedCategory_of_isInvertible
    (mA : MonoidalCategory (DerivedCategory A))
    (mA' : MonoidalCategory (DerivedCategory A'))
    (bA' : letI := mA'; BraidedCategory (DerivedCategory A'))
    (cmpA : letI := mA; ∀ X Y : DerivedCategory A,
      X ⊗ Y ≅ ((derivedBifunctor F).obj X).obj Y)
    (cmpA' : letI := mA'; ∀ X Y : DerivedCategory A',
      X ⊗ Y ≅ ((derivedBifunctor F').obj X).obj Y)
    (unitε : letI := mA; letI := mA';
      e.functor.mapDerivedCategory.obj (𝟙_ (DerivedCategory A)) ≅ 𝟙_ (DerivedCategory A'))
    (K : DerivedCategory A)
    (hK : letI := mA; MonoidalCategory.IsInvertible K) :
    letI := mA'; MonoidalCategory.IsInvertible (e.functor.mapDerivedCategory.obj K) :=
  let := mA
  let := mA'
  let := bA'
  MonoidalCategory.isInvertible_of_tensorComparison_of_braided
    e.functor.mapDerivedCategory
    (fun X Y => e.functor.mapDerivedCategory.mapIso (cmpA X Y) ≪≫
      derivedTransportObjIsoOfEquivalence F F' e ε hε₁ hε₂ X Y ≪≫ (cmpA' _ _).symm)
    unitε hK

end Derived

end CochainComplex.KFlatBifunctor

end
