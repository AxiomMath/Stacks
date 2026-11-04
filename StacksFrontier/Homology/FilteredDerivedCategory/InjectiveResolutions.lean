module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The filtered derived category and filtered injective resolutions

Let `𝒜` be an abelian category with enough injectives. Every bounded below filtered complex with
finite filtrations has a filtered injective resolution, a filtered quasi-isomorphism to a bounded
below complex of filtered injective objects, and the underlying complex of a complex of filtered
injective objects is a complex of injective objects.

For an additive functor `T : 𝒜 ⥤ ℬ` the filtered right derived functor of a
filtered complex `K^•` is computed by `T(I^•)`, filtered by the `T(F^p I^•)`, for any filtered
injective resolution `K^• ⟶ I^•`. The spectral sequence of this filtered complex
([Stacks, Tag 012M]) has `E_1^{p,q} = H^{p+q}(gr^p T(I^•)) = H^{p+q}(T(gr^p I^•))`, which is
`R^{p+q}T(gr^p K^•)` because `gr^p K^• ⟶ gr^p I^•` is an injective resolution; the filtration of
`T(I^•)` being finite in each degree, the spectral sequence is bounded and converges to
`H^*(T(I^•)) = R^*T(K^•)` ([Stacks, Tag 012W]). This is [Stacks, Tag 015W].

## Main definitions

* `CategoryTheory.FilteredObject.mapOfMono`: the image of a filtered object under a functor
  sending the inclusions of the filtration steps to monomorphisms.
* `CochainComplex.mapFilteredInjective`: the filtered complex `T(I^•)` for `I^•` a complex of
  filtered injective objects.

## Main results

* `CochainComplex.gradedPieceMapFilteredInjectiveIso`: `gr^p T(I^•) ≅ T(gr^p I^•)`.
* `CochainComplex.exists_spectralSequenceMap_rightDerivedFunctorPlus`,
  `CochainComplex.filteredHomotopic_comp_and_spectralSequenceMap_comp`,
  `CochainComplex.isIso_spectralSequenceMap_rightDerivedFunctorPlus`: its functoriality and
  independence of choices.
* `CochainComplex.exists_spectralSequence_rightDerivedFunctorPlus`: the spectral sequence
  `E_1^{p,q} = R^{p+q}T(gr^p K^•) ⇒ R^{p+q}T(K^•)` of [Stacks, Tag 015W], bounded and convergent,
  with finite induced filtration on the abutment.

## Implementation notes

*`T` is additive.* The source assumes `T` left exact; only additivity is used, since for a
complex `I^•` of filtered injective objects the inclusions `F^p I^n ⟶ I^n` and the sequences
`0 → F^{p+1} I^n → F^p I^n → gr^p I^n → 0` are split, and additive functors preserve split
monomorphisms and split short exact sequences. The filtered complex `T(I^•)` filtered by
`T(F^p I^•)` is therefore a filtered complex with `gr^p T(I^•) ≅ T(gr^p I^•)`, and it stands in
for `T_ext(I^•)` of [Stacks, Tag 05U0], to which it is isomorphic.

*Functoriality.* A morphism `f : K^• ⟶ L^•` lifts, up to filtered homotopy, to a morphism
`γ : I^• ⟶ J^•` of filtered injective resolutions ([Stacks, Tag 05TY]); `T(γ)` induces a morphism
of spectral sequences ([Stacks, Tag 012O]), which on the pages `E_r`, `r ≥ 1`, depends only on
`f`, since filtered homotopic maps induce the same maps there. This gives the functoriality, the
compatibility with composition and the independence of the choice of resolution.

*The spectral sequence is presented by its pages.* As in [Stacks, Tag 012M] and
[Stacks, Tag 012W], the spectral sequence is pinned by isomorphisms of its pages with the
quotients `Z_r^{p,q}/D_r^{p,q}` of subobjects of `T(I^n)` and by the compatibility of its
differentials with the differential of `T(I^•)`; `R^nT(X)` for a bounded below complex `X` is the
`n`-th cohomology of `RT(X) ∈ D⁺(ℬ)`.

## References

* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
* [Stacks Project, Tag 015W](https://stacks.math.columbia.edu/tag/015W)
* [Stacks Project, Tag 015T](https://stacks.math.columbia.edu/tag/015T)
* [Stacks Project, Tag 05TW](https://stacks.math.columbia.edu/tag/05TW)
* [Stacks Project, Tag 05TY](https://stacks.math.columbia.edu/tag/05TY)
* [Stacks Project, Tag 05U0](https://stacks.math.columbia.edu/tag/05U0)
* [Stacks Project, Tag 05U2](https://stacks.math.columbia.edu/tag/05U2)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v v' u u' w w'

namespace CochainComplex

section Injective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- In a filtered complex whose filtration is finite in degree `n` and all of whose graded pieces
are injective in degree `n`, every step `F^p K^n` of the filtration is injective. -/
lemma injective_filtration_obj_X_of_injective_gr (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (n : ℤ) (hK : ∃ q : ℤ, IsZero ((K.filtration.obj (op q)).X n))
    (hgr : ∀ p : ℤ, Injective (((FilteredObject.gr p).obj K).X n)) (p : ℤ) :
    Injective ((K.filtration.obj (op p)).X n) := by
  obtain ⟨q, hq⟩ := hK
  by_cases hpq : p ≤ q
  · exact Stacks.FilteredDerived.ForgetCommutes.injective_filtration_obj_X_of_isZero K n q hq hgr
      (q - p).toNat p (by omega)
  · exact (hq.of_mono ((K.filtration.step (opHomOfLE (not_le.1 hpq).le)).f n)).injective

end Injective


end CochainComplex

namespace CategoryTheory.FilteredObject

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {I : Type*} [Category* I]

/-- The image `G(A)` of a filtered object `A` under a functor `G` which sends each inclusion
`F^i A ⟶ A` to a monomorphism: the object `G(A.X)` filtered by the subobjects `G(F^i A)`. -/
@[implicit_reducible]
def mapOfMono (G : C ⥤ D) (A : FilteredObject C I)
    (h : ∀ i, Mono (G.map (A.filtration.ι.app i))) : FilteredObject D I where
  X := G.obj A.X
  filtration := ⟨{
    obj i := MonoOver.mk (G.map (A.filtration.ι.app i))
    map f := MonoOver.homMk (G.map (A.filtration.step f)) (by
      simp [← G.map_comp])
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }⟩

variable (G : C ⥤ D) (A : FilteredObject C I) (h : ∀ i, Mono (G.map (A.filtration.ι.app i)))

/-- The underlying object of `G(A)` is `G` of the underlying object of `A`. -/
@[simp] lemma mapOfMono_X : (A.mapOfMono G h).X = G.obj A.X := rfl
/-- The `i`-th step of `G(A)` is `G(F^i A)`. -/
lemma mapOfMono_filtration_obj (i : I) :
    (A.mapOfMono G h).filtration.obj i = G.obj (A.filtration.obj i) := rfl
/-- The inclusion of the `i`-th step of `G(A)` is `G` of the inclusion `F^i A ⟶ A`. -/
@[simp] lemma mapOfMono_filtration_ι_app (i : I) :
    (A.mapOfMono G h).filtration.ι.app i = G.map (A.filtration.ι.app i) := rfl
/-- The steps of `G(A)` are `G` of the steps of `A`. -/
@[simp] lemma mapOfMono_filtration_step {i j : I} (f : i ⟶ j) :
    (A.mapOfMono G h).filtration.step f = G.map (A.filtration.step f) := rfl

end CategoryTheory.FilteredObject

namespace CochainComplex

section

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  (T : A ⥤ B) [T.Additive]

/-- An additive functor `T` preserves the cokernel of a monomorphism `f : X ⟶ Y` of cochain
complexes whose source has injective terms: in each degree `0 → X^n → Y^n → Coker(f)^n → 0` is
short exact with `X^n` injective, hence split, and `T` preserves split short exact sequences. -/
noncomputable def cokernelMapIsoOfInjective {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f]
    (hX : ∀ n, Injective (X.X n)) :
    cokernel ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj (cokernel f) := by
  let S : ShortComplex (CochainComplex A ℤ) := ShortComplex.mk f (cokernel.π f) (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hS' : (S.map (T.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
    have hn : (S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).ShortExact :=
      hS.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
    have : Injective (S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).X₁ := hX n
    exact (hn.splittingOfInjective.map T).shortExact
  have := hS'.epi_g
  exact (hS'.exact.gIsCokernel).coconePointUniqueUpToIso (cokernelIsCokernel _) |>.symm

/-- In a complex of filtered injective objects every step `F^p I^n` is injective. -/
lemma injective_filtration_obj_X_of_isFilteredInjective
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective)
    (i : ℤᵒᵖ) (n : ℤ) : Injective ((I.filtration.obj i).X n) := by
  obtain ⟨⟨p, q, hp, hq⟩, hgr⟩ := (isFilteredInjective_evalFil_iff I n).1 (hI n)
  exact injective_filtration_obj_X_of_injective_gr I n ⟨q, hq⟩ hgr i.unop

/-- For a complex `I` of filtered injective objects and an additive functor `T`, the maps
`T(F^p I) ⟶ T(I)` are monomorphisms: `F^p I^n ⟶ I^n` is a split monomorphism, `F^p I^n` being
injective. -/
@[ega "0 13.6.4" "partial"]
lemma mono_map_filtration_ι_of_isFilteredInjective
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective)
    (i : ℤᵒᵖ) :
    Mono ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map (I.filtration.ι.app i)) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  have := injective_filtration_obj_X_of_isFilteredInjective I hI i n
  have : IsSplitMono ((I.filtration.ι.app i).f n) :=
    IsSplitMono.mk' ⟨Injective.factorThru (𝟙 _) _, Injective.comp_factorThru _ _⟩
  dsimp
  infer_instance

/-- The filtered complex `T(I^•)` of `ℬ`, for `T : 𝒜 ⥤ ℬ` additive and `I^•` a complex of filtered
injective objects of `𝒜`, filtered by the subcomplexes `T(F^p I^•)`. Its graded pieces are the
`T(gr^p I^•)` (`gradedPieceMapFilteredInjectiveIso`), so it is a model of `T_ext(I^•)`
([Stacks, Tag 05U0]) and hence of `RT` of any filtered complex of which `I^•` is a filtered
injective resolution ([Stacks, Tag 05U2]). -/
noncomputable def mapFilteredInjective
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective) :
    FilteredObject (CochainComplex B ℤ) ℤᵒᵖ :=
  I.mapOfMono _ (mono_map_filtration_ι_of_isFilteredInjective T I hI)

/-- The underlying complex of `T(I^•)` is `T` applied termwise to `I^•`. -/
@[simp] lemma mapFilteredInjective_X
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective) :
    (mapFilteredInjective T I hI).X = (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.X :=
  rfl

/-- The inclusion `F^p T(I^•) ⟶ T(I^•)` is `T` of the inclusion `F^p I^• ⟶ I^•`. -/
@[simp] lemma mapFilteredInjective_filtration_ι_app
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective)
    (i : ℤᵒᵖ) : (mapFilteredInjective T I hI).filtration.ι.app i =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (I.filtration.ι.app i) :=
  rfl

/-- `gr^p T(I^•) ≅ T(gr^p I^•)` for a complex `I^•` of filtered injective objects
([Stacks, Tag 015T]). -/
noncomputable def gradedPieceMapFilteredInjectiveIso
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (hI : ∀ n, (evalFil I n).IsFilteredInjective)
    (p : ℤ) :
    (FilteredObject.gr p).obj (mapFilteredInjective T I hI) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr p).obj I) :=
  cokernelMapIsoOfInjective T (I.filtration.step (FilteredObject.succHom p))
    (injective_filtration_obj_X_of_isFilteredInjective I hI _)

/-- The graded pieces of a filtered complex vanishing in degrees `< a` vanish in degrees `< a`. -/
lemma isStrictlyGE_gr (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (a : ℤ)
    [K.X.IsStrictlyGE a] (p : ℤ) : ((FilteredObject.gr p).obj K).IsStrictlyGE a := by
  rw [isStrictlyGE_iff]
  intro n hn
  have h0 : IsZero ((K.filtration.obj (op p)).X n) :=
    (K.X.isZero_of_isStrictlyGE a n hn).of_mono ((K.filtration.ι.app (op p)).f n)
  exact IsZero.of_iso (h0.of_epi (cokernel.π _))
    (FilteredComplexSpectralSequence.gradedPieceXIso K p n)

end

section SpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B]

/-- The `n`-th cohomology of the image in `D⁺(ℬ)` of a bounded below complex `X` is `H^n(X)`. -/
noncomputable def homologyQhQuotientIso (X : CochainComplex.Plus B) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj X)) ≅
      X.obj.homology n :=
  (DerivedCategory.homologyFunctorFactorsh B n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors B _ n).app X.obj

/-- **Stacks 015W.** Let `T : 𝒜 ⥤ ℬ` be an additive functor of abelian categories, `𝒜` having
enough injectives, and let `(K^•, F)` be an object of `Comp⁺(Fil^f(𝒜))`: a filtered complex with
`K^n = 0` for `n < a` whose filtration is finite in each degree. Let `α : K^• ⟶ I^•` be a filtered
quasi-isomorphism to a bounded below complex of filtered injective objects — such a filtered
injective resolution exists ([Stacks, Tag 05TW],
`exists_mono_isStrictHom_filteredQuasiIso_isStrictlyGE_injective_gradedPiece`) and the statement
holds for every choice of it. Let `E` be the spectral sequence of the filtered complex
`T(I^•) = RT(K^•)` of `ℬ`, presented as in [Stacks, Tag 012M] by its pages
`E_r^{p,q} = Z_r^{p,q}/D_r^{p,q}` and its differentials `d_r` of bidegree `(r, -r + 1)` induced by
the differential of `T(I^•)`. Then

1. `E_1^{p,q} ≅ R^{p+q}T(gr^p K^•)`;
2. `E` is bounded: for each `n` only finitely many `E_0^{p, n - p}` are nonzero;
3. `E` converges to `H^*(T(I^•)) = R^*T(K^•)`: `d_r^{p,q} = 0` for `r ≫ 0`, and the stable
   cycles and boundaries exist and are those of (012S) and (012T) with equality;
4. the induced filtration on each `R^nT(K^•) = H^n(T(I^•))` is finite;
5. `H^n(T(I^•)) ≅ R^nT(K^•)`. -/
@[stacks 015W "the spectral sequence, its `E_1` page, boundedness, convergence and finiteness of
the induced filtration", ega "0 13.6.4" "E_1, abutment, biregular"]
theorem exists_spectralSequence_rightDerivedFunctorPlus
    [HasDerivedCategory.{w} A] [EnoughInjectives A] (T : A ⥤ B) [T.Additive]
    {K I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (a b : ℤ) [K.X.IsStrictlyGE a]
    [I.X.IsStrictlyGE b] (hK : K.filtration.IsDegreewiseFinite) (α : K ⟶ I)
    (hα : filteredQuasiIso A α) (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (F : ∀ (_p n : ℤ), Subobject ((mapFilteredInjective T I hI).X.X n))
    (hF : ∀ p n : ℤ, F p n =
      Subobject.mk (((mapFilteredInjective T I hI).filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject ((mapFilteredInjective T I hI).X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n = F p n ⊓
      (Subobject.pullback ((mapFilteredInjective T I hI).X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject ((mapFilteredInjective T I hI).X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» ((mapFilteredInjective T I hI).X.d (n - 1) n)).obj
        (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject ((mapFilteredInjective T I hI).X.homology n))
    (hFH : ∀ n p : ℤ, FH n p = imageSubobject
      (HomologicalComplex.homologyMap ((mapFilteredInjective T I hI).filtration.ι.app (op p)) n)) :
    ∃ (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q),
        ((spectralSequenceOf (mapFilteredInjective T I hI) F hF).page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
      (∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
        ∃ δ : (Z r p n : B) ⟶ (Z r (p + r) (n + 1) : B),
          δ ≫ (Z r (p + r) (n + 1)).arrow =
            (Z r p n).arrow ≫ (mapFilteredInjective T I hI).X.d n (n + 1) ∧
          cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
              (e r p q n hr hn).inv ≫
                ((spectralSequenceOf (mapFilteredInjective T I hI) F hF).page r hr).d
                  (p, q) (p + r, q - r + 1) =
            δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
                D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
              (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
      (∀ p q : ℤ, Nonempty
        (((spectralSequenceOf (mapFilteredInjective T I hI) F hF).page 1).X (p, q) ≅
        (DerivedCategory.Plus.homologyFunctor B (p + q)).obj
          (T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient A).obj
              ⟨(FilteredObject.gr p).obj K, ⟨a, isStrictlyGE_gr K a p⟩⟩))))) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero
        (((spectralSequenceOf (mapFilteredInjective T I hI) F hF).page 0).X (p, n - p))}.Finite) ∧
      (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
        ((spectralSequenceOf (mapFilteredInjective T I hI) F hF).page r hr).d
          (p, q) (p + r, q - r + 1) = 0) ∧
      (∀ p n : ℤ,
        IsGLB (Set.range fun r : ℕ => F p n ⊓
            (Subobject.pullback ((mapFilteredInjective T I hI).X.d n (n + 1))).obj
              (F (p + r) (n + 1)) ⊔ F (p + 1) n)
          (kernelSubobject ((mapFilteredInjective T I hI).X.d n (n + 1)) ⊓ F p n ⊔
            F (p + 1) n) ∧
        IsLUB (Set.range fun r : ℕ => F p n ⊓
            (Subobject.«exists» ((mapFilteredInjective T I hI).X.d (n - 1) n)).obj
              (F (p - r) (n - 1)) ⊔ F (p + 1) n)
          (imageSubobject ((mapFilteredInjective T I hI).X.d (n - 1) n) ⊓ F p n ⊔
            F (p + 1) n)) ∧
      (∀ n : ℤ, ∃ p₀ p₁ : ℤ, p₀ ≤ p₁ ∧ FH n p₀ = ⊤ ∧ FH n p₁ = ⊥) ∧
      (∀ n : ℤ, Nonempty ((mapFilteredInjective T I hI).X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor B n).obj
          (T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient A).obj ⟨K.X, ⟨a, inferInstance⟩⟩))))) := by
  let M := mapFilteredInjective T I hI
  have hfinI := fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1
  have hinjgr := fun p n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).2 p
  obtain ⟨e, -, hδ, -, -, hE1⟩ := exists_iso_spectralSequence_page M F hF Z hZ D hD
  have hM : M.filtration.IsDegreewiseFinite := by
    intro n
    obtain ⟨p, q, hp, hq⟩ := hfinI n
    exact ⟨p, q, inferInstanceAs (IsIso (T.map ((I.filtration.ι.app (op p)).f n))),
      T.map_isZero hq⟩
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ :=
    isBounded_and_converges_of_isDegreewiseFinite M hM F hF Z hZ D hD FH hFH _ e
  have : M.X.IsStrictlyGE b := inferInstanceAs
    (CochainComplex.IsStrictlyGE ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.X) b)
  refine ⟨e, hδ, fun p q => ?_, h₁, h₃, h₄, h₂, fun n => ?_⟩
  · obtain ⟨φ⟩ := hE1 p q (p + q) rfl
    obtain ⟨Φ, -⟩ := exists_iso_gradedPiece_rightDerivedFunctorPlus_of_filteredQuasiIso T α hα
      hinjgr M (fun p => ⟨a, isStrictlyGE_gr K a p⟩) (fun p => ⟨b, isStrictlyGE_gr I b p⟩)
      (fun p => ⟨b, isStrictlyGE_gr M b p⟩)
      (fun p => (HomotopyCategory.Plus.quotient B).mapIso
        (ObjectProperty.isoMk (CochainComplex.plus B) (X := ⟨_, ⟨b, isStrictlyGE_gr M b p⟩⟩)
          (Y := ⟨(T.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr p).obj I),
            ⟨b, have := isStrictlyGE_gr I b p; inferInstance⟩⟩)
          (gradedPieceMapFilteredInjectiveIso T I hI p))) p
    exact ⟨φ ≪≫ (homologyQhQuotientIso ⟨_, ⟨b, isStrictlyGE_gr M b p⟩⟩ (p + q)).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B (p + q)).mapIso Φ⟩
  · have hq : QuasiIso (FilteredObject.forget.map α) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
        ((isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso α hα).2 hK hfinI)
    let XK : CochainComplex.Plus A := ⟨K.X, ⟨a, inferInstance⟩⟩
    let XI : CochainComplex.Plus A := ⟨I.X, ⟨b, inferInstance⟩⟩
    let f : (HomotopyCategory.Plus.quotient A).obj XK ⟶
        (HomotopyCategory.Plus.quotient A).obj XI :=
      (HomotopyCategory.Plus.quotient A).map
        (ObjectProperty.homMk (X := XK) (Y := XI) (FilteredObject.forget.map α))
    have hf : HomotopyCategory.Plus.quasiIso A f := by
      rw [HomotopyCategory.Plus.quasiIso_iff]
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hq
    have := Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _ hf
    have hu : IsIso
        (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj XI)) :=
      isIso_rightDerivedFunctorPlusUnit_app_forget_of_injective_gradedPiece T I b hI
    exact ⟨(homologyQhQuotientIso ⟨M.X, ⟨b, inferInstance⟩⟩ n).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B n).mapIso
        (@asIso _ _ _ _ _ hu ≪≫
          (asIso (T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map f))).symm)⟩

end SpectralSequence

section Functoriality

open FilteredComplexSpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The morphism `T(I^•) ⟶ T(J^•)` of filtered complexes induced by a morphism of complexes of
filtered injective objects. -/
noncomputable def mapFilteredInjectiveMap (T : A ⥤ B) [T.Additive]
    {I J : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (γ : I ⟶ J)
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective) :
    mapFilteredInjective T I hI ⟶ mapFilteredInjective T J hJ :=
  FilteredObject.homMk ((T.mapHomologicalComplex _).map γ.hom)
    (fun i => (T.mapHomologicalComplex _).map (γ.natTrans.app i))
    (fun i => ((Functor.map_comp _ _ _).symm.trans
      ((T.mapHomologicalComplex _).congr_map (γ.comm i))).trans (Functor.map_comp _ _ _))

/-- `mapFilteredInjectiveMap` sends the identity to the identity. -/
lemma mapFilteredInjectiveMap_id (T : A ⥤ B) [T.Additive]
    {I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective) :
    mapFilteredInjectiveMap T (𝟙 I) hI hI = 𝟙 _ := by
  ext1
  exact (T.mapHomologicalComplex _).map_id _

/-- `mapFilteredInjectiveMap` is compatible with composition. -/
lemma mapFilteredInjectiveMap_comp (T : A ⥤ B) [T.Additive]
    {I J M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (γ : I ⟶ J) (δ : J ⟶ M)
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective)
    (hM : ∀ n : ℤ, (evalFil M n).IsFilteredInjective) :
    mapFilteredInjectiveMap T (γ ≫ δ) hI hM =
      mapFilteredInjectiveMap T γ hI hJ ≫ mapFilteredInjectiveMap T δ hJ hM := by
  ext1
  exact (T.mapHomologicalComplex _).map_comp _ _

/-- Filtered homotopy is symmetric. -/
lemma FilteredHomotopic.symm {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} {φ ψ : M ⟶ N}
    (h : FilteredHomotopic φ ψ) : FilteredHomotopic ψ φ := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h.symm, fun i j p => ⟨-(hh i j p).choose, by
    simp [Homotopy.symm, (hh i j p).choose_spec]⟩⟩

/-- Filtered homotopy is transitive. -/
lemma FilteredHomotopic.trans {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} {φ ψ χ : M ⟶ N}
    (h : FilteredHomotopic φ ψ) (h' : FilteredHomotopic ψ χ) : FilteredHomotopic φ χ := by
  obtain ⟨h, hh⟩ := h
  obtain ⟨h', hh'⟩ := h'
  exact ⟨h.trans h', fun i j p => ⟨(hh i j p).choose + (hh' i j p).choose, by
    simp [Homotopy.trans, Preadditive.add_comp, Preadditive.comp_add, (hh i j p).choose_spec,
      (hh' i j p).choose_spec]⟩⟩

/-- Precomposing filtered homotopic morphisms with a morphism `u` gives filtered homotopic
morphisms. -/
lemma FilteredHomotopic.comp_left {X M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (u : X ⟶ M) {φ ψ : M ⟶ N} (h : FilteredHomotopic φ ψ) :
    FilteredHomotopic (u ≫ φ) (u ≫ ψ) := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h.compLeft u.hom, fun i j p => ⟨(u.natTrans.app (op p)).f i ≫ (hh i j p).choose, by
    rw [Category.assoc, (hh i j p).choose_spec, ← Category.assoc,
      ← HomologicalComplex.comp_f, u.comm (op p), HomologicalComplex.comp_f, Category.assoc]
    rfl⟩⟩

/-- Postcomposing filtered homotopic morphisms with a morphism `v` gives filtered homotopic
morphisms. -/
lemma FilteredHomotopic.comp_right {M N Y : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    {φ ψ : M ⟶ N} (h : FilteredHomotopic φ ψ) (v : N ⟶ Y) :
    FilteredHomotopic (φ ≫ v) (ψ ≫ v) := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h.compRight v.hom, fun i j p => ⟨(hh i j p).choose ≫ (v.natTrans.app (op p)).f j, by
    rw [Category.assoc, ← HomologicalComplex.comp_f, v.comm (op p), HomologicalComplex.comp_f,
      ← Category.assoc, (hh i j p).choose_spec, Category.assoc]
    rfl⟩⟩

/-- Applying an additive functor `T` to filtered homotopic morphisms of complexes of filtered
injective objects gives filtered homotopic morphisms. -/
lemma FilteredHomotopic.mapFilteredInjectiveMap (T : A ⥤ B) [T.Additive]
    {I J : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} {γ γ' : I ⟶ J}
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective) (h : FilteredHomotopic γ γ') :
    FilteredHomotopic (mapFilteredInjectiveMap T γ hI hJ) (mapFilteredInjectiveMap T γ' hI hJ) := by
  obtain ⟨h, hh⟩ := h
  exact ⟨T.mapHomotopy h, fun i j p => ⟨T.map (hh i j p).choose, by
    show T.map _ ≫ T.map _ = T.map _ ≫ T.map _
    rw [← T.map_comp, ← T.map_comp, (hh i j p).choose_spec]⟩⟩

/-- [Stacks, Tag 05TY] in the form used for functoriality: maps from a filtered
quasi-isomorphism's target into a bounded below complex of filtered injective objects lift maps
from its source, uniquely up to filtered homotopy. -/
@[ega "0 13.6.3" "special case", sga "2 VIII 1.4" "more general"]
lemma filteredHomotopic_lift {K L J : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (hK : K.filtration.IsDegreewiseFinite) (hL : L.filtration.IsDegreewiseFinite)
    (b : ℤ) [J.X.IsStrictlyGE b] (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective)
    (α : K ⟶ L) (hα : filteredQuasiIso A α) :
    (∀ γ : K ⟶ J, ∃ β : L ⟶ J, FilteredHomotopic (α ≫ β) γ) ∧
      ∀ β β' : L ⟶ J, FilteredHomotopic (α ≫ β) (α ≫ β') → FilteredHomotopic β β' := by
  let Filf : ObjectProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
    fun K => ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n)
  let J' : Filf.FullSubcategory :=
    ⟨J, fun n => ((isFilteredInjective_evalFil_iff J n).1 (hJ n)).1⟩
  have : J'.obj.X.IsStrictlyGE b := ‹_›
  have H := (bijective_precomp_full_and_map_eq_iff_filteredHomotopy_of_injective_gradedPiece
    Filf (fun _ => Iff.rfl) ((filteredQuasiIso A).inverseImage Filf.ι).Q J' b
    (fun p n => ((isFilteredInjective_evalFil_iff J n).1 (hJ n)).2 p)).1
    ⟨K, hK⟩ ⟨L, hL⟩ (ObjectProperty.homMk α) hα
  refine ⟨fun γ => ?_, fun β β' hβ => ?_⟩
  · obtain ⟨β, h, hh⟩ := H.1 (ObjectProperty.homMk γ)
    exact ⟨β.hom, h, hh⟩
  · obtain ⟨h, hh⟩ := hβ
    obtain ⟨h', hh'⟩ := H.2 (ObjectProperty.homMk β) (ObjectProperty.homMk β') ⟨h, hh⟩
    exact ⟨h', hh'⟩

/-- An endomorphism `γ₀` of a complex `I` of filtered injective objects with `α ≫ γ₀` filtered
homotopic to `α` induces the identity on the pages `E_r`, `r ≥ 1`, given uniqueness up to
filtered homotopy of lifts along `α`. -/
private theorem spectralSequenceMap_eq_id_of_filteredHomotopic (T : A ⥤ B) [T.Additive]
    {K I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective) (α : K ⟶ I)
    (hu : ∀ β β' : I ⟶ I, FilteredHomotopic (α ≫ β) (α ≫ β') → FilteredHomotopic β β')
    (γ₀ : I ⟶ I) (h₀ : FilteredHomotopic (α ≫ γ₀) α) (r : ℤ) (hr : 1 ≤ r) :
    (filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ₀ hI hI)).hom r (by omega) =
      𝟙 _ := by
  have h₀' : FilteredHomotopic γ₀ (𝟙 I) :=
    hu _ _ (h₀.trans (by rw [Category.comp_id]; exact ⟨Homotopy.refl _, fun i j p =>
      ⟨0, by simp⟩⟩))
  rw [filteredSpectralSequenceMap_hom_eq_of_filteredHomotopic
    (h₀'.mapFilteredInjectiveMap T hI hI) hr, mapFilteredInjectiveMap_id,
    filteredSpectralSequenceMap_id]
  rfl

variable [HasDerivedCategory.{w} A] [EnoughInjectives A] (T : A ⥤ B) [T.Additive]

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **Stacks 015W, functoriality.** Let `f : K^• ⟶ L^•` be a morphism of
`Comp⁺(Fil^f(𝒜))` and let `α : K^• ⟶ I^•`, `β : L^• ⟶ J^•` be filtered injective resolutions.
There is a morphism `γ : I^• ⟶ J^•` with `α ≫ γ` filtered homotopic to `f ≫ β`
([Stacks, Tag 05TY]); it induces a morphism of spectral sequences
`E_r(T(I^•)) ⟶ E_r(T(J^•))` ([Stacks, Tag 012O]), and on the pages `E_r`, `r ≥ 1`, this
morphism does not depend on the choice of `γ`. -/
@[stacks 015W "functoriality in `K^•`: the induced morphism of spectral sequences, independent of
choices on `E_r` for `r ≥ 1`",
  ega "0 13.6.3" "existence of v",
  ega "0 13.6.4" "E_r indep. of choices"]
theorem exists_spectralSequenceMap_rightDerivedFunctorPlus
    {K L I J : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (hK : K.filtration.IsDegreewiseFinite)
    (a b : ℤ) [I.X.IsStrictlyGE a] [J.X.IsStrictlyGE b]
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective)
    (α : K ⟶ I) (hα : filteredQuasiIso A α) (β : L ⟶ J) (f : K ⟶ L) :
    (∃ γ : I ⟶ J, FilteredHomotopic (α ≫ γ) (f ≫ β)) ∧
      ∀ γ γ' : I ⟶ J, FilteredHomotopic (α ≫ γ) (f ≫ β) →
        FilteredHomotopic (α ≫ γ') (f ≫ β) → ∀ (r : ℤ) (hr : 1 ≤ r),
          (filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ hI hJ)).hom r (by omega) =
            (filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ' hI hJ)).hom r
              (by omega) := by
  have H := filteredHomotopic_lift hK
    (fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1) b hJ α hα
  exact ⟨H.1 (f ≫ β), fun γ γ' hγ hγ' r hr =>
    filteredSpectralSequenceMap_hom_eq_of_filteredHomotopic
      ((H.2 γ γ' (hγ.trans hγ'.symm)).mapFilteredInjectiveMap T hI hJ) hr⟩

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **Stacks 015W, compatibility with composition.** If `γ` lifts `f : K^• ⟶ L^•` and `δ` lifts
`g : L^• ⟶ M^•` along filtered injective resolutions, then `γ ≫ δ` lifts `f ≫ g`, and the
morphism of spectral sequences induced by `γ ≫ δ` is the composite of those induced by `γ` and
`δ`. -/
@[stacks 015W "the construction is compatible with composition"]
theorem filteredHomotopic_comp_and_spectralSequenceMap_comp
    {K L M I J P : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective)
    (hP : ∀ n : ℤ, (evalFil P n).IsFilteredInjective)
    (α : K ⟶ I) (β : L ⟶ J) (ε : M ⟶ P) (f : K ⟶ L) (g : L ⟶ M) (γ : I ⟶ J) (δ : J ⟶ P)
    (hγ : FilteredHomotopic (α ≫ γ) (f ≫ β)) (hδ : FilteredHomotopic (β ≫ δ) (g ≫ ε)) :
    FilteredHomotopic (α ≫ γ ≫ δ) ((f ≫ g) ≫ ε) ∧
      filteredSpectralSequenceMap (mapFilteredInjectiveMap T (γ ≫ δ) hI hP) =
        filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ hI hJ) ≫
          filteredSpectralSequenceMap (mapFilteredInjectiveMap T δ hJ hP) := by
  refine ⟨?_, by rw [mapFilteredInjectiveMap_comp T γ δ hI hJ hP,
    filteredSpectralSequenceMap_comp]⟩
  have h₁ := hγ.comp_right δ
  have h₂ := hδ.comp_left f
  simp only [Category.assoc] at h₁ h₂ ⊢
  exact h₁.trans h₂

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **Stacks 015W, independence of choices.** For two filtered injective resolutions
`α : K^• ⟶ I^•` and `α' : K^• ⟶ I'^•` of the same object, any `γ : I^• ⟶ I'^•` with
`α ≫ γ` filtered homotopic to `α'` induces isomorphisms `E_r(T(I^•)) ≅ E_r(T(I'^•))` on all pages
`r ≥ 1`; when `I'^• = I^•` and `α' = α` the induced morphism is the identity on these pages. So
the terms `(E_r, d_r)`, `r ≥ 1`, do not depend on the choice of resolution. -/
@[stacks 015W "the terms `(E_r, d_r)` for `r ≥ 1` do not depend on any choices",
  ega "0 13.6.4" "partial"]
theorem isIso_spectralSequenceMap_rightDerivedFunctorPlus
    {K I I' : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (hK : K.filtration.IsDegreewiseFinite)
    (a a' : ℤ) [I.X.IsStrictlyGE a] [I'.X.IsStrictlyGE a']
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective)
    (hI' : ∀ n : ℤ, (evalFil I' n).IsFilteredInjective)
    (α : K ⟶ I) (hα : filteredQuasiIso A α) (α' : K ⟶ I') (hα' : filteredQuasiIso A α')
    (γ : I ⟶ I') (hγ : FilteredHomotopic (α ≫ γ) α') :
    (∀ (r : ℤ) (hr : 1 ≤ r),
      IsIso ((filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ hI hI')).hom r
        (by omega))) ∧
    ∀ γ₀ : I ⟶ I, FilteredHomotopic (α ≫ γ₀) α → ∀ (r : ℤ) (hr : 1 ≤ r),
      (filteredSpectralSequenceMap (mapFilteredInjectiveMap T γ₀ hI hI)).hom r (by omega) =
        𝟙 _ := by
  have hIfin : I.filtration.IsDegreewiseFinite := fun n =>
    ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1
  have hI'fin : I'.filtration.IsDegreewiseFinite := fun n =>
    ((isFilteredInjective_evalFil_iff I' n).1 (hI' n)).1
  have HI := filteredHomotopic_lift hK hIfin a hI α hα
  have HI' := filteredHomotopic_lift hK hI'fin a' hI' α' hα'
  have HI'I := filteredHomotopic_lift hK hI'fin a hI α' hα'
  refine ⟨fun r hr => ?_, spectralSequenceMap_eq_id_of_filteredHomotopic T hI α HI.2⟩
  obtain ⟨δ, hδ⟩ := HI'I.1 α
  have e₁ : FilteredHomotopic (α ≫ γ ≫ δ) α := by
    rw [← Category.assoc]
    exact (hγ.comp_right δ).trans hδ
  have e₂ : FilteredHomotopic (α' ≫ δ ≫ γ) α' := by
    rw [← Category.assoc]
    exact (hδ.comp_right γ).trans hγ
  refine ⟨⟨(filteredSpectralSequenceMap (mapFilteredInjectiveMap T δ hI' hI)).hom r (by omega),
    ?_, ?_⟩⟩
  · have := spectralSequenceMap_eq_id_of_filteredHomotopic T hI α HI.2 _ e₁ r hr
    rwa [mapFilteredInjectiveMap_comp T γ δ hI hI' hI, filteredSpectralSequenceMap_comp] at this
  · have := spectralSequenceMap_eq_id_of_filteredHomotopic T hI' α' HI'.2 _ e₂ r hr
    rwa [mapFilteredInjectiveMap_comp T δ γ hI' hI hI', filteredSpectralSequenceMap_comp] at this

end Functoriality

end CochainComplex
