module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAboveResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Triangulated subcategories of the derived category

Let `𝒜` be an abelian category and let `ℬ ⊆ 𝒜` be a Serre subcategory, i.e. a Serre class
`P : ObjectProperty 𝒜`, cutting out the full subcategory `ℬ = P.FullSubcategory` with exact
inclusion `P.ι`. Two derived categories are attached to this situation: the derived category
`D(𝒜/ℬ)` of the quotient, and the strictly full subcategory `D_ℬ(𝒜) ⊆ D(𝒜)` of objects all of
whose cohomology objects lie in `ℬ` ([Stacks, Tag 06UP]). This file relates them to `D(𝒜)` and to
`D(ℬ)`.

The quotient functor `v : 𝒜 ⥤ 𝒜/ℬ` is exact, so it induces a triangulated functor
`D(v) : D(𝒜) ⥤ D(𝒜/ℬ)`. That functor is always essentially surjective: a complex over `𝒜/ℬ`
whose differentials are only morphisms *modulo* `ℬ` can be replaced, up to isomorphism, by one
whose differentials come from `𝒜`. It need not be a localization, but it is one — so that
`D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)` — as soon as `v` admits a fully faithful left adjoint `u`: then the
counit `u v X ⟶ X` has cone in `D_ℬ(𝒜)`, so `X` becomes isomorphic to `u v X` in the quotient.

In the other direction, the inclusion induces `D(ℬ) ⥤ D(𝒜)`, which lands in `D_ℬ(𝒜)`. On bounded
above objects this is an equivalence `D⁻(ℬ) ≌ D⁻_ℬ(𝒜)` as soon as `ℬ` has enough subobjects:
every epimorphism of `𝒜` with target in `ℬ` is hit by an object of `ℬ`.

## Main results

* `CategoryTheory.ObjectProperty.SerreClassLocalization.essSurj_mapDerivedCategory`: for a
  localization `L : C ⥤ D` of an abelian category at the morphisms that become isomorphisms
  modulo a Serre class `P` — that is, for `D = C/P` — the induced functor
  `DerivedCategory C ⥤ DerivedCategory D` is essentially surjective.
* `CategoryTheory.ObjectProperty.SerreClassLocalization`
  `.isLocalization_mapDerivedCategory_of_leftAdjoint`: if moreover `L` has a fully faithful left
  adjoint, that functor is a localization at the class of morphisms whose cone has all its
  cohomology objects in `P`, i.e. `D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)`.
* `CategoryTheory.ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory`: if every
  epimorphism of `C` with target in `P` is hit by an object of `P`, then `D⁻(ℬ) ⥤ D(𝒜)` is full
  and faithful with essential image exactly the bounded above objects all of whose cohomology
  objects lie in `P`; that is, `D⁻(ℬ) ⥤ D⁻_ℬ(𝒜)` is an equivalence.

## Implementation notes

The quotient category is never constructed. `D` is any abelian category with a functor `L`
exhibiting it as the localization of `C` at `P.isoModSerre`, the morphisms which become
isomorphisms modulo `P`; `ObjectProperty.SerreClassLocalization.abelian` ([Stacks, Tag 02MS] —
the very description of `𝒜/ℬ` the source's proofs use) produces one such. Stating the
localization hypothesis rather than choosing a model means no user has to transport along an
equivalence. The Verdier quotient `D(𝒜)/D_ℬ(𝒜)` is likewise not constructed: `D_ℬ(𝒜)` is the
object property `fun X ↦ ∀ n, P (Hⁿ X)` and `ObjectProperty.trW` is the class of morphisms with
cone in it, so `Functor.IsLocalization` for that class is precisely the source's equality of
categories. The hypothesis `v u ≅ 𝟭` is spelled `[u.Full] [u.Faithful]`: for an adjunction
`u ⊣ L` the unit is invertible exactly when `u` is fully faithful, and that is the form Mathlib's
API consumes. `P` is not assumed to be the kernel of `L`; it is one, by
`SerreClassLocalization.isZero_obj_iff`, so `D_ℬ(𝒜)` is also the kernel of
`L.mapDerivedCategory`. In every statement the comparison functor is pinned rather than asserted
to exist: it is `L.mapDerivedCategory`, characterised by `Functor.mapDerivedCategoryFactors` as
applying `L` termwise to complexes.

Essential surjectivity is proved at the level of complexes, in the stronger
derived-category-free form: `L` induces an essentially surjective functor
`Cochain(𝒜) ⥤ Cochain(𝒜/ℬ)`. Since `L` is a localization it is essentially surjective, so the
objects of a complex over `𝒜/ℬ` may be taken of the form `L Aⁱ`; what has to be rectified is the
differentials, which a priori are fractions and compose to zero only in `𝒜/ℬ`. Writing
`dⁱ = (sⁱ, fⁱ)` with `sⁱ` invertible modulo `ℬ`, one lifts the differentials by iterated
pushouts along `sⁱ` in nonnegative degrees and iterated pullbacks in negative degrees
(`exists_pushout_tower`, `exists_pullback_tower`), and then strictifies `d ∘ d = 0` by passing to
the subobjects `Yⁱ = ker(fⁱ⁺¹ ∘ fⁱ) ⊆ Aⁱ`, on which the `fⁱ` restrict to an honest complex and
which change nothing modulo `ℬ`. The single subobject `ker (fⁱ⁺¹ ∘ fⁱ)` does in every degree at
once the work the source splits between a quotient in positive degrees and an intersection in
negative degrees; it is invertible modulo `ℬ` because its cokernel is the coimage of
`fⁱ⁺¹ ∘ fⁱ`, isomorphic to its image, which lies in `ℬ` precisely because `L (fⁱ⁺¹ ∘ fⁱ) = 0`.
Intermediate stages are presented unbundled, as a family `A : ℤ → 𝒜` together with morphisms of
the quotient category and isomorphisms `L (Y i) ≅ L (A i)`, so that the transport along
objectwise isomorphisms happens once rather than at every step.

That `D(v)` is a localization is checked on cochain complexes and transported: the two comparison
isomorphisms of the equivalence are obtained from isomorphisms of functors on `Cochain(𝒜)` and
`Cochain(𝒜/ℬ)` by `Localization.liftNatIso`. The quasi-inverse is produced explicitly rather
than from essential surjectivity and fullness: it is `u` applied termwise to cochain complexes,
descended along `Q : Cochain(𝒜/ℬ) ⥤ D(𝒜/ℬ)`, which is legitimate because `L ∘ u ≅ 𝟭`, so `u`
carries a quasi-isomorphism to a morphism `D(v)` inverts.

For the equivalence `D⁻(ℬ) ≌ D⁻_ℬ(𝒜)`, `D⁻_ℬ(𝒜)` has no name in Mathlib, so the conclusion is
spelled out: the composite `D⁻(ℬ) ⥤ D(𝒜)` is full, faithful, and its essential image is the class
of `X : D(𝒜)` which are `≤ n` for some `n` and have `P (Hⁱ X)` for all `i`. A full, faithful
functor whose essential image is that class is precisely an equivalence onto the corresponding
full subcategory, and stating it this way pins the functor to the canonical one of
[Stacks, Tag 06UR]. The source's hypothesis asks for a *subobject* of `X` in `ℬ` surjecting onto
`Y`; the form used here only asks for some `g : X' ⟶ X` with `X'` in `ℬ` and `g ≫ f` epi, which
is formally weaker hence gives a stronger statement, and the two are equivalent by passing to the
image of `g`, a subobject of `X` which lies in the Serre class because it is a quotient of `X'`.
The instances `P.IsClosedUnderFiniteProducts`, `PreservesFiniteLimits P.ι` and
`PreservesFiniteColimits P.ι` are consequences of `P.IsSerreClass` which Mathlib does not record;
they are assumed so that `P.FullSubcategory` is abelian and `P.ι.mapDerivedCategory` is
available, and they restrict nothing.

The mathematical content there is again about complexes: a bounded above complex `X` of `𝒜` all
of whose cohomology objects lie in `ℬ` receives a quasi-isomorphism from a bounded above complex
with all terms in `ℬ` (`exists_quasiIso_of_prop_homology`). Following the source one chooses
`Cⁱ ⊆ ker dⁱ` in `ℬ` surjecting onto `Hⁱ(X)`, then by descending induction from a degree above
which `X` vanishes chooses `Eⁱ ⊆ Xⁱ` in `ℬ` with `d(Eⁱ) = (Dⁱ⁺¹ + Eⁱ⁺¹) ∩ im dⁱ`; the complex
`Yⁱ = Dⁱ + Eⁱ` then has cohomology surjecting onto and injecting into that of `X`. That
construction is not carried out here: it is
`Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis`, which builds
the resolution for a weak Serre class `R` containing the cohomology objects and a separate class
`G` supplying the terms. The case needed here is `R = G = P`, for which the hypotheses on `G` —
that it contains the zero object and is closed under binary biproducts and under isomorphism —
are `P.prop_zero`, `P.prop_biprod` and `P.prop_of_iso`, so `exists_quasiIso_of_prop_homology`
supplies nothing beyond `CoversEpis P` itself.

For faithfulness and fullness the source enlarges the subcomplex so that it contains the image of
a chosen homotopy; that bookkeeping is not needed, because `ℬ` is a *full* subcategory of `𝒜`, so
a morphism of complexes of `ℬ` which is null-homotopic in `𝒜` is already null-homotopic in `ℬ`.
Both properties therefore follow from the claim together with the calculus of fractions on the
homotopy category, in the form of `DerivedCategory.right_fac_of_isStrictlyLE`. The claim is
correspondingly stated as the existence of a quasi-isomorphism `Y ⟶ X` rather than of a
subcomplex `Y ⊆ X` containing prescribed subobjects, which is the source's form.

Two facts about an exact functor between abelian categories are used throughout which Mathlib
does not record: it commutes with the homology of a complex and with the homology functors on the
derived categories, and it preserves the property of being `≤ n` for the canonical t-structure.
They are proved once, naturally in the complex, and specialised by evaluation.

## References

* [Stacks project, Tag 06XL](https://stacks.math.columbia.edu/tag/06XL)
* [Stacks project, Tag 06XM](https://stacks.math.columbia.edu/tag/06XM)
* [Stacks project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks project, Tag 06UR](https://stacks.math.columbia.edu/tag/06UR)
-/

universe w w' v v' u u'

namespace CategoryTheory.ObjectProperty

/-! ### Exact functors, homology, and boundedness in the derived category -/

section ExactFunctor

open Limits _root_.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor `F` commutes with the homology of cochain complexes:
`Hⁿ(F(K)) ≅ F(Hⁿ(K))`, naturally in `K`. -/
private noncomputable def mapHomologicalComplexCompHomologyFunctorIso (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ) F)

/-- An exact functor between abelian categories commutes with the homology of a complex. -/
private noncomputable def mapHomologicalComplexHomologyIso (K : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅ F.obj (K.homology i) :=
  (mapHomologicalComplexCompHomologyFunctorIso F i).app K

/-- An exact functor `F` commutes with the cohomology objects of the derived category:
`Hⁿ ∘ D(F) ≅ F ∘ Hⁿ`. This is the previous isomorphism descended along the localization
`Q : Cochain(𝒜) ⥤ D(𝒜)`, which is possible because both sides send quasi-isomorphisms to
isomorphisms. -/
private noncomputable def mapDerivedCategoryCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      mapHomologicalComplexCompHomologyFunctorIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

/-- An exact functor between abelian categories commutes with the homology functors on the
derived categories. -/
private noncomputable def homologyMapDerivedCategoryObjIso (X : DerivedCategory C) (i : ℤ) :
    (homologyFunctor D i).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((homologyFunctor C i).obj X) :=
  (mapDerivedCategoryCompHomologyFunctorIso F i).app X

/-- An exact functor between abelian categories preserves the objects which are `≤ n` for the
canonical t-structure on the derived category. -/
private lemma isLE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  rw [isLE_iff]
  intro i hi
  exact (F.map_isZero (X.isZero_of_isLE n i hi)).of_iso (homologyMapDerivedCategoryObjIso F X i)

end ExactFunctor

/-! ### `D(𝒜) ⥤ D(𝒜/ℬ)` is essentially surjective -/

section EssSurj

open Limits

section Towers

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

/-- **The tower of pushouts of [Stacks, Tag 06XL].** Given objects `A n` of `C` and morphisms
`s n : B n ⟶ A n` in `W` and `g n : B n ⟶ A (n + 1)`, there are objects `A' n`, morphisms
`φ n : A n ⟶ A' n` in `W` and morphisms `f n : A' n ⟶ A' (n + 1)` such that
`s n ≫ φ n ≫ f n = g n ≫ φ (n + 1)`: the right fractions `(s n, g n)` become genuine morphisms
of `C` after replacing `A n` by `A' n`.

`A' 0` is `A 0` and `A' (n + 1)` is the pushout of `s n ≫ φ n` and `g n`, so that `φ (n + 1)` is
a cobase change of `s n ≫ φ n`. In particular `φ 0` is an isomorphism. -/
private theorem exists_pushout_tower [W.IsStableUnderCobaseChange] [HasPushouts C] (A B : ℕ → C)
    (s : ∀ n, B n ⟶ A n) (hs : ∀ n, W (s n)) (g : ∀ n, B n ⟶ A (n + 1)) :
    ∃ (A' : ℕ → C) (φ : ∀ n, A n ⟶ A' n) (f : ∀ n, A' n ⟶ A' (n + 1)),
      IsIso (φ 0) ∧ (∀ n, W (φ n)) ∧ ∀ n, s n ≫ φ n ≫ f n = g n ≫ φ (n + 1) := by
  let T : ∀ n, Σ' (X : C) (φ : A n ⟶ X), W φ := fun n =>
    Nat.rec (motive := fun n => Σ' (X : C) (φ : A n ⟶ X), W φ)
      ⟨A 0, 𝟙 _, W.id_mem _⟩
      (fun n ih => ⟨pushout (s n ≫ ih.2.1) (g n), pushout.inr _ _,
        W.pushout_inr _ _ (W.comp_mem _ _ (hs n) ih.2.2)⟩) n
  refine ⟨fun n => (T n).1, fun n => (T n).2.1,
    fun n => pushout.inl (s n ≫ (T n).2.1) (g n), ?_, fun n => (T n).2.2, fun n => ?_⟩
  · exact inferInstanceAs (IsIso (𝟙 (A 0)))
  · rw [← Category.assoc]
    exact pushout.condition

/-- **The tower of pullbacks of [Stacks, Tag 06XL].** The dual of `exists_pushout_tower`, with
the index `n` standing for the degree `-(n + 1)`: given morphisms `t n : A n ⟶ Z n` in `W` and
`g n : A (n + 1) ⟶ Z n`, and a morphism `ψ : X₀ ⟶ A 0` in `W` to start from, there are objects
`A' n`, morphisms `φ n : A' n ⟶ A (n + 1)` in `W`, morphisms `f n : A' (n + 1) ⟶ A' n` and
`f₀ : A' 0 ⟶ X₀` with `φ (n + 1) ≫ g (n + 1) = f n ≫ φ n ≫ t (n + 1)` and
`φ 0 ≫ g 0 = f₀ ≫ ψ ≫ t 0`: the left fractions `(g n, t n)` become genuine morphisms of `C`
after replacing `A (n + 1)` by `A' n`, compatibly with the given `X₀` in degree `0`.

`A' n` is the pullback of `φ (n - 1) ≫ t n` and `g n`, starting from `ψ ≫ t 0` and `g 0`, so
that `φ n` is a base change of `φ (n - 1) ≫ t n`. -/
private theorem exists_pullback_tower [W.IsStableUnderBaseChange] [HasPullbacks C] (A Z : ℕ → C)
    (t : ∀ n, A n ⟶ Z n) (ht : ∀ n, W (t n)) (g : ∀ n, A (n + 1) ⟶ Z n)
    (X₀ : C) (ψ : X₀ ⟶ A 0) (hψ : W ψ) :
    ∃ (A' : ℕ → C) (φ : ∀ n, A' n ⟶ A (n + 1)) (f : ∀ n, A' (n + 1) ⟶ A' n) (f₀ : A' 0 ⟶ X₀),
      (∀ n, W (φ n)) ∧ (∀ n, φ (n + 1) ≫ g (n + 1) = f n ≫ φ n ≫ t (n + 1)) ∧
        φ 0 ≫ g 0 = f₀ ≫ ψ ≫ t 0 := by
  let T : ∀ n, Σ' (X : C) (φ : X ⟶ A n), W φ := fun n =>
    Nat.rec (motive := fun n => Σ' (X : C) (φ : X ⟶ A n), W φ)
      ⟨X₀, ψ, hψ⟩
      (fun n ih => ⟨pullback (ih.2.1 ≫ t n) (g n), pullback.snd _ _,
        W.pullback_snd _ _ (W.comp_mem _ _ ih.2.2 (ht n))⟩) n
  exact ⟨fun n => (T (n + 1)).1, fun n => (T (n + 1)).2.1,
    fun n => pullback.fst ((T (n + 1)).2.1 ≫ t (n + 1)) (g (n + 1)),
    pullback.fst (ψ ≫ t 0) (g 0), fun n => (T (n + 1)).2.2,
    fun n => (pullback.condition (f := (T (n + 1)).2.1 ≫ t (n + 1)) (g := g (n + 1))).symm,
    (pullback.condition (f := ψ ≫ t 0) (g := g 0)).symm⟩

end Towers

section Complexes

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]
  [L.Additive]

/-- **Lifting the differentials in nonnegative degrees.** A family of morphisms
`d i : L (A i) ⟶ L (A (i + 1))` of the quotient category is, in the degrees `i = n : ℕ` and up to
isomorphisms `L (A' n) ≅ L (A n)`, a family of morphisms of `C`; moreover the isomorphism in
degree `0` is `L` of a morphism `A' 0 ⟶ A 0` invertible modulo `P`, so that the construction can
be continued into the negative degrees by `exists_diff_eq_map_neg`.

This is the nonnegative half of the first two paragraphs of the proof of [Stacks, Tag 06XL]: each
`d n` is written as a right fraction `(s n, g n)` and `exists_pushout_tower` rectifies the whole
family at once. -/
private theorem exists_diff_eq_map_nonneg (A : ℤ → C)
    (d : ∀ i, L.obj (A i) ⟶ L.obj (A (i + 1))) :
    ∃ (A' : ℕ → C) (f : ∀ n, A' n ⟶ A' (n + 1)) (e : ∀ n : ℕ, L.obj (A' n) ≅ L.obj (A n))
      (ψ : A' 0 ⟶ A 0), P.isoModSerre ψ ∧ L.map ψ = (e 0).hom ∧
        ∀ n : ℕ, (e n).hom ≫ d n = L.map (f n) ≫ (e (n + 1)).hom := by
  have key : ∀ n : ℕ, ∃ (Z : C) (s : Z ⟶ A n) (_ : P.isoModSerre s) (g : Z ⟶ A ((n : ℤ) + 1)),
      L.map s ≫ d n = L.map g := fun n => by
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction (W := P.isoModSerre) (L := L) (d n)
    exact ⟨φ.X', φ.s, φ.hs, φ.f, by rw [hφ]; exact φ.map_s_comp_map L (Localization.inverts L _)⟩
  choose B s hs g hg using key
  obtain ⟨A', φ, f, h0, hφ, hcomm⟩ :=
    exists_pushout_tower P.isoModSerre (fun n : ℕ => A n) B s hs g
  have hs' : ∀ n, IsIso (L.map (s n)) := fun n =>
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).2 (hs n)
  have hφ' : ∀ n, IsIso (L.map (φ n)) := fun n =>
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).2 (hφ n)
  have key2 : ∀ n : ℕ, d n ≫ L.map (φ (n + 1)) = L.map (φ n) ≫ L.map (f n) := fun n => by
    have := hs' n
    rw [← cancel_epi (L.map (s n)), ← Category.assoc, hg n]
    simp only [← Functor.map_comp]
    rw [hcomm n]
  have := h0
  refine ⟨A', f, fun n => (asIso (L.map (φ n))).symm, inv (φ 0),
    P.isoModSerre_of_isIso _, by simp, fun n => ?_⟩
  have := hφ' n
  have := hφ' (n + 1)
  simp only [Iso.symm_hom, asIso_inv]
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← key2 n, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- **Lifting the differentials in negative degrees.** The dual of
`exists_diff_eq_map_nonneg`: a family of morphisms `d i : L (A i) ⟶ L (A (i + 1))` of the
quotient category is, in the degrees `i = -(n + 1)` and up to isomorphisms
`L (A' n) ≅ L (A (-(n + 1)))`, a family of morphisms of `C`, compatibly with a prescribed
replacement `ψ : X₀ ⟶ A 0` of the object of degree `0`.

Each `d (-(n + 1))` is written as a left fraction `(g n, t n)` and `exists_pullback_tower`
rectifies the whole family at once. The degrees are spelled `Int.negSucc n` rather than
`-(n + 1)`, because `Int.negSucc (n + 1) + 1` reduces to `Int.negSucc n` and `Int.negSucc 0 + 1`
to `0`, which is what makes the two halves splice without transport in
`exists_diff_eq_map`. -/
private theorem exists_diff_eq_map_neg (A : ℤ → C)
    (d : ∀ i, L.obj (A i) ⟶ L.obj (A (i + 1))) (X₀ : C) (ψ : X₀ ⟶ A 0)
    (hψ : P.isoModSerre ψ) :
    ∃ (A' : ℕ → C) (f : ∀ n, A' (n + 1) ⟶ A' n) (f₀ : A' 0 ⟶ X₀)
      (e : ∀ n : ℕ, L.obj (A' n) ≅ L.obj (A (Int.negSucc n))),
      (∀ n, (e (n + 1)).hom ≫ d (Int.negSucc (n + 1)) = L.map (f n) ≫ (e n).hom) ∧
        (e 0).hom ≫ d (Int.negSucc 0) = L.map f₀ ≫ L.map ψ := by
  have key : ∀ n : ℕ, ∃ (Z : C) (t : A (Int.negSucc n + 1) ⟶ Z) (_ : P.isoModSerre t)
      (g : A (Int.negSucc n) ⟶ Z), d (Int.negSucc n) ≫ L.map t = L.map g := fun n => by
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction (W := P.isoModSerre) (L := L)
      (d (Int.negSucc n))
    exact ⟨φ.Y', φ.s, φ.hs, φ.f, by rw [hφ]; exact φ.map_comp_map_s L (Localization.inverts L _)⟩
  choose Z t ht g hg using key
  obtain ⟨A', φ, f, f₀, hφ, hcomm, hcomm₀⟩ :=
    exists_pullback_tower P.isoModSerre (fun n : ℕ => A (Int.negSucc n + 1)) Z t ht g X₀ ψ hψ
  have ht' : ∀ n, IsIso (L.map (t n)) := fun n =>
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).2 (ht n)
  have hφ' : ∀ n, IsIso (L.map (φ n)) := fun n =>
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).2 (hφ n)
  refine ⟨A', f, f₀, fun n => asIso (L.map (φ n)), fun n => ?_, ?_⟩
  · have := ht' (n + 1)
    rw [← cancel_mono (L.map (t (n + 1)))]
    simp only [asIso_hom, Category.assoc, hg (n + 1), ← Functor.map_comp]
    rw [hcomm n]
  · have := ht' 0
    rw [← cancel_mono (L.map (t 0))]
    simp only [asIso_hom, Category.assoc, hg 0, ← Functor.map_comp]
    rw [hcomm₀]

include P in
/-- **Lifting the differentials** ([Stacks, Tag 06XL], first two paragraphs of the proof). Any
family of morphisms `d i : L (A i) ⟶ L (A (i + 1))` of the quotient category is, up to
isomorphisms `L (A' i) ≅ L (A i)`, a family of morphisms of `C`.

Vanishing of the composites is not used. In nonnegative degrees the source writes
`d i = (s i, f i)` as a right fraction, `s i : B i ⟶ A i` invertible modulo `P` and
`f i : B i ⟶ A (i + 1)` (available from `Localization.exists_rightFraction`, since
`P.isoModSerre` has a right calculus of fractions), and takes `A' (n + 1)` to be the pushout of
`B n ⟶ A' n` along `f n`, starting from `A' 0 = A 0`; the map `A (n + 1) ⟶ A' (n + 1)` is the
cobase change of `B n ⟶ A' n`, hence again invertible modulo `P` because `P.isoModSerre` is
multiplicative and stable under cobase change. In negative degrees one writes `d i` as a left
fraction and dualises, `A' (n - 1)` being the pullback.

The two halves are `exists_diff_eq_map_nonneg` and `exists_diff_eq_map_neg`; the negative half is
run with the object `A' 0` of the nonnegative one prescribed in degree `0`, so that the families
splice over `ℤ = ℕ ⊔ ℕ` with no transport. -/
private theorem exists_diff_eq_map (A : ℤ → C) (d : ∀ i, L.obj (A i) ⟶ L.obj (A (i + 1))) :
    ∃ (A' : ℤ → C) (f : ∀ i, A' i ⟶ A' (i + 1)) (e : ∀ i, L.obj (A' i) ≅ L.obj (A i)),
      ∀ i, (e i).hom ≫ d i = L.map (f i) ≫ (e (i + 1)).hom := by
  obtain ⟨Ap, fp, ep, ψ, hψ, hψe, hp⟩ := exists_diff_eq_map_nonneg L P A d
  obtain ⟨Am, fm, fm₀, em, hm, hm₀⟩ := exists_diff_eq_map_neg L P A d (Ap 0) ψ hψ
  refine ⟨fun i => Int.rec (motive := fun _ => C) Ap Am i,
    fun i => match i with
      | Int.ofNat n => fp n
      | Int.negSucc 0 => fm₀
      | Int.negSucc (n + 1) => fm n,
    fun i => match i with
      | Int.ofNat n => ep n
      | Int.negSucc n => em n, ?_⟩
  intro i
  match i with
  | Int.ofNat n => exact hp n
  | Int.negSucc 0 => rw [hψe] at hm₀; exact hm₀
  | Int.negSucc (n + 1) => exact hm n

/-- **A morphism killed by the quotient functor has a kernel invertible modulo `P`.** If
`L g = 0` then the inclusion `ker g ⟶ X` becomes an isomorphism in `C / P`: it is a monomorphism
whose cokernel is the coimage of `g`, isomorphic to the image of `g`, which satisfies `P`
precisely because `L g = 0`.

This is the only property of the subobject `ker (fⁱ⁺¹ ∘ fⁱ) ⊆ Aⁱ` that the strictification step
of [Stacks, Tag 06XL] uses. Mathlib has `ObjectProperty.SerreClassLocalization.map_eq_zero_iff`
and `ObjectProperty.isoModSerre_of_mono` but not their combination. -/
private theorem isoModSerre_kernel_ι {X Y : C} (g : X ⟶ Y) (hg : L.map g = 0) :
    P.isoModSerre (kernel.ι g) :=
  P.isoModSerre_of_mono _ <| (P.prop_iff_of_iso (Abelian.coimageIsoImage g)).2
    ((ObjectProperty.SerreClassLocalization.map_eq_zero_iff L P g).1 hg)

include P in
/-- **Strictifying `d ∘ d = 0`** ([Stacks, Tag 06XL], third paragraph of the proof). A family of
morphisms `f i : A i ⟶ A (i + 1)` of `C` whose composites vanish in the quotient category is, up
to isomorphisms `L (Y i) ≅ L (A i)`, an honest complex of `C`.

The complex is `Y i = ker (f i ≫ f (i + 1)) ⊆ A i`: the `f i` restrict to it because
`f (i + 1) ≫ f (i + 2)` kills `ker (f i ≫ f (i + 1)) ≫ f i`, and the restricted composites
vanish because `Y (i + 2)` is a subobject of `A (i + 2)` through which `Y i ⟶ A (i + 2)` factors
as zero. The inclusion `Y i ⟶ A i` is invertible modulo `P`: it is a monomorphism, and its
cokernel is the coimage of `f i ≫ f (i + 1)`, isomorphic to its image, which satisfies `P`
because `L (f i ≫ f (i + 1)) = 0`. -/
private theorem exists_cochainComplex_of_map_comp_eq_zero (A : ℤ → C)
    (f : ∀ i, A i ⟶ A (i + 1)) (hf : ∀ i, L.map (f i ≫ f (i + 1)) = 0) :
    ∃ (Y : CochainComplex C ℤ) (e : ∀ i, L.obj (Y.X i) ≅ L.obj (A i)),
      ∀ i, (e i).hom ≫ L.map (f i) = L.map (Y.d i (i + 1)) ≫ (e (i + 1)).hom := by
  have hcomp : ∀ i : ℤ,
      (kernel.ι (f i ≫ f (i + 1)) ≫ f i) ≫ (f (i + 1) ≫ f (i + 1 + 1)) = 0 := fun i =>
    calc (kernel.ι (f i ≫ f (i + 1)) ≫ f i) ≫ (f (i + 1) ≫ f (i + 1 + 1))
        = (kernel.ι (f i ≫ f (i + 1)) ≫ (f i ≫ f (i + 1))) ≫ f (i + 1 + 1) := by
          simp only [Category.assoc]
      _ = 0 := by rw [kernel.condition, zero_comp]
  have hι : ∀ i : ℤ, IsIso (L.map (kernel.ι (f i ≫ f (i + 1)))) := fun i =>
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).2
      (isoModSerre_kernel_ι L P _ (hf i))
  refine ⟨{ X := fun i => kernel (f i ≫ f (i + 1))
            d := fun i j => if h : i + 1 = j then
              kernel.lift _ (kernel.ι (f i ≫ f (i + 1)) ≫ f i) (hcomp i) ≫
                eqToHom (by rw [h]) else 0
            shape := fun i j hij => dite_eq_right hij
            d_comp_d' := ?_ },
    fun i => @asIso _ _ _ _ (L.map (kernel.ι (f i ≫ f (i + 1)))) (hι i), ?_⟩
  · intro i j k h₁ h₂
    subst h₁
    subst h₂
    rw [dite_eq_left rfl, dite_eq_left rfl]
    simp only [eqToHom_refl, Category.comp_id]
    refine zero_of_comp_mono (kernel.ι (f (i + 1 + 1) ≫ f (i + 1 + 1 + 1))) ?_
    simp only [Category.assoc, kernel.lift_ι]
    rw [← Category.assoc, kernel.lift_ι, Category.assoc, kernel.condition]
  · intro i
    simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id, asIso_hom, ← Functor.map_comp,
      kernel.lift_ι]

include P in
/-- A family of morphisms `d i : L (A i) ⟶ L (A (i + 1))` of the quotient category with vanishing
composites comes, up to isomorphisms `L (Y i) ≅ L (A i)`, from a complex of `C`. -/
private theorem exists_cochainComplex_of_comp_eq_zero (A : ℤ → C)
    (d : ∀ i, L.obj (A i) ⟶ L.obj (A (i + 1))) (hd : ∀ i, d i ≫ d (i + 1) = 0) :
    ∃ (Y : CochainComplex C ℤ) (e : ∀ i, L.obj (Y.X i) ≅ L.obj (A i)),
      ∀ i, (e i).hom ≫ d i = L.map (Y.d i (i + 1)) ≫ (e (i + 1)).hom := by
  obtain ⟨A', f, e₁, h₁⟩ := exists_diff_eq_map L P A d
  have hmap : ∀ i, L.map (f i) = (e₁ i).hom ≫ d i ≫ (e₁ (i + 1)).inv := fun i => by
    rw [← Category.assoc, h₁ i]; simp
  obtain ⟨Y, e₂, h₂⟩ := exists_cochainComplex_of_map_comp_eq_zero L P A' f (fun i => by
    rw [L.map_comp, hmap i, hmap (i + 1)]
    slice_lhs 3 4 => rw [Iso.inv_hom_id]
    rw [Category.id_comp]
    slice_lhs 2 3 => rw [hd i]
    simp)
  refine ⟨Y, fun i => e₂ i ≪≫ e₁ i, fun i => ?_⟩
  have := h₂ i
  simp only [Iso.trans_hom, Category.assoc]
  rw [h₁ i, ← Category.assoc, h₂ i, Category.assoc]

include P in
/-- The termwise application of the quotient functor `L` is essentially surjective on complexes:
every complex of `C / P` is isomorphic to one obtained from a complex of `C`. -/
private theorem essSurj_mapHomologicalComplex :
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).EssSurj := by
  have := Localization.essSurj L P.isoModSerre
  constructor
  intro X
  set iso : ∀ i : ℤ, L.obj (L.objPreimage (X.X i)) ≅ X.X i := fun i => L.objObjPreimageIso _
    with hiso
  obtain ⟨Y, e, he⟩ := exists_cochainComplex_of_comp_eq_zero L P (fun i => L.objPreimage (X.X i))
    (fun i => (iso i).hom ≫ X.d i (i + 1) ≫ (iso (i + 1)).inv) (fun i => by
      slice_lhs 3 4 => rw [Iso.inv_hom_id]
      rw [Category.id_comp]
      slice_lhs 2 3 => rw [X.d_comp_d i (i + 1) (i + 1 + 1)]
      simp)
  refine ⟨Y, ⟨HomologicalComplex.Hom.isoOfComponents (fun i => e i ≪≫ iso i) ?_⟩⟩
  rintro i j (rfl : i + 1 = j)
  have h := congrArg (fun φ => φ ≫ (iso (i + 1)).hom) (he i)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  simpa using h

end Complexes

/-- **Stacks 06XL.** Let `C` be an abelian category, let `P` be a Serre class in `C`, and let
`L : C ⥤ D` be a localization of `C` at the morphisms which become isomorphisms modulo `P`,
i.e. let `D` be the quotient abelian category `C/P`. Then the induced functor
`DerivedCategory C ⥤ DerivedCategory D` is essentially surjective. -/
@[stacks 06XL]
public theorem SerreClassLocalization.essSurj_mapDerivedCategory
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    L.mapDerivedCategory.EssSurj := by
  have := essSurj_mapHomologicalComplex L P
  have hQ : (DerivedCategory.Q (C := D)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
  constructor
  intro K
  refine ⟨DerivedCategory.Q.obj
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).objPreimage
      (DerivedCategory.Q.objPreimage K)), ⟨?_⟩⟩
  refine L.mapDerivedCategoryFactors.app _ ≪≫ ?_
  exact DerivedCategory.Q.mapIso
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).objObjPreimageIso _) ≪≫
      DerivedCategory.Q.objObjPreimageIso K

end EssSurj

/-! ### `D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)` for a quotient with a fully faithful left adjoint -/

section LeftAdjoint

open Category Limits Pretriangulated

/-- An object is zero as soon as the zero endomorphism is an isomorphism. -/
private lemma isZero_iff_isIso_zero {A : Type*} [Category A] [HasZeroMorphisms A] (X : A) :
    IsZero X ↔ IsIso (0 : X ⟶ X) :=
  ⟨fun h ↦ (isIsoZeroSelfEquiv X).symm ((IsZero.iff_id_eq_zero X).1 h),
    fun h ↦ (IsZero.iff_id_eq_zero X).2 (isIsoZeroSelfEquiv X h)⟩

section Complexes

variable {C : Type u} [Category.{v} C] [Preadditive C] {D : Type u'} [Category.{v'} D]
  [Preadditive D] (L : C ⥤ D) [L.Additive] {u : D ⥤ C} [u.Additive] (adj : u ⊣ L)

/-- The counit `L u ⟶ 𝟭` of the adjunction, applied termwise to cochain complexes: the source's
`c_K : u L K ⟶ K`. -/
private noncomputable def counitCochainComplex :
    L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ u.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      𝟭 (CochainComplex C ℤ) :=
  NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom

private lemma counitCochainComplex_app_f (K : CochainComplex C ℤ) (i : ℤ) :
    ((counitCochainComplex L adj).app K).f i = adj.counit.app (K.X i) := by
  simp [counitCochainComplex]

section

variable [u.Full] [u.Faithful]

/-- Applying `L` termwise to the counit `u L K ⟶ K` gives an isomorphism of cochain complexes:
in each degree it is `L` of the counit, invertible because the unit of an adjunction with fully
faithful left adjoint is invertible. -/
private lemma isIso_map_counitCochainComplex_app (K : CochainComplex C ℤ) :
    IsIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((counitCochainComplex L adj).app K)) := by
  have (i : ℤ) : IsIso (((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((counitCochainComplex L adj).app K)).f i) := by
    rw [Functor.mapHomologicalComplex_map_f, counitCochainComplex_app_f]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `L ∘ u ≅ 𝟭` applied termwise to cochain complexes. -/
private noncomputable def mapHomologicalComplexCompIsoId :
    u.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ L.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex D ℤ) :=
  (NatIso.mapHomologicalComplex (asIso adj.unit) (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomologicalComplexIdIso D (ComplexShape.up ℤ)

end

end Complexes

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- An object of the derived category is zero iff all its cohomology objects are. -/
private lemma isZero_iff_forall_isZero_homology (X : DerivedCategory C) :
    IsZero X ↔ ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj X) := by
  rw [isZero_iff_isIso_zero, DerivedCategory.isIso_iff]
  refine forall_congr' fun n ↦ ?_
  rw [(DerivedCategory.homologyFunctor C n).map_zero, ← isZero_iff_isIso_zero]

/-- `D_ℬ(𝒜) ⊆ D(𝒜)`, the objects of the derived category all of whose cohomology objects lie in
`ℬ = P`, [Stacks, Tag 06UP]. -/
@[sga "4 Vbis 2.4.1" "partial", sga "4 Vbis 2.4.2" "partial", sga "6 IV 1.6"]
private abbrev homologyProp (P : ObjectProperty C) : ObjectProperty (DerivedCategory C) :=
  fun X ↦ ∀ n : ℤ, P ((DerivedCategory.homologyFunctor C n).obj X)

variable (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

variable (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]

/-- `D_ℬ(𝒜)` is the kernel of `D(L)`: a morphism of `D(𝒜)` has its cone in `D_ℬ(𝒜)` if and only
if `D(L) : D(𝒜) ⥤ D(𝒜/ℬ)` inverts it. -/
private lemma mem_trW_iff {X Y : DerivedCategory C} (f : X ⟶ Y) :
    trW (homologyProp P) f ↔ IsIso (L.mapDerivedCategory.map f) := by
  have : (homologyProp P).IsClosedUnderIsomorphisms :=
    ⟨fun e h n ↦ P.prop_of_iso ((DerivedCategory.homologyFunctor C n).mapIso e) (h n)⟩
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  refine (ObjectProperty.trW_iff_of_distinguished _ (Triangle.mk f g h) hT).trans
    (Iff.trans ?_ (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (L.mapDerivedCategory.map_distinguished _ hT)))
  rw [isZero_iff_forall_isZero_homology]
  exact forall_congr' fun n ↦ (SerreClassLocalization.isZero_obj_iff L P _).symm.trans
    ((mapDerivedCategoryCompHomologyFunctorIso L n).app Z).isZero_iff.symm

/-- On complexes: a morphism of cochain complexes of `𝒜` has its cone in `D_ℬ(𝒜)` exactly when
applying `L` termwise makes it a quasi-isomorphism. -/
private lemma trW_Q_map_iff {K K' : CochainComplex C ℤ} (f : K ⟶ K') :
    trW (homologyProp P) (DerivedCategory.Q.map f) ↔
      IsIso (DerivedCategory.Q.map
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
  rw [mem_trW_iff L P]
  exact NatIso.isIso_map_iff L.mapDerivedCategoryFactors f

include L in
/-- The functor `D(𝒜)/D_ℬ(𝒜) ⥤ D(𝒜/ℬ)` induced by `D(L)`. -/
private noncomputable def liftMapDerivedCategory :
    (trW (homologyProp P)).Localization ⥤ DerivedCategory D :=
  Localization.lift L.mapDerivedCategory (fun _ _ f hf ↦ (mem_trW_iff L P f).1 hf)
    (trW (homologyProp P)).Q

private noncomputable def liftMapDerivedCategoryFactors :
    (trW (homologyProp P)).Q ⋙ liftMapDerivedCategory L P ≅ L.mapDerivedCategory :=
  Localization.fac _ (fun _ _ f hf ↦ (mem_trW_iff L P f).1 hf) _

section Adjoint

variable {u : D ⥤ C} [u.Additive] [u.Full] [u.Faithful] (adj : u ⊣ L)

/-- **The content of [Stacks, Tag 06XM].** The counit `u L K ⟶ K` of a cochain complex of `𝒜` has
its cone in `D_ℬ(𝒜)`, hence becomes invertible in the Verdier quotient `D(𝒜)/D_ℬ(𝒜)`: it is
inverted by `D(L)`, being an isomorphism in every degree after applying `L`. -/
private lemma trW_Q_map_counitCochainComplex_app (K : CochainComplex C ℤ) :
    trW (homologyProp P) (DerivedCategory.Q.map ((counitCochainComplex L adj).app K)) := by
  rw [trW_Q_map_iff L P]
  have := isIso_map_counitCochainComplex_app L adj K
  infer_instance

private lemma isIso_whiskerRight_counitCochainComplex :
    IsIso (Functor.whiskerRight (counitCochainComplex L adj)
      (DerivedCategory.Q ⋙ (trW (homologyProp P)).Q)) := by
  have (K : CochainComplex C ℤ) : IsIso ((Functor.whiskerRight (counitCochainComplex L adj)
      (DerivedCategory.Q ⋙ (trW (homologyProp P)).Q)).app K) :=
    Localization.inverts (trW (homologyProp P)).Q (trW (homologyProp P)) _
      (trW_Q_map_counitCochainComplex_app L P adj K)
  exact NatIso.isIso_of_isIso_app _

include L adj in
/-- Applying `u` termwise to a quasi-isomorphism of complexes of `𝒜/ℬ` gives a morphism inverted
in `D(𝒜)/D_ℬ(𝒜)`, because `L ∘ u ≅ 𝟭`. -/
private lemma isInvertedBy_quasiIso :
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)).IsInvertedBy
      (u.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ (trW (homologyProp P)).Q) := fun K K' f hf ↦ by
  refine Localization.inverts (trW (homologyProp P)).Q (trW (homologyProp P)) _
    ((trW_Q_map_iff L P _).2 ?_)
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (mapHomologicalComplexCompIsoId L adj) DerivedCategory.Q) f).2 ?_
  exact Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso D _) _ hf

include L adj in
/-- The quasi-inverse of `D(𝒜)/D_ℬ(𝒜) ⥤ D(𝒜/ℬ)`: `u` applied termwise to cochain complexes,
descended to the derived categories. -/
private noncomputable def quasiInverse :
    DerivedCategory D ⥤ (trW (homologyProp P)).Localization :=
  Localization.lift (u.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⋙ (trW (homologyProp P)).Q) (isInvertedBy_quasiIso L P adj)
    DerivedCategory.Q

private noncomputable def quasiInverseFactors :
    DerivedCategory.Q ⋙ quasiInverse L P adj ≅ u.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⋙ (trW (homologyProp P)).Q :=
  Localization.fac _ (isInvertedBy_quasiIso L P adj) DerivedCategory.Q

/-- One composite is the identity because `L ∘ u ≅ 𝟭`. -/
private noncomputable def quasiInverseCompLiftIso :
    quasiInverse L P adj ⋙ liftMapDerivedCategory L P ≅ 𝟭 (DerivedCategory D) :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (quasiInverse L P adj ⋙ liftMapDerivedCategory L P))
    DerivedCategory.Q _ _
    (Functor.isoWhiskerRight (quasiInverseFactors L P adj) (liftMapDerivedCategory L P) ≪≫
      Functor.isoWhiskerLeft (u.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        (liftMapDerivedCategoryFactors L P) ≪≫
      Functor.isoWhiskerLeft (u.mapHomologicalComplex (ComplexShape.up ℤ))
        L.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (mapHomologicalComplexCompIsoId L adj) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor)

/-- `D(L)` followed by the quasi-inverse is the localization functor `D(𝒜) ⥤ D(𝒜)/D_ℬ(𝒜)`:
on a complex `K` this is the counit `u L K ⟶ K`, invertible in the quotient. -/
private noncomputable def mapDerivedCategoryCompQuasiInverseIso :
    L.mapDerivedCategory ⋙ quasiInverse L P adj ≅ (trW (homologyProp P)).Q :=
  have := isIso_whiskerRight_counitCochainComplex L P adj
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (L.mapDerivedCategory ⋙ quasiInverse L P adj))
    (DerivedCategory.Q ⋙ (trW (homologyProp P)).Q) _ _
    (Functor.isoWhiskerRight L.mapDerivedCategoryFactors (quasiInverse L P adj) ≪≫
      Functor.isoWhiskerLeft (L.mapHomologicalComplex (ComplexShape.up ℤ))
        (quasiInverseFactors L P adj) ≪≫
      asIso (Functor.whiskerRight (counitCochainComplex L adj)
        (DerivedCategory.Q ⋙ (trW (homologyProp P)).Q)))

/-- The other composite is the identity because the counit is invertible in the quotient. -/
private noncomputable def liftCompQuasiInverseIso :
    𝟭 ((trW (homologyProp P)).Localization) ≅
      liftMapDerivedCategory L P ⋙ quasiInverse L P adj :=
  (Localization.liftNatIso (trW (homologyProp P)).Q (trW (homologyProp P))
    ((trW (homologyProp P)).Q ⋙ (liftMapDerivedCategory L P ⋙ quasiInverse L P adj))
    (trW (homologyProp P)).Q _ _
    (Functor.isoWhiskerRight (liftMapDerivedCategoryFactors L P) (quasiInverse L P adj) ≪≫
      mapDerivedCategoryCompQuasiInverseIso L P adj)).symm

include L adj in
/-- The equivalence `D(𝒜)/D_ℬ(𝒜) ≌ D(𝒜/ℬ)` induced by `D(L)`. -/
private noncomputable def equivalence :
    (trW (homologyProp P)).Localization ≌ DerivedCategory D :=
  .mk (liftMapDerivedCategory L P) (quasiInverse L P adj)
    (liftCompQuasiInverseIso L P adj) (quasiInverseCompLiftIso L P adj)

end Adjoint

end

/-- **Stacks 06XM.** Let `𝒜` be an abelian category, let `ℬ ⊆ 𝒜` be a Serre subcategory (a Serre
class `P` of objects of `C = 𝒜`) and let `L : 𝒜 ⥤ 𝒜/ℬ` be the quotient functor, i.e. a
localization functor for `P.isoModSerre`. Assume `L` has a left adjoint `u` with `L ∘ u ≅ 𝟭`,
equivalently `u` fully faithful. Then `D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)`: the induced functor
`L.mapDerivedCategory : D(𝒜) ⥤ D(𝒜/ℬ)` is a localization functor for the class of morphisms of
`D(𝒜)` whose cone has all its cohomology objects in `ℬ`. -/
@[stacks 06XM]
public theorem SerreClassLocalization.isLocalization_mapDerivedCategory_of_leftAdjoint
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]
    [L.IsLocalization P.isoModSerre] [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {u : D ⥤ C} [u.Full] [u.Faithful] (adj : u ⊣ L) :
    L.mapDerivedCategory.IsLocalization
      (trW (fun X : DerivedCategory C ↦
        ∀ n : ℤ, P ((DerivedCategory.homologyFunctor C n).obj X))) :=
  have : u.Additive := adj.left_adjoint_additive
  Functor.IsLocalization.of_equivalence_target (trW (homologyProp P)).Q (trW (homologyProp P))
    L.mapDerivedCategory (equivalence L P adj) (liftMapDerivedCategoryFactors L P)

end LeftAdjoint

/-! ### `D⁻(ℬ) ≌ D⁻_ℬ(𝒜)` when `ℬ` has enough subobjects -/

section Minus

open Limits ZeroObject _root_.DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A) [P.IsSerreClass]
  [P.IsClosedUnderFiniteProducts] [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} P.FullSubcategory]

section Covers

omit [P.IsSerreClass] [P.IsClosedUnderFiniteProducts] [PreservesFiniteLimits P.ι]
  [PreservesFiniteColimits P.ι] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} P.FullSubcategory]

/-- The hypothesis of [Stacks, Tag 0FCL] on the class `P`: every epimorphism `f : X ⟶ Y` of `A`
whose target lies in `P` is hit by an object of `P`, i.e. there are `X'` in `P` and `g : X' ⟶ X`
with `g ≫ f` again epi. When `P` is a Serre class this is the source's hypothesis, which asks
for a *subobject* of `X` lying in `P` and surjecting onto `Y`: replace `g` by its image, a
subobject of `X` which lies in `P` because it is a quotient of `X'`. -/
private def CoversEpis : Prop :=
  ∀ ⦃X Y : A⦄ (f : X ⟶ Y), Epi f → P Y → ∃ (X' : A) (g : X' ⟶ X), P X' ∧ Epi (g ≫ f)

end Covers

section Lift

omit [P.IsSerreClass] [P.IsClosedUnderFiniteProducts] [PreservesFiniteLimits P.ι]
  [PreservesFiniteColimits P.ι] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} P.FullSubcategory]

/-- A cochain complex of `A` all of whose terms lie in `P` viewed as a cochain complex of
`P.FullSubcategory`. -/
private def liftCochainComplex (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) :
    CochainComplex P.FullSubcategory ℤ where
  X i := ⟨K.X i, hK i⟩
  d i j := ObjectProperty.homMk (K.d i j)
  shape i j h := by ext; exact K.shape i j h
  d_comp_d' i j k _ _ := by ext; simp

private lemma mapHomologicalComplex_liftCochainComplex
    (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) :
    (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj (liftCochainComplex P K hK) = K :=
  rfl

private lemma isStrictlyLE_liftCochainComplex (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i))
    (n : ℤ) [K.IsStrictlyLE n] : (liftCochainComplex P K hK).IsStrictlyLE n := by
  rw [← CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ P.ι n,
    mapHomologicalComplex_liftCochainComplex]
  infer_instance

/-- A morphism from a cochain complex of `A` all of whose terms lie in `P` to the underlying
complex of a cochain complex of `P.FullSubcategory`, viewed as a morphism of cochain complexes
of `P.FullSubcategory`. -/
private def liftHom {K : CochainComplex A ℤ} (hK : ∀ i, P (K.X i))
    {L : CochainComplex P.FullSubcategory ℤ}
    (f : K ⟶ (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    liftCochainComplex P K hK ⟶ L where
  f i := ObjectProperty.homMk (f.f i)
  comm' i j _ := by ext; exact f.comm i j

/-- The underlying complex of `liftCochainComplex P K hK` is `K`. This isomorphism is the
identity, but stating the identification as a morphism rather than relying on the
definitional equality keeps every composite below type-correct without unfolding. -/
private def liftCochainComplexIso (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) :
    (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj (liftCochainComplex P K hK) ≅ K :=
  Iso.refl _

private lemma map_liftHom {K : CochainComplex A ℤ} (hK : ∀ i, P (K.X i))
    {L : CochainComplex P.FullSubcategory ℤ}
    (f : K ⟶ (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map (liftHom P hK f) =
      (liftCochainComplexIso P K hK).hom ≫ f :=
  (Category.id_comp f).symm

end Lift

/-- The cohomology objects of an object of `D(A)` coming from `D(B)` lie in `P`. -/
private lemma prop_homology_mapDerivedCategory_obj (X : DerivedCategory P.FullSubcategory)
    (i : ℤ) : P ((homologyFunctor A i).obj (P.ι.mapDerivedCategory.obj X)) :=
  P.prop_of_iso (homologyMapDerivedCategoryObjIso P.ι X i).symm
    (P.prop_ι_obj ((homologyFunctor P.FullSubcategory i).obj X))

section Key

omit [P.IsClosedUnderFiniteProducts] [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} P.FullSubcategory]

/-- **The key step**: a bounded above complex of `A` all of whose cohomology objects lie in the
Serre subcategory cut out by `P` receives a quasi-isomorphism from a bounded above complex all
of whose terms lie in that subcategory. -/
private lemma exists_quasiIso_of_prop_homology (hP : CoversEpis P)
    (X : CochainComplex A ℤ) (a : ℤ) [X.IsStrictlyLE a] (hX : ∀ i, P (X.homology i)) :
    ∃ (Y : CochainComplex A ℤ) (_ : Y.IsStrictlyLE a) (f : Y ⟶ X) (_ : QuasiIso f),
      ∀ i, P (Y.X i) := by
  refine Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
    P (fun Z => P Z) X ?_ P.prop_zero ?_ ?_ a hX
  · intro V W f hf hW
    obtain ⟨V', g, hV', hepi⟩ := hP f hf hW
    exact ⟨V', g, hV', hV', hepi⟩
  · intro C E hC hE
    exact P.prop_biprod hC hE
  · intro V W e he hV
    exact P.prop_of_iso (asIso e) hV

end Key

section Resolutions

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} P.FullSubcategory]

/-- If a complex of `A` is quasi-isomorphic to a complex of the Serre subcategory cut out by
`P`, then all its cohomology objects lie in `P`. -/
private lemma prop_homology_of_quasiIso {Z : CochainComplex A ℤ}
    {K : CochainComplex P.FullSubcategory ℤ}
    (t : Z ⟶ (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) [QuasiIso t] (i : ℤ) :
    P (Z.homology i) :=
  P.prop_of_iso (asIso (HomologicalComplex.homologyMap t i)).symm
    (P.prop_of_iso (mapHomologicalComplexHomologyIso P.ι K i).symm
      (P.prop_ι_obj (K.homology i)))

/-- `liftHom` sends quasi-isomorphisms to quasi-isomorphisms. -/
private lemma quasiIso_liftHom {K : CochainComplex A ℤ} (hK : ∀ i, P (K.X i))
    {L : CochainComplex P.FullSubcategory ℤ}
    (f : K ⟶ (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) (hf : QuasiIso f) :
    QuasiIso (liftHom P hK f) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (liftHom P hK f) P.ι]
  exact hf

end Resolutions

section Homotopies

omit [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} P.FullSubcategory]

/-- A morphism of cochain complexes of the Serre subcategory cut out by `P` which is
null-homotopic in `A` is null-homotopic. -/
private lemma quotient_map_eq_zero {K L : CochainComplex P.FullSubcategory ℤ} (u : K ⟶ L)
    (hu : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map u) = 0) :
    (HomotopyCategory.quotient P.FullSubcategory (ComplexShape.up ℤ)).map u = 0 := by
  have h := (P.ι.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.naturality u
  simp only [Functor.comp_map, hu, comp_zero] at h
  apply (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map_injective
  rw [Functor.map_zero, ← cancel_mono
    ((P.ι.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L), zero_comp]
  exact h

end Homotopies

section Zero

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A morphism of cochain complexes vanishes in the derived category if and only if its image
in the localization of the homotopy category vanishes. -/
private lemma Qh_map_quotient_map_eq_zero_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) = 0 ↔ Q.map f = 0 := by
  constructor
  · intro h
    rw [← cancel_epi ((quotientCompQhIso C).hom.app K), comp_zero,
      ← quotientCompQhIso_hom_naturality, h, zero_comp]
  · intro h
    rw [← cancel_mono ((quotientCompQhIso C).hom.app L), zero_comp,
      quotientCompQhIso_hom_naturality, h, comp_zero]

end Zero

/-- The core of full faithfulness: a morphism of cochain complexes of the Serre subcategory cut
out by `P` whose source is bounded above and which vanishes in `D(A)` already vanishes in
`D(B)`. -/
private lemma Q_map_eq_zero_of_map_eq_zero (hP : CoversEpis P)
    {K L : CochainComplex P.FullSubcategory ℤ} (n : ℤ) [K.IsStrictlyLE n] (g : K ⟶ L)
    (hg : Q.map ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g) = 0) :
    Q.map g = 0 := by
  have hKA : CochainComplex.IsStrictlyLE
      ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K P.ι n).2 inferInstance
  obtain ⟨Zbar, sbar, hsbar, hcomp⟩ := (MorphismProperty.map_eq_iff_precomp Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) 0).1
      (by rw [Functor.map_zero]; exact (Qh_map_quotient_map_eq_zero_iff _).2 hg)
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Zbar
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective sbar
  rw [comp_zero, ← Functor.map_comp] at hcomp
  have hqs : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hsbar
  have hZLE : CochainComplex.IsLE Z n := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (CochainComplex.isZero_of_isLE _ n i hi).of_iso
      (asIso (HomologicalComplex.homologyMap s i))
  have hqt : QuasiIso (CochainComplex.ιTruncLE Z n ≫ s) := inferInstance
  obtain ⟨Y₀, hY₀, f, hf, hPY₀⟩ :=
    exists_quasiIso_of_prop_homology P hP (CochainComplex.truncLE Z n) n
      (fun i ↦ prop_homology_of_quasiIso P (CochainComplex.ιTruncLE Z n ≫ s) i)
  have := hf
  have hu : IsIso (Q.map (liftHom P hPY₀ (f ≫ CochainComplex.ιTruncLE Z n ≫ s))) :=
    (isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_liftHom P hPY₀ _ inferInstance)
  have hmap : (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (liftHom P hPY₀ (f ≫ CochainComplex.ιTruncLE Z n ≫ s) ≫ g) =
      (liftCochainComplexIso P Y₀ hPY₀).hom ≫ f ≫ CochainComplex.ιTruncLE Z n ≫
        (s ≫ (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    rw [Functor.map_comp, map_liftHom]
    simp only [Category.assoc]
  have hzero : Q.map (liftHom P hPY₀ (f ≫ CochainComplex.ιTruncLE Z n ≫ s) ≫ g) = 0 := by
    refine (Qh_map_quotient_map_eq_zero_iff _).1 ?_
    rw [quotient_map_eq_zero P _ (by
        rw [hmap, Functor.map_comp, Functor.map_comp, Functor.map_comp, hcomp, comp_zero,
          comp_zero, comp_zero]), Functor.map_zero]
  rw [Functor.map_comp] at hzero
  exact (cancel_epi (Q.map (liftHom P hPY₀ (f ≫ CochainComplex.ιTruncLE Z n ≫ s)))).1
    (by rw [hzero, comp_zero])

/-- Every bounded above object of `D(A)` whose cohomology objects lie in `P` comes from
`D⁻(B)`. -/
private lemma essImage_of_isLE_of_prop_homology (hP : CoversEpis P)
    (X : DerivedCategory A) (n : ℤ) (hn : X.IsLE n)
    (hX : ∀ i : ℤ, P ((homologyFunctor A i).obj X)) :
    (Minus.ι ⋙ P.ι.mapDerivedCategory).essImage X := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  have hK : ∀ i, P (K.homology i) := fun i ↦ P.prop_of_iso
    (((homologyFunctorFactors A i).app K).symm ≪≫
      (homologyFunctor A i).mapIso e.symm).symm (hX i)
  obtain ⟨Y, hY, f, hf, hPY⟩ := exists_quasiIso_of_prop_homology P hP K n hK
  have hf' : IsIso (Q.map f) := by rw [isIso_Q_map_iff_quasiIso]; exact hf
  have e' : Q.obj Y ≅ Q.obj K := @asIso _ _ _ _ (Q.map f) hf'
  have hLE := isStrictlyLE_liftCochainComplex P Y hPY n
  exact ⟨⟨Q.obj (liftCochainComplex P Y hPY), ⟨n, inferInstance⟩⟩,
    ⟨(P.ι.mapDerivedCategoryFactors.app (liftCochainComplex P Y hPY)) ≪≫
      e' ≪≫ e.symm⟩⟩

/-- The core of faithfulness: a morphism of `D(B)` whose source is bounded above and which
vanishes in `D(A)` already vanishes. By the calculus of fractions it is `inv (Q.map s) ≫ Q.map g`
for morphisms of complexes `s`, `g` with bounded above source, so
`Q_map_eq_zero_of_map_eq_zero` applies to `g`. -/
private lemma eq_zero_of_map_eq_zero (hP : CoversEpis P)
    {X Y : DerivedCategory P.FullSubcategory} (n : ℤ) [X.IsLE n] (θ : X ⟶ Y)
    (hθ : P.ι.mapDerivedCategory.map θ = 0) : θ = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  obtain ⟨K', hK', s, hs, g, hfac⟩ := right_fac_of_isStrictlyLE
    (e.inv ≫ θ ≫ (Q.objObjPreimageIso Y).inv) n
  have h1 : P.ι.mapDerivedCategory.map (inv (Q.map s) ≫ Q.map g) = 0 := by
    rw [← hfac, Functor.map_comp, Functor.map_comp, hθ, zero_comp, comp_zero]
  rw [Functor.map_comp, Functor.map_inv] at h1
  have h2 : P.ι.mapDerivedCategory.map (Q.map g) = 0 :=
    (cancel_epi (inv (P.ι.mapDerivedCategory.map (Q.map s)))).1 (by rw [h1, comp_zero])
  have h3 : Q.map ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g) = 0 := by
    have hnat := P.ι.mapDerivedCategoryFactors.hom.naturality g
    simp only [Functor.comp_map] at hnat
    rw [← cancel_epi (P.ι.mapDerivedCategoryFactors.hom.app K'), comp_zero, ← hnat, h2,
      zero_comp]
  have h4 : e.inv ≫ θ ≫ (Q.objObjPreimageIso Y).inv = 0 := by
    rw [hfac, Q_map_eq_zero_of_map_eq_zero P hP n g h3, comp_zero]
  calc θ = e.hom ≫ (e.inv ≫ θ ≫ (Q.objObjPreimageIso Y).inv) ≫
            (Q.objObjPreimageIso Y).hom := by simp
    _ = 0 := by rw [h4, zero_comp, comp_zero]

/-- The canonical functor `D⁻(B) ⥤ D(A)` is faithful. -/
private lemma faithful_minus_mapDerivedCategory (hP : CoversEpis P) :
    (Minus.ι ⋙ P.ι.mapDerivedCategory).Faithful where
  map_injective {X Y φ ψ} h := by
    obtain ⟨n, hn⟩ := X.2
    have := hn
    apply Minus.ι.map_injective
    rw [← sub_eq_zero]
    refine eq_zero_of_map_eq_zero P hP (X := X.1) (Y := Y.1) n _ ?_
    rw [Functor.map_sub, sub_eq_zero]
    exact h

/-- The canonical functor `D⁻(B) ⥤ D(A)` is full. -/
private lemma full_minus_mapDerivedCategory (hP : CoversEpis P) :
    (Minus.ι ⋙ P.ι.mapDerivedCategory).Full where
  map_surjective {X Y} ψ := by
    obtain ⟨n₁, hn₁⟩ := X.2
    obtain ⟨n₂, hn₂⟩ := Y.2
    have := hn₁
    have := hn₂
    obtain ⟨U, hU, ⟨eX⟩⟩ := X.1.exists_iso_Q_obj_of_isLE n₁
    obtain ⟨V, hV, ⟨eY⟩⟩ := Y.1.exists_iso_Q_obj_of_isLE n₂
    have hUA : CochainComplex.IsStrictlyLE
        ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj U) n₁ :=
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff U P.ι n₁).2 hU
    obtain ⟨Z, hZ, t, ht, k, hfac⟩ := right_fac_of_isStrictlyLE
      (P.ι.mapDerivedCategoryFactors.inv.app U ≫ P.ι.mapDerivedCategory.map eX.inv ≫ ψ ≫
        P.ι.mapDerivedCategory.map eY.hom ≫ P.ι.mapDerivedCategoryFactors.hom.app V) n₁
    have hqt : QuasiIso t := (isIso_Q_map_iff_quasiIso A t).1 ht
    obtain ⟨Y₀, hY₀, f, hf, hPY₀⟩ := exists_quasiIso_of_prop_homology P hP Z n₁
      (fun i ↦ prop_homology_of_quasiIso P t i)
    have := hf
    have hA1 : IsIso (Q.map (liftHom P hPY₀ (f ≫ t))) :=
      (isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_liftHom P hPY₀ (f ≫ t) inferInstance)
    refine ⟨Minus.ι.preimage (eX.hom ≫ inv (Q.map (liftHom P hPY₀ (f ≫ t))) ≫
      Q.map (liftHom P hPY₀ (f ≫ k)) ≫ eY.inv), ?_⟩
    have hnt := P.ι.mapDerivedCategoryFactors.hom.naturality (liftHom P hPY₀ (f ≫ t))
    have hnk := P.ι.mapDerivedCategoryFactors.hom.naturality (liftHom P hPY₀ (f ≫ k))
    simp only [Functor.comp_map, map_liftHom] at hnt hnk
    have hkey : P.ι.mapDerivedCategory.map (inv (Q.map (liftHom P hPY₀ (f ≫ t))) ≫
        Q.map (liftHom P hPY₀ (f ≫ k))) =
        P.ι.mapDerivedCategoryFactors.hom.app U ≫ (inv (Q.map t) ≫ Q.map k) ≫
          P.ι.mapDerivedCategoryFactors.inv.app V := by
      rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq,
        ← cancel_mono (P.ι.mapDerivedCategoryFactors.hom.app V), hnk]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [reassoc_of% hnt]
      simp [Functor.map_comp]
    rw [Functor.comp_map, Functor.map_preimage,
      show eX.hom ≫ inv (Q.map (liftHom P hPY₀ (f ≫ t))) ≫
            Q.map (liftHom P hPY₀ (f ≫ k)) ≫ eY.inv =
          eX.hom ≫ (inv (Q.map (liftHom P hPY₀ (f ≫ t))) ≫
            Q.map (liftHom P hPY₀ (f ≫ k))) ≫ eY.inv from by simp,
      Functor.map_comp, Functor.map_comp, hkey, ← hfac]
    simp

/-- Let `A` be an abelian category and `P` a Serre class in `A`, cutting out the Serre
subcategory `B = P.FullSubcategory`. Assume that for every epimorphism `f : X ⟶ Y` of `A` with
`Y ∈ B` there is an object `X'` of `B` and a morphism `g : X' ⟶ X` such that `g ≫ f` is again
epi (equivalently: some subobject of `X` belonging to `B` surjects onto `Y`). Then the
canonical functor `D⁻(B) ⥤ D⁻_B(A)` is an equivalence: the composite
`D⁻(B) ⥤ D(A)` is full and faithful and its essential image consists exactly of the bounded
above objects all of whose cohomology objects lie in `B`. -/
@[stacks 0FCL]
public theorem full_faithful_essImage_minus_mapDerivedCategory
    {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A) [P.IsSerreClass]
    [P.IsClosedUnderFiniteProducts] [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} P.FullSubcategory]
    (hP : ∀ ⦃X Y : A⦄ (f : X ⟶ Y), Epi f → P Y → ∃ (X' : A) (g : X' ⟶ X), P X' ∧ Epi (g ≫ f)) :
    (Minus.ι ⋙ P.ι.mapDerivedCategory).Full ∧
      (Minus.ι ⋙ P.ι.mapDerivedCategory).Faithful ∧
      ∀ X : DerivedCategory A, (Minus.ι ⋙ P.ι.mapDerivedCategory).essImage X ↔
        ((∃ n : ℤ, X.IsLE n) ∧ ∀ i : ℤ, P ((homologyFunctor A i).obj X)) := by
  refine ⟨full_minus_mapDerivedCategory P hP, faithful_minus_mapDerivedCategory P hP,
    fun X ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨Y, ⟨e⟩⟩
    obtain ⟨n, hn⟩ := Y.2
    dsimp at e
    have := hn
    have := isLE_mapDerivedCategory_obj P.ι Y.1 n
    refine ⟨⟨n, TStructure.t.isLE_of_iso e n⟩, fun i ↦ P.prop_of_iso
      ((homologyFunctor A i).mapIso e) (prop_homology_mapDerivedCategory_obj P Y.1 i)⟩
  · rintro ⟨⟨n, hn⟩, hX⟩
    exact essImage_of_isLE_of_prop_homology P hP X n hn hX

end Minus

end CategoryTheory.ObjectProperty

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, `A` is an abelian category. We work with the derived category
`D(A) = DerivedCategory A`, viewed as a triangulated category, together with its
cohomology functors `H^n : D(A) → A` for `n ∈ ℤ`
(`DerivedCategory.homologyFunctor A n`).

We identify a full subcategory of a category with the *property* on objects that
cuts it out (a predicate `P` on objects, i.e. a `CategoryTheory.ObjectProperty`).

## Main Definitions

* Definition 1 (Weak Serre subcategory; Stacks 02MO): a full subcategory
  `B ⊆ A` is a weak Serre subcategory if it is closed under isomorphism,
  nonempty, and for every exact sequence `A₀ → A₁ → A₂ → A₃ → A₄` in `A` with
  `A₀, A₁, A₃, A₄ ∈ B` (exact at `A₁, A₂, A₃`), also `A₂ ∈ B`.

* Definition 2 (`D_B(A)`; Stacks 06UP): for a weak Serre subcategory `B`, the
  strictly full subcategory of `D(A)` of objects `X` with `H^n(X) ∈ B` for all
  `n ∈ ℤ`.  The bounded versions intersect with the cohomologically bounded
  (below / above / both) subcategories.

* Definition 3 (Triangulated subcategory): captured by
  `ObjectProperty.IsTriangulated` (fields `ContainsZero`, `IsStableUnderShift ℤ`,
  `IsTriangulatedClosed₂`).

* Definition 4 (Saturated / thick subcategory; Stacks 05RB): a triangulated
  subcategory closed under direct summands / retracts, captured by
  `ObjectProperty.IsStableUnderRetracts`.

## Main Statements

* Statement 1 (Stacks 06UQ, unbounded): `D_B(A)` is a strictly full, saturated,
  triangulated subcategory of `D(A)`.

* Statement 2 (Stacks 06UQ, bounded): the same for `D^+_B(A)`, `D^-_B(A)`,
  `D^b_B(A)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace WeakSerre

variable {A : Type*} [Category A] [Abelian A]

/-- A sequence `A₀ →(f₀) A₁ →(f₁) A₂ →(f₂) A₃ →(f₃) A₄` of length five in `A`, exact at
`A₁`, `A₂` and `A₃`. -/
structure Exact5 (A : Type*) [Category A] [Abelian A] where
  /-- The object `A₀`. -/
  obj₀ : A
  /-- The object `A₁`. -/
  obj₁ : A
  /-- The object `A₂`. -/
  obj₂ : A
  /-- The object `A₃`. -/
  obj₃ : A
  /-- The object `A₄`. -/
  obj₄ : A
  /-- The map `f₀ : A₀ ⟶ A₁`. -/
  f₀ : obj₀ ⟶ obj₁
  /-- The map `f₁ : A₁ ⟶ A₂`. -/
  f₁ : obj₁ ⟶ obj₂
  /-- The map `f₂ : A₂ ⟶ A₃`. -/
  f₂ : obj₂ ⟶ obj₃
  /-- The map `f₃ : A₃ ⟶ A₄`. -/
  f₃ : obj₃ ⟶ obj₄
  /-- The composition `f₀ ≫ f₁` vanishes. -/
  zero₀ : f₀ ≫ f₁ = 0 := by aesop_cat
  /-- The composition `f₁ ≫ f₂` vanishes. -/
  zero₁ : f₁ ≫ f₂ = 0 := by aesop_cat
  /-- The composition `f₂ ≫ f₃` vanishes. -/
  zero₂ : f₂ ≫ f₃ = 0 := by aesop_cat
  /-- Exactness at `obj₁`. -/
  exact₁ : (ShortComplex.mk f₀ f₁ zero₀).Exact
  /-- Exactness at `obj₂`. -/
  exact₂ : (ShortComplex.mk f₁ f₂ zero₁).Exact
  /-- Exactness at `obj₃`. -/
  exact₃ : (ShortComplex.mk f₂ f₃ zero₂).Exact

/-- **Definition 1 (Weak Serre subcategory; Stacks 02MO).**
An object property `B` on an abelian category `A` is a *weak Serre subcategory*
if it is closed under isomorphism, nonempty, and for every length-5 exact
sequence with the four outer terms in `B`, the middle term is in `B`. -/
structure IsWeakSerre (B : ObjectProperty A) : Prop where
  /-- Closed under isomorphism (strictly full). -/
  isClosedUnderIsomorphisms : B.IsClosedUnderIsomorphisms
  /-- Nonempty. -/
  nonempty : ∃ X, B X
  /-- The defining closure condition: in an exact `A₀ → A₁ → A₂ → A₃ → A₄`,
  if the four outer terms are in `B` then so is the middle term. -/
  mem_of_exact5 : ∀ (E : Exact5 A), B E.obj₀ → B E.obj₁ → B E.obj₃ → B E.obj₄ →
    B E.obj₂

end WeakSerre

namespace DerivedCategoryB

open WeakSerre

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- **Definition 2 (the subcategory `D_B(A)`; Stacks 06UP).**
For an object property `B` on `A`, this is the object property on `D(A)`
selecting objects all of whose cohomology objects satisfy `B`. -/
@[sga "4 Vbis 2.4.1" "partial",
  sga "4 Vbis 2.4.2" "partial",
  sga "4 XVII 5.1.13" "more general",
  sga "4½ Dualite 1.1" "more general",
  sga "5 I App.1.1" "more general",
  sga "5 I App.1.2",
  sga "5 III 6.1" "more general",
  sga "5 IIIB 6.1" "more general",
  sga "6 II 3.7" "more general",
  sga "6 IV 1.6"]
def derivedCategoryB (B : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun X => ∀ n : ℤ, B ((DerivedCategory.homologyFunctor A n).obj X)

omit [HasDerivedCategory A] in
/-- A zero object of `A` lies in any weak Serre subcategory. -/
theorem zero_mem_of_isWeakSerre (B : ObjectProperty A) (hB : IsWeakSerre B)
    (O : A) (hO : IsZero O) : B O := by
  obtain ⟨X, hX⟩ := hB.nonempty
  -- the exact sequence `X --id--> X --0--> O --0--> X --id--> X`
  refine hB.mem_of_exact5
    { obj₀ := X, obj₁ := X, obj₂ := O, obj₃ := X, obj₄ := X
      f₀ := 𝟙 X, f₁ := 0, f₂ := 0, f₃ := 𝟙 X
      zero₀ := by simp, zero₁ := by simp, zero₂ := by simp
      exact₁ := ?_, exact₂ := ?_, exact₃ := ?_ } hX hX hX hX
  · exact (ShortComplex.exact_iff_epi _ rfl).mpr inferInstance
  · exact ShortComplex.exact_of_isZero_X₂ _ hO
  · exact (ShortComplex.exact_iff_mono _ rfl).mpr inferInstance

omit [HasDerivedCategory A] in
/-- A weak Serre subcategory is closed under retracts (direct summands).
SANITY CHECK PASSED.

Mathematical argument: given a retract `i ≫ r = 𝟙 X` of `X` in `Y`, the
idempotent `e := r ≫ i : Y → Y` satisfies `e ≫ e = e`, and we have a
(split) exact sequence
  `Y --(𝟙 - r≫i)--> Y --r--> X --0--> Z --0--> Z`
(with `Z` a zero object), exact at `Y`, `X`, `Z`: `r` is a split epimorphism
(section `i`), its kernel is the image of `𝟙 - r≫i`, and the tail is exact since
`Z` is zero.  All four outer terms `Y, Y, Z, Z` lie in `B`, so by the weak Serre
condition the middle term `X ∈ B`. -/
theorem retract_mem_of_isWeakSerre (B : ObjectProperty A) (hB : IsWeakSerre B)
    {X Y : A} (h : Retract X Y) (hY : B Y) : B X := by
  obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject A)
  set i := h.i
  set r := h.r
  have hr : i ≫ r = 𝟙 X := h.retract
  refine hB.mem_of_exact5
    { obj₀ := Y, obj₁ := Y, obj₂ := X, obj₃ := Z, obj₄ := Z
      f₀ := 𝟙 Y - r ≫ i, f₁ := r, f₂ := 0, f₃ := 0
      zero₀ := by
        simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, hr,
          Category.comp_id, sub_self]
      zero₁ := by simp
      zero₂ := by simp
      exact₁ := ?_, exact₂ := ?_, exact₃ := ?_ }
    hY hY (zero_mem_of_isWeakSerre B hB Z hZ) (zero_mem_of_isWeakSerre B hB Z hZ)
  · -- exactness at obj₁ = Y: ker r = im (𝟙 - r≫i)
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have hz : (𝟙 Y - r ≫ i) ≫ r = 0 := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, hr,
        Category.comp_id, sub_self]
    have hsec : (kernel.ι r) ≫ (kernel.lift r (𝟙 Y - r ≫ i) hz) = 𝟙 _ := by
      apply equalizer.hom_ext
      simp only [Category.assoc, kernel.lift_ι, Category.id_comp, Preadditive.comp_sub,
        Category.comp_id]
      rw [← Category.assoc, kernel.condition]
      simp
    have : IsSplitEpi (kernel.lift r (𝟙 Y - r ≫ i) hz) := ⟨⟨kernel.ι r, hsec⟩⟩
    exact inferInstance
  · -- exactness at obj₂ = X: r is (split) epi and the next map is 0
    have : Epi r := ⟨fun g₁ g₂ hgh => by
      have := congrArg (i ≫ ·) hgh
      simpa [← Category.assoc, hr] using this⟩
    exact (ShortComplex.exact_iff_epi _ rfl).mpr this
  · -- exactness at obj₃ = Z (zero object)
    exact ShortComplex.exact_of_isZero_X₂ _ hZ

/-- Cohomologically bounded below: `H^n(X) = 0` for `n ≪ 0`. -/
@[ega "0 11.2.1" "special case",
  sga "4 Vbis 1.3.8" "partial",
  sga "4 Vbis 2.4.1",
  sga "4½ Etat_0 1.2.3",
  sga "4½ Etat_0 3.1.3"]
def IsBoundedBelow (X : DerivedCategory A) : Prop :=
  ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ → IsZero ((DerivedCategory.homologyFunctor A n).obj X)

/-- Cohomologically bounded above: `H^n(X) = 0` for `n ≫ 0`. -/
@[ega "0 11.2.1" "special case", sga "4½ Etat_0 1.2.3", sga "4½ Etat_0 3.1.3", sga "4½ Rapport 4.1"]
def IsBoundedAbove (X : DerivedCategory A) : Prop :=
  ∃ n₀ : ℤ, ∀ n : ℤ, n₀ < n → IsZero ((DerivedCategory.homologyFunctor A n).obj X)

/-- Cohomologically bounded: `H^n(X) = 0` for `|n| ≫ 0`. -/
@[sga "4½ Etat_0 1.2.3", sga "4½ Etat_0 3.1.3", sga "4½ Rapport 4.1", sga "6 IV 2.1" "partial"]
def IsBounded (X : DerivedCategory A) : Prop :=
  IsBoundedBelow X ∧ IsBoundedAbove X

/-- `D^+_B(A) = D^+(A) ∩ D_B(A)`. -/
@[sga "4 Vbis 1.3.8" "more general",
  sga "4 Vbis 2.4.1",
  sga "4 Vbis 2.4.2" "more general",
  sga "4½ Rapport 4.1" "more general",
  sga "6 II 3.5" "more general"]
def derivedCategoryBPlus (B : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun X => IsBoundedBelow X ∧ derivedCategoryB B X

/-- `D^-_B(A) = D^-(A) ∩ D_B(A)`. -/
@[sga "4½ Rapport 4.1" "more general", sga "6 I 1.1.5" "partial"]
def derivedCategoryBMinus (B : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun X => IsBoundedAbove X ∧ derivedCategoryB B X

/-- `D^b_B(A) = D^b(A) ∩ D_B(A)`. -/
@[sga "6 I 1.1.5" "partial", sga "6 IV 1.6"]
def derivedCategoryBBounded (B : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun X => IsBounded X ∧ derivedCategoryB B X

/-! ## Helper lemmas (unbounded case) -/

open DerivedCategory CategoryTheory.Pretriangulated

/-- The cohomology object `Hⁿ(X⟦a⟧)` is isomorphic to `Hᵃ⁺ⁿ(X)`. -/
private noncomputable def homologyShiftObjIso (a n : ℤ) (X : DerivedCategory A) :
    (homologyFunctor A n).obj ((shiftFunctor (DerivedCategory A) a).obj X) ≅
      (homologyFunctor A (a + n)).obj X :=
  ((homologyFunctor A 0).shiftIso a n (a + n) rfl).app X

/-- If `X` is a retract of `Y` and `Hⁿ(Y)` is zero, then so is `Hⁿ(X)`. -/
private theorem isZero_homology_of_retract {X Y : DerivedCategory A} (r : Retract X Y) (n : ℤ)
    (h : IsZero ((homologyFunctor A n).obj Y)) : IsZero ((homologyFunctor A n).obj X) := by
  have hr := r.map (homologyFunctor A n)
  rw [IsZero.iff_id_eq_zero, ← hr.retract, h.eq_zero_of_tgt hr.i, zero_comp]

/-- A property of `D(A)` which is closed under isomorphisms, contains zero, is stable under shifts
and closed under the middle term of distinguished triangles is triangulated. -/
private theorem isTriangulated_of_mem_obj₂ (P : ObjectProperty (DerivedCategory A))
    [P.ContainsZero] [P.IsStableUnderShift ℤ] [P.IsClosedUnderIsomorphisms]
    (h : ∀ T ∈ distinguishedTriangles, P T.obj₁ → P T.obj₃ → P T.obj₂) : P.IsTriangulated := by
  have : P.IsTriangulatedClosed₂ := ⟨fun T hT h₁ h₃ => P.le_isoClosure _ (h T hT h₁ h₃)⟩
  exact ⟨⟩

/-- `derivedCategoryB B` is closed under isomorphisms. -/
theorem derivedCategoryB_isClosedUnderIsomorphisms
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX n => ?_⟩
  exact hB.isClosedUnderIsomorphisms.of_iso ((homologyFunctor A n).mapIso e) (hX n)

/-- `derivedCategoryB B` contains a zero object. -/
theorem derivedCategoryB_containsZero
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).ContainsZero := by
  obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (DerivedCategory A))
  refine ⟨Z, hZ, fun n => ?_⟩
  apply zero_mem_of_isWeakSerre B hB
  exact (homologyFunctor A n).map_isZero hZ

/-- The key closure property: in a distinguished triangle whose first and third
vertices lie in `derivedCategoryB B`, the middle vertex does too. -/
theorem derivedCategoryB_mem_obj₂_of_distinguished
    (B : ObjectProperty A) (hB : IsWeakSerre B)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    (h₁ : derivedCategoryB B T.obj₁) (h₃ : derivedCategoryB B T.obj₃) :
    derivedCategoryB B T.obj₂ := by
  intro n
  set F := homologyFunctor A 0 with hF
  refine hB.mem_of_exact5
    { obj₀ := (F.shift (n - 1)).obj T.obj₃
      obj₁ := (F.shift n).obj T.obj₁
      obj₂ := (F.shift n).obj T.obj₂
      obj₃ := (F.shift n).obj T.obj₃
      obj₄ := (F.shift (n + 1)).obj T.obj₁
      f₀ := F.homologySequenceδ T (n - 1) n (by omega)
      f₁ := (F.shift n).map T.mor₁
      f₂ := (F.shift n).map T.mor₂
      f₃ := F.homologySequenceδ T n (n + 1) (by omega)
      zero₀ := F.homologySequenceδ_comp T hT (n - 1) n (by omega)
      zero₁ := by
        rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
      zero₂ := F.comp_homologySequenceδ T hT n (n + 1) (by omega)
      exact₁ := F.homologySequence_exact₁ T hT (n - 1) n (by omega)
      exact₂ := F.homologySequence_exact₂ T hT n
      exact₃ := F.homologySequence_exact₃ T hT n (n + 1) (by omega) }
    (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1))

/-- `derivedCategoryB B` is stable under the shift by any integer. -/
theorem derivedCategoryB_isStableUnderShift
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun X hX => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  intro n
  exact hB.isClosedUnderIsomorphisms.of_iso (homologyShiftObjIso a n X).symm (hX (a + n))

/-- Membership form of shift-stability for `derivedCategoryB B`. -/
theorem derivedCategoryB_shift_mem
    (B : ObjectProperty A) (hB : IsWeakSerre B)
    (a : ℤ) {X : DerivedCategory A} (hX : derivedCategoryB B X) :
    derivedCategoryB B ((shiftFunctor (DerivedCategory A) a).obj X) := by
  intro n
  exact hB.isClosedUnderIsomorphisms.of_iso (homologyShiftObjIso a n X).symm (hX (a + n))

/-- For a weak Serre subcategory `B` of `A`, the objects of `D(A)` all of whose cohomology
objects lie in `B` form a triangulated subcategory of `D(A)`. -/
@[sga "5 I App.1.2" "more general", sga "6 IV 1.6"]
theorem derivedCategoryB_isTriangulated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).IsTriangulated := by
  have : (derivedCategoryB B).ContainsZero := derivedCategoryB_containsZero B hB
  have : (derivedCategoryB B).IsStableUnderShift ℤ := derivedCategoryB_isStableUnderShift B hB
  have hcl : (derivedCategoryB B).IsClosedUnderIsomorphisms :=
    derivedCategoryB_isClosedUnderIsomorphisms B hB
  exact isTriangulated_of_mem_obj₂ _ fun T hT h₁ h₃ =>
    derivedCategoryB_mem_obj₂_of_distinguished B hB T hT h₁ h₃

/-- `derivedCategoryB B` is stable under retracts (saturated). -/
theorem derivedCategoryB_isStableUnderRetracts
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).IsStableUnderRetracts := by
  refine ⟨fun {X Y} r hY n => ?_⟩
  -- `H^n(X)` is a retract of `H^n(Y) ∈ B`
  exact retract_mem_of_isWeakSerre B hB (r.map (homologyFunctor A n)) (hY n)

/-! ## Helper lemmas (boundedness predicates)

The bounded variants `D^±_B`, `D^b_B` are intersections of `derivedCategoryB B`
with the cohomological boundedness predicates `IsBoundedBelow / IsBoundedAbove /
IsBounded`.  To show each variant is a strictly full saturated triangulated
subcategory, it suffices (since intersection of object properties preserves all
three closure conditions componentwise) to prove that each boundedness predicate
itself is iso-closed, contains zero, shift-stable, cone-closed, and
retract-closed.  These lemmas establish exactly that. -/

/-- `IsBoundedBelow` is invariant under isomorphism. -/
theorem isBoundedBelow_of_iso {X Y : DerivedCategory A} (e : X ≅ Y)
    (hX : IsBoundedBelow X) : IsBoundedBelow Y := by
  obtain ⟨n₀, h⟩ := hX
  refine ⟨n₀, fun n hn => ?_⟩
  -- `H^n(Y) ≅ H^n(X)`, and a zero object is preserved by isomorphism
  -- SANITY CHECK PASSED
  -- Strategy: `(homologyFunctor A n).mapIso e.symm : H^n Y ≅ H^n X`; then
  -- `IsZero.of_iso (h n hn) (...).symm` (or `Limits.IsZero.of_iso`).
  exact (h n hn).of_iso ((homologyFunctor A n).mapIso e.symm)

/-- `IsBoundedAbove` is invariant under isomorphism. -/
theorem isBoundedAbove_of_iso {X Y : DerivedCategory A} (e : X ≅ Y)
    (hX : IsBoundedAbove X) : IsBoundedAbove Y := by
  obtain ⟨n₀, h⟩ := hX
  refine ⟨n₀, fun n hn => ?_⟩
  -- SANITY CHECK PASSED.  Same as `isBoundedBelow_of_iso`.
  exact (h n hn).of_iso ((homologyFunctor A n).mapIso e.symm)

/-- `IsBounded` is invariant under isomorphism. -/
theorem isBounded_of_iso {X Y : DerivedCategory A} (e : X ≅ Y)
    (hX : IsBounded X) : IsBounded Y :=
  ⟨isBoundedBelow_of_iso e hX.1, isBoundedAbove_of_iso e hX.2⟩

/-- A zero object is bounded below. -/
theorem isBoundedBelow_of_isZero {X : DerivedCategory A} (hX : IsZero X) :
    IsBoundedBelow X := by
  -- SANITY CHECK PASSED.  `H^n(X)` is zero for *all* `n`, in particular `n < 0`.
  -- Strategy: `⟨0, fun n _ => (homologyFunctor A n).map_isZero hX⟩`.
  exact ⟨0, fun n _ => (homologyFunctor A n).map_isZero hX⟩

/-- A zero object is bounded above. -/
theorem isBoundedAbove_of_isZero {X : DerivedCategory A} (hX : IsZero X) :
    IsBoundedAbove X := by
  -- SANITY CHECK PASSED.
  exact ⟨0, fun n _ => (homologyFunctor A n).map_isZero hX⟩

/-- A zero object is bounded. -/
theorem isBounded_of_isZero {X : DerivedCategory A} (hX : IsZero X) :
    IsBounded X :=
  ⟨isBoundedBelow_of_isZero hX, isBoundedAbove_of_isZero hX⟩

/-- `IsBoundedBelow` is stable under shift: `X⟦a⟧` is bounded below if `X` is.
The shift by `a` translates cohomological degrees by `a`. -/
theorem isBoundedBelow_shift (a : ℤ) {X : DerivedCategory A}
    (hX : IsBoundedBelow X) : IsBoundedBelow ((shiftFunctor (DerivedCategory A) a).obj X) := by
  obtain ⟨n₀, h⟩ := hX
  -- `H^n(X⟦a⟧) ≅ H^(a+n)(X)`, which is zero once `a+n < n₀`, i.e. `n < n₀ - a`.
  -- SANITY CHECK PASSED.
  -- Strategy: use `n₀ - a` as the new bound; transport `IsZero` along
  -- `((homologyFunctor A 0).shift n).shiftIso a n (a+n) rfl |>.app X`
  -- (cf. `derivedCategoryB_isStableUnderShift`).
  exact ⟨n₀ - a, fun n hn => (h (a + n) (by omega)).of_iso (homologyShiftObjIso a n X)⟩

/-- `IsBoundedAbove` is stable under shift. -/
theorem isBoundedAbove_shift (a : ℤ) {X : DerivedCategory A}
    (hX : IsBoundedAbove X) : IsBoundedAbove ((shiftFunctor (DerivedCategory A) a).obj X) := by
  obtain ⟨n₀, h⟩ := hX
  -- SANITY CHECK PASSED.  Mirror of `isBoundedBelow_shift`; new bound `n₀ - a`.
  exact ⟨n₀ - a, fun n hn => (h (a + n) (by omega)).of_iso (homologyShiftObjIso a n X)⟩

/-- `IsBounded` is stable under shift. -/
theorem isBounded_shift (a : ℤ) {X : DerivedCategory A}
    (hX : IsBounded X) : IsBounded ((shiftFunctor (DerivedCategory A) a).obj X) :=
  ⟨isBoundedBelow_shift a hX.1, isBoundedAbove_shift a hX.2⟩

omit [HasDerivedCategory A] in
/-- An exact short complex with both outer terms zero has a zero middle term. -/
theorem ShortComplex.isZero_X₂_of_exact_of_isZero {S : ShortComplex A}
    (hS : S.Exact) (h1 : IsZero S.X₁) (h3 : IsZero S.X₃) : IsZero S.X₂ := by
  have hmono : Mono S.g := hS.mono_g (h1.eq_zero_of_src _)
  rw [IsZero.iff_id_eq_zero]
  have hg : S.g = 0 := h3.eq_zero_of_tgt _
  have h0 : (𝟙 S.X₂) ≫ S.g = 0 ≫ S.g := by rw [hg]; simp
  simpa using (cancel_mono S.g).mp h0

/-- If `Hⁿ(X)` and `Hⁿ(Z)` are zero in a distinguished triangle `X → Y → Z → X⟦1⟧`, so is
`Hⁿ(Y)`. -/
private theorem isZero_homology_obj₂ (T : Triangle (DerivedCategory A))
    (hT : T ∈ distinguishedTriangles) (n : ℤ) (h₁ : IsZero ((homologyFunctor A n).obj T.obj₁))
    (h₃ : IsZero ((homologyFunctor A n).obj T.obj₃)) :
    IsZero ((homologyFunctor A n).obj T.obj₂) :=
  ShortComplex.isZero_X₂_of_exact_of_isZero ((homologyFunctor A 0).homologySequence_exact₂ T hT n)
    h₁ h₃

/-- In a distinguished triangle `X → Y → Z → X⟦1⟧`, if both `X` and `Y` are
cohomologically bounded below then so is `Z`.

Mathematical argument: the long exact cohomology sequence gives, for each `n`,
exactness of `H^n(X) → H^n(Y) → H^n(Z) → H^{n+1}(X)`.  Choose `n₀` below which
`H^*(X) = 0` and `H^*(Y) = 0` (take the min of the two bounds).  For `n < n₀ - 1`
we have `H^n(Y) = 0` and `H^{n+1}(X) = 0` (since `n+1 < n₀`), so `H^n(Z)` is
squeezed between two zero objects in the exact sequence
`H^n(Y) → H^n(Z) → H^{n+1}(X)`, hence is zero. -/
theorem isBoundedBelow_mem_obj₂_of_distinguished
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    (h₁ : IsBoundedBelow T.obj₁) (h₃ : IsBoundedBelow T.obj₃) :
    IsBoundedBelow T.obj₂ := by
  -- For `n` below both bounds, `H^n(T.obj₁) = 0` and `H^n(T.obj₃) = 0`; the
  -- exact segment `H^n(T.obj₁) → H^n(T.obj₂) → H^n(T.obj₃)` then forces
  -- `H^n(T.obj₂) = 0` (`ShortComplex.isZero_X₂_of_exact_of_isZero`).
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₃, hn₃⟩ := h₃
  exact ⟨min n₁ n₃, fun n hn => isZero_homology_obj₂ T hT n
    (hn₁ n (lt_of_lt_of_le hn (min_le_left _ _))) (hn₃ n (lt_of_lt_of_le hn (min_le_right _ _)))⟩

/-- In a distinguished triangle, if `X` and `Y` are bounded above then so is `Z`. -/
theorem isBoundedAbove_mem_obj₂_of_distinguished
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    (h₁ : IsBoundedAbove T.obj₁) (h₃ : IsBoundedAbove T.obj₃) :
    IsBoundedAbove T.obj₂ := by
  -- Mirror of `isBoundedBelow_mem_obj₂_of_distinguished` using the upper bound.
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₃, hn₃⟩ := h₃
  exact ⟨max n₁ n₃, fun n hn => isZero_homology_obj₂ T hT n
    (hn₁ n (lt_of_le_of_lt (le_max_left _ _) hn)) (hn₃ n (lt_of_le_of_lt (le_max_right _ _) hn))⟩

/-- In a distinguished triangle, if `X` and `Y` are bounded then so is `Z`. -/
theorem isBounded_mem_obj₂_of_distinguished
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    (h₁ : IsBounded T.obj₁) (h₃ : IsBounded T.obj₃) :
    IsBounded T.obj₂ :=
  ⟨isBoundedBelow_mem_obj₂_of_distinguished T hT h₁.1 h₃.1,
   isBoundedAbove_mem_obj₂_of_distinguished T hT h₁.2 h₃.2⟩

/-- `IsBoundedBelow` is stable under retracts: a retract of a bounded-below
object is bounded below. -/
theorem isBoundedBelow_of_retract {X Y : DerivedCategory A} (r : Retract X Y)
    (hY : IsBoundedBelow Y) : IsBoundedBelow X := by
  obtain ⟨n₀, h⟩ := hY
  refine ⟨n₀, fun n hn => ?_⟩
  -- `H^n(X)` is a retract of `H^n(Y) = 0`, hence zero.
  exact isZero_homology_of_retract r n (h n hn)

/-- `IsBoundedAbove` is stable under retracts. -/
theorem isBoundedAbove_of_retract {X Y : DerivedCategory A} (r : Retract X Y)
    (hY : IsBoundedAbove Y) : IsBoundedAbove X := by
  obtain ⟨n₀, h⟩ := hY
  refine ⟨n₀, fun n hn => ?_⟩
  exact isZero_homology_of_retract r n (h n hn)

/-- `IsBounded` is stable under retracts. -/
theorem isBounded_of_retract {X Y : DerivedCategory A} (r : Retract X Y)
    (hY : IsBounded Y) : IsBounded X :=
  ⟨isBoundedBelow_of_retract r hY.1, isBoundedAbove_of_retract r hY.2⟩

/-! ### Assembly of bounded variants into closure structures

Given the boundedness closure lemmas above, each bounded variant is the
componentwise conjunction of a boundedness predicate and `derivedCategoryB B`,
so the three closure properties follow from the corresponding pairs. -/

/-- `derivedCategoryBPlus B` is closed under isomorphisms. -/
theorem derivedCategoryBPlus_isClosedUnderIsomorphisms
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX => ⟨isBoundedBelow_of_iso e hX.1, ?_⟩⟩
  exact (derivedCategoryB_isClosedUnderIsomorphisms B hB).of_iso e hX.2

/-- `derivedCategoryBPlus B` contains a zero object. -/
theorem derivedCategoryBPlus_containsZero
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).ContainsZero := by
  obtain ⟨Z, hZ, hZB⟩ := (derivedCategoryB_containsZero B hB).exists_zero
  exact ⟨Z, hZ, isBoundedBelow_of_isZero hZ, hZB⟩

/-- `derivedCategoryBPlus B` is stable under shift. -/
theorem derivedCategoryBPlus_isStableUnderShift
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun X hX => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  -- Strategy: split `hX : IsBoundedBelow X ∧ derivedCategoryB B X`; the first
  -- via `isBoundedBelow_shift`, the second via `derivedCategoryB_shift_mem`.
  exact ⟨isBoundedBelow_shift a hX.1, derivedCategoryB_shift_mem B hB a hX.2⟩

/-- `derivedCategoryBPlus B` is a triangulated subcategory. -/
theorem derivedCategoryBPlus_isTriangulated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).IsTriangulated := by
  have hz : (derivedCategoryBPlus B).ContainsZero := derivedCategoryBPlus_containsZero B hB
  have hs : (derivedCategoryBPlus B).IsStableUnderShift ℤ :=
      derivedCategoryBPlus_isStableUnderShift B hB
  have hcl : (derivedCategoryBPlus B).IsClosedUnderIsomorphisms :=
    derivedCategoryBPlus_isClosedUnderIsomorphisms B hB
  exact isTriangulated_of_mem_obj₂ _ fun T hT h₁ h₃ =>
    ⟨isBoundedBelow_mem_obj₂_of_distinguished T hT h₁.1 h₃.1,
      derivedCategoryB_mem_obj₂_of_distinguished B hB T hT h₁.2 h₃.2⟩

/-- `derivedCategoryBPlus B` is stable under retracts. -/
theorem derivedCategoryBPlus_isStableUnderRetracts
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).IsStableUnderRetracts := by
  refine ⟨fun {X Y} r hY => ⟨isBoundedBelow_of_retract r hY.1, ?_⟩⟩
  exact (derivedCategoryB_isStableUnderRetracts B hB).of_retract r hY.2

/-- `derivedCategoryBMinus B` is closed under isomorphisms. -/
theorem derivedCategoryBMinus_isClosedUnderIsomorphisms
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX => ⟨isBoundedAbove_of_iso e hX.1, ?_⟩⟩
  exact (derivedCategoryB_isClosedUnderIsomorphisms B hB).of_iso e hX.2

/-- `derivedCategoryBMinus B` contains a zero object. -/
theorem derivedCategoryBMinus_containsZero
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).ContainsZero := by
  obtain ⟨Z, hZ, hZB⟩ := (derivedCategoryB_containsZero B hB).exists_zero
  exact ⟨Z, hZ, isBoundedAbove_of_isZero hZ, hZB⟩

/-- `derivedCategoryBMinus B` is stable under shift. -/
theorem derivedCategoryBMinus_isStableUnderShift
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun X hX => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  exact ⟨isBoundedAbove_shift a hX.1, derivedCategoryB_shift_mem B hB a hX.2⟩

/-- `derivedCategoryBMinus B` is a triangulated subcategory. -/
@[sga "5 I App.1.2" "special case", sga "6 I 1.1.5" "partial"]
theorem derivedCategoryBMinus_isTriangulated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).IsTriangulated := by
  have hz : (derivedCategoryBMinus B).ContainsZero := derivedCategoryBMinus_containsZero B hB
  have hs : (derivedCategoryBMinus B).IsStableUnderShift ℤ :=
      derivedCategoryBMinus_isStableUnderShift B hB
  have hcl : (derivedCategoryBMinus B).IsClosedUnderIsomorphisms :=
    derivedCategoryBMinus_isClosedUnderIsomorphisms B hB
  exact isTriangulated_of_mem_obj₂ _ fun T hT h₁ h₃ =>
    ⟨isBoundedAbove_mem_obj₂_of_distinguished T hT h₁.1 h₃.1,
      derivedCategoryB_mem_obj₂_of_distinguished B hB T hT h₁.2 h₃.2⟩

/-- `derivedCategoryBMinus B` is stable under retracts. -/
theorem derivedCategoryBMinus_isStableUnderRetracts
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).IsStableUnderRetracts := by
  refine ⟨fun {X Y} r hY => ⟨isBoundedAbove_of_retract r hY.1, ?_⟩⟩
  exact (derivedCategoryB_isStableUnderRetracts B hB).of_retract r hY.2

/-- `derivedCategoryBBounded B` is closed under isomorphisms. -/
theorem derivedCategoryBBounded_isClosedUnderIsomorphisms
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX => ⟨isBounded_of_iso e hX.1, ?_⟩⟩
  exact (derivedCategoryB_isClosedUnderIsomorphisms B hB).of_iso e hX.2

/-- `derivedCategoryBBounded B` contains a zero object. -/
theorem derivedCategoryBBounded_containsZero
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).ContainsZero := by
  obtain ⟨Z, hZ, hZB⟩ := (derivedCategoryB_containsZero B hB).exists_zero
  exact ⟨Z, hZ, isBounded_of_isZero hZ, hZB⟩

/-- `derivedCategoryBBounded B` is stable under shift. -/
theorem derivedCategoryBBounded_isStableUnderShift
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun X hX => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  exact ⟨isBounded_shift a hX.1, derivedCategoryB_shift_mem B hB a hX.2⟩

/-- `derivedCategoryBBounded B` is a triangulated subcategory. -/
@[sga "6 I 1.1.5" "partial"]
theorem derivedCategoryBBounded_isTriangulated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).IsTriangulated := by
  have hz : (derivedCategoryBBounded B).ContainsZero := derivedCategoryBBounded_containsZero B hB
  have hs : (derivedCategoryBBounded B).IsStableUnderShift ℤ :=
      derivedCategoryBBounded_isStableUnderShift B hB
  have hcl : (derivedCategoryBBounded B).IsClosedUnderIsomorphisms :=
    derivedCategoryBBounded_isClosedUnderIsomorphisms B hB
  exact isTriangulated_of_mem_obj₂ _ fun T hT h₁ h₃ =>
    ⟨isBounded_mem_obj₂_of_distinguished T hT h₁.1 h₃.1,
      derivedCategoryB_mem_obj₂_of_distinguished B hB T hT h₁.2 h₃.2⟩

/-- `derivedCategoryBBounded B` is stable under retracts. -/
theorem derivedCategoryBBounded_isStableUnderRetracts
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).IsStableUnderRetracts := by
  refine ⟨fun {X Y} r hY => ⟨isBounded_of_retract r hY.1, ?_⟩⟩
  exact (derivedCategoryB_isStableUnderRetracts B hB).of_retract r hY.2

/-! ## Main Statements -/

/-- **Statement 1 (Stacks 06UQ, unbounded version).**
For a weak Serre subcategory `B ⊆ A`, the property `D_B(A)` is a strictly full,
saturated, triangulated subcategory of `D(A)`. -/
@[stacks 06UQ, sga "5 I App.1.2" "more general", sga "6 IV 1.6"]
theorem derivedCategoryB_isTriangulated_saturated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryB B).IsClosedUnderIsomorphisms ∧
      (derivedCategoryB B).IsTriangulated ∧
      (derivedCategoryB B).IsStableUnderRetracts :=
  ⟨derivedCategoryB_isClosedUnderIsomorphisms B hB,
   derivedCategoryB_isTriangulated B hB,
   derivedCategoryB_isStableUnderRetracts B hB⟩

/-- **Statement 2 (Stacks 06UQ, bounded version, bounded below).**
`D^+_B(A)` is a strictly full, saturated, triangulated subcategory of `D(A)`. -/
@[stacks 06UQ, sga "5 I App.1.2" "special case", sga "6 I 1.1.5" "partial"]
theorem derivedCategoryBPlus_isTriangulated_saturated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBPlus B).IsClosedUnderIsomorphisms ∧
      (derivedCategoryBPlus B).IsTriangulated ∧
      (derivedCategoryBPlus B).IsStableUnderRetracts :=
  ⟨derivedCategoryBPlus_isClosedUnderIsomorphisms B hB,
   derivedCategoryBPlus_isTriangulated B hB,
   derivedCategoryBPlus_isStableUnderRetracts B hB⟩

/-- **Statement 2 (Stacks 06UQ, bounded version, bounded above).**
`D^-_B(A)` is a strictly full, saturated, triangulated subcategory of `D(A)`. -/
@[stacks 06UQ, sga "6 I 1.1.5" "partial"]
theorem derivedCategoryBMinus_isTriangulated_saturated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBMinus B).IsClosedUnderIsomorphisms ∧
      (derivedCategoryBMinus B).IsTriangulated ∧
      (derivedCategoryBMinus B).IsStableUnderRetracts :=
  ⟨derivedCategoryBMinus_isClosedUnderIsomorphisms B hB,
   derivedCategoryBMinus_isTriangulated B hB,
   derivedCategoryBMinus_isStableUnderRetracts B hB⟩

/-- **Statement 2 (Stacks 06UQ, bounded version, bounded).**
`D^b_B(A)` is a strictly full, saturated, triangulated subcategory of `D(A)`. -/
@[stacks 06UQ, sga "6 I 1.1.5" "partial"]
theorem derivedCategoryBBounded_isTriangulated_saturated
    (B : ObjectProperty A) (hB : IsWeakSerre B) :
    (derivedCategoryBBounded B).IsClosedUnderIsomorphisms ∧
      (derivedCategoryBBounded B).IsTriangulated ∧
      (derivedCategoryBBounded B).IsStableUnderRetracts :=
  ⟨derivedCategoryBBounded_isClosedUnderIsomorphisms B hB,
   derivedCategoryBBounded_isTriangulated B hB,
   derivedCategoryBBounded_isStableUnderRetracts B hB⟩

end DerivedCategoryB

end

end
