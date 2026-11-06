module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedAdjunctionUnitFullyFaithful
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exact functors inducing equivalences of bounded below derived categories

Let `L : 𝒜 ⥤ ℬ` be an exact functor between abelian categories with enough injectives, and let
`P` and `Q` be classes of objects of `𝒜` and `ℬ` with `L(P) ⊆ Q`. Then `L` applied degreewise
carries `D⁺_P(𝒜)`, the bounded below objects of `D(𝒜)` all of whose cohomology objects lie in `P`,
into `D⁺_Q(ℬ)` ([Stacks, Tag 06UP]).

Suppose that `L` has a right adjoint `R`, that the unit `𝟭 ⟶ R ∘ L` is an isomorphism, and that
`L` carries injective objects to objects right acyclic for `R`. Then `L` is fully faithful on
`D⁺(𝒜)` (the argument of [Stacks, Tag 099V]). If moreover every object of `Q` is isomorphic to
`L(M)` for some `M` in `P`, then `L : D⁺_P(𝒜) ⥤ D⁺_Q(ℬ)` is an equivalence: for `K` in
`D⁺_Q(ℬ)` the counit `L(Rℛ K) ⟶ K` of the derived adjunction is invertible, since it is so on the
cohomology objects of `K` placed in degree zero, these being of the form `L(M)`, and the dévissage
along the truncation triangles of `D⁺(ℬ)` passes from them to `K`. This is the formal content of
the proofs of [Stacks, Tag 099Z] and [Stacks, Tag 09AL].

## Main definitions

* `DerivedCategoryB.mapDerivedCategoryBPlus`: the functor `D⁺_P(𝒜) ⥤ D⁺_Q(ℬ)` induced by an exact
  functor `L` with `L(P) ⊆ Q`.

## Main results

* `DerivedCategoryB.derivedCategoryBPlus_mapDerivedCategory_obj`: an exact functor with
  `L(P) ⊆ Q` carries `D⁺_P(𝒜)` into `D⁺_Q(ℬ)`.
* `DerivedCategoryB.isEquivalence_mapDerivedCategoryBPlus`: **the theorem**, that the induced
  functor is an equivalence under the hypotheses above.
* `DerivedCategoryB.derivedCategoryBPlus_essImage_iff`: under the same hypotheses on `L ⊣ R`,
  an object of `D(ℬ)` is bounded below with cohomology objects in the essential image of `L`
  exactly when it is bounded below and isomorphic to `L(M)` for some `M` in `D(𝒜)`.

## Implementation notes

The right adjoint of `L.mapDerivedCategoryPlus` used in the proof is the right derived functor of
`R` on `D⁺(ℬ)`, with the commutation with the shift induced from the one of
`L.mapDerivedCategoryPlus` through the adjunction; this makes the counit compatible with the
shift, as the dévissage `DerivedCategory.Plus.isIso_app_of_bounded_below` requires. The quasi
inverse is therefore not part of the statement, which is about the functor induced by `L`.

## References

* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
* [Stacks Project, Tag 099Z](https://stacks.math.columbia.edu/tag/099Z)
* [Stacks Project, Tag 09AL](https://stacks.math.columbia.edu/tag/09AL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory

universe v u v' u'

namespace CategoryTheory.Functor

/-- The right derived functor `D⁺(𝒜) ⥤ D⁺(ℬ)` of an additive functor out of an abelian category
with enough injectives exists, with unit `Functor.rightDerivedFunctorPlusUnith`. Instance search
finds this from the injective derivability structure only after many steps; registering it as a
local instance is a shortcut. -/
@[ega "0 13.6.1" "more general"]
theorem hasRightDerivedFunctor_mapHomotopyCategoryPlus_of_enoughInjectives {A B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory A]
    [HasDerivedCategory B] [EnoughInjectives A] (G : A ⥤ B) [G.Additive] :
    (G.mapHomotopyCategoryPlus ⋙ Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
  HasRightDerivedFunctor.mk' (RF := G.rightDerivedFunctorPlus)
    (α := G.rightDerivedFunctorPlusUnith)

end CategoryTheory.Functor

attribute [local instance]
  Functor.hasRightDerivedFunctor_mapHomotopyCategoryPlus_of_enoughInjectives

namespace DerivedCategoryB

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
  (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (P : ObjectProperty A) (Q : ObjectProperty B) [Q.IsClosedUnderIsomorphisms]
  (hPQ : ∀ M : A, P M → Q (L.obj M))

include hPQ in
/-- **An exact functor with `L(P) ⊆ Q` carries `D⁺_P(𝒜)` into `D⁺_Q(ℬ)`**: it commutes with
cohomology. -/
theorem derivedCategoryBPlus_mapDerivedCategory_obj (X : DerivedCategory A)
    (hX : derivedCategoryBPlus P X) :
    derivedCategoryBPlus Q (L.mapDerivedCategory.obj X) := by
  obtain ⟨n, hn⟩ := (isBoundedBelow_iff_exists_isGE X).1 hX.1
  exact ⟨(isBoundedBelow_iff_exists_isGE _).2 ⟨n, L.isGE_obj_mapDerivedCategory X n hn⟩,
    fun q ↦ Q.prop_of_iso ((L.mapDerivedCategoryHomologyIso q).app X).symm (hPQ _ (hX.2 q))⟩

/-- **The functor `D⁺_P(𝒜) ⥤ D⁺_Q(ℬ)` induced by an exact functor `L` with `L(P) ⊆ Q`**: `L`
applied degreewise to complexes. -/
def mapDerivedCategoryBPlus :
    (derivedCategoryBPlus P).FullSubcategory ⥤ (derivedCategoryBPlus Q).FullSubcategory :=
  (derivedCategoryBPlus Q).lift ((derivedCategoryBPlus P).ι ⋙ L.mapDerivedCategory)
    fun X ↦ derivedCategoryBPlus_mapDerivedCategory_obj L P Q hPQ X.1 X.2

/-- The functor induced on `D⁺_P(𝒜)`, followed by the inclusion of `D⁺_Q(ℬ)`, is the inclusion
of `D⁺_P(𝒜)` followed by `L` applied degreewise. -/
theorem mapDerivedCategoryBPlus_comp_ι :
    mapDerivedCategoryBPlus L P Q hPQ ⋙ (derivedCategoryBPlus Q).ι =
      (derivedCategoryBPlus P).ι ⋙ L.mapDerivedCategory :=
  rfl

omit [Q.IsClosedUnderIsomorphisms] in
/-- **The cohomology objects of `L(M)` lie in the essential image of `L`**, for every object `M`
of `D(𝒜)`: `L` commutes with cohomology. -/
theorem derivedCategoryB_essImage_of_essImage_mapDerivedCategory {X : DerivedCategory B}
    (hX : L.mapDerivedCategory.essImage X) : derivedCategoryB L.essImage X := by
  obtain ⟨M, ⟨e⟩⟩ := hX
  exact fun q ↦ ⟨_, ⟨((L.mapDerivedCategoryHomologyIso q).app M).symm ≪≫
    (homologyFunctor B q).mapIso e⟩⟩

omit [HasDerivedCategory A] in
/-- An object of `D⁺_P(𝒜)` read as an object of `D⁺(𝒜)`. -/
def toPlus [HasDerivedCategory A] (P : ObjectProperty A) :
    (derivedCategoryBPlus P).FullSubcategory ⥤ Plus A :=
  ObjectProperty.lift _ (derivedCategoryBPlus P).ι fun X ↦
    (isBoundedBelow_iff_exists_isGE X.1).1 X.2.1

omit [HasDerivedCategory A] in
/-- `D⁺_P(𝒜)` is a full subcategory of `D⁺(𝒜)`. -/
def fullyFaithfulToPlus [HasDerivedCategory A] (P : ObjectProperty A) :
    (toPlus P).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := Plus.ι) (derivedCategoryBPlus P).fullyFaithfulι

variable [EnoughInjectives A] [EnoughInjectives B] {R : B ⥤ A} [R.Additive]

variable (adj : L ⊣ R) [IsIso adj.unit] (hR : ∀ I : A, Injective I → R.rightAcyclic (L.obj I))

include adj hR in
/-- **`L` is fully faithful on `D⁺(𝒜)`** when the unit of `L ⊣ R` is invertible and `L` carries
injective objects to objects right acyclic for `R`. -/
def fullyFaithfulMapDerivedCategoryPlus : L.mapDerivedCategoryPlus.FullyFaithful :=
  have : L.PreservesHomology := Functor.preservesHomologyOfExact L
  have := adj.isIso_rightDerivedFunctorPlus_unit hR
  adj.rightDerivedFunctorPlus.fullyFaithfulLOfIsIsoUnit.ofIso
    (L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus)

include adj hR in
/-- The functor induced on `D⁺_P(𝒜)` is fully faithful. -/
def fullyFaithfulMapDerivedCategoryBPlus :
    (mapDerivedCategoryBPlus L P Q hPQ).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (derivedCategoryBPlus Q).ι)
    (((fullyFaithfulToPlus P).comp (fullyFaithfulMapDerivedCategoryPlus L adj hR)).comp
      TStructure.t.plus.fullyFaithfulι)

omit [Q.IsClosedUnderIsomorphisms] in
include adj hR in
/-- **The counit of the derived adjunction is invertible on `D⁺_Q(ℬ)`.** Let `G` be a right
adjoint of `L.mapDerivedCategoryPlus`. If every object of `Q` is isomorphic to `L(M)` for some
`M`, then the counit `L(G K) ⟶ K` is invertible at every `K` in `D⁺(ℬ)` whose cohomology
objects lie in `Q`: it is invertible on objects of the essential image of the fully faithful
`L.mapDerivedCategoryPlus`, among which are the cohomology objects of `K` in degree zero, and
the dévissage along truncations passes to `K`. -/
theorem isIso_counit_app_of_cohomology {G : Plus B ⥤ Plus A}
    (adj' : L.mapDerivedCategoryPlus ⊣ G) [G.CommShift ℤ] [adj'.CommShift ℤ]
    (hG : ∀ (K : Plus B) (m : ℤ), K.IsGE m → (G.obj K).IsGE m)
    (hess : ∀ N : B, Q N → ∃ M : A, Nonempty (L.obj M ≅ N))
    (K : Plus B) (hK : ∀ q : ℤ, Q ((Plus.homologyFunctor B q).obj K)) :
    IsIso (adj'.counit.app K) := by
  have hff := fullyFaithfulMapDerivedCategoryPlus L adj hR
  have := hff.full
  have := hff.faithful
  have : G.IsTriangulated := adj'.isTriangulated_rightAdjoint
  obtain ⟨a, ha⟩ := K.2
  refine Plus.isIso_app_of_bounded_below adj'.counit
    (fun M m hM ↦ L.isGE_mapDerivedCategoryPlus_obj _ m (hG M m hM)) (fun M m hM ↦ hM) K a
    ((Plus.isGE_ι_obj_iff K a).1 ha) fun q ↦ ?_
  obtain ⟨M, ⟨e⟩⟩ := hess _ (hK q)
  rw [adj'.isIso_counit_app_iff_mem_essImage]
  exact ⟨(Plus.singleFunctor A 0).obj M, ⟨(TStructure.t.plus.fullyFaithfulι.preimageIso
    (X := L.mapDerivedCategoryPlus.obj ((Plus.singleFunctor A 0).obj M))
    (Y := (Plus.singleFunctor B 0).obj (L.obj M))
    ((L.mapDerivedCategorySingleFunctor 0).app M)) ≪≫ (Plus.singleFunctor B 0).mapIso e⟩⟩

include adj hR in
/-- **An exact functor inducing an equivalence `D⁺_P(𝒜) ≌ D⁺_Q(ℬ)`** ([Stacks, Tag 099Z],
[Stacks, Tag 09AL] in general form). Let `L : 𝒜 ⥤ ℬ` be exact with right adjoint `R`, such that
the unit `𝟭 ⟶ R ∘ L` is an isomorphism and `L` carries injective objects to objects right acyclic
for `R`. Let `P` and `Q` be classes of objects closed under isomorphism with `L(P) ⊆ Q`, such that
every object of `Q` is isomorphic to `L(M)` for some `M` in `P`. Then `L`, applied degreewise,
is an equivalence from the bounded below objects of `D(𝒜)` with cohomology in `P` to the bounded
below objects of `D(ℬ)` with cohomology in `Q`. -/
theorem isEquivalence_mapDerivedCategoryBPlus [P.IsClosedUnderIsomorphisms]
    (hess : ∀ N : B, Q N → ∃ M : A, P M ∧ Nonempty (L.obj M ≅ N)) :
    (mapDerivedCategoryBPlus L P Q hPQ).IsEquivalence := by
  have hFF := fullyFaithfulMapDerivedCategoryBPlus L P Q hPQ adj hR
  have : L.PreservesHomology := Functor.preservesHomologyOfExact L
  let adj' : L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
    adj.rightDerivedFunctorPlus.ofNatIsoLeft L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
  let : R.rightDerivedFunctorPlus.CommShift ℤ := adj'.rightAdjointCommShift ℤ
  have : adj'.CommShift ℤ := adj'.commShift_of_leftAdjoint ℤ
  have : (mapDerivedCategoryBPlus L P Q hPQ).EssSurj := ⟨fun Y ↦ by
    let K : Plus B := (toPlus Q).obj Y
    have : IsIso (adj'.counit.app K) :=
      isIso_counit_app_of_cohomology L Q adj hR adj'
        (fun K m _ ↦ R.isGE_rightDerivedFunctorPlus_obj K m)
        (fun N hN ↦ (hess N hN).imp fun _ h ↦ h.2) K Y.2.2
    let X : Plus A := R.rightDerivedFunctorPlus.obj K
    have hX : derivedCategoryBPlus P (Plus.ι.obj X) := by
      obtain ⟨n, hn⟩ := X.2
      refine ⟨(isBoundedBelow_iff_exists_isGE _).2 ⟨n, hn⟩, fun q ↦ ?_⟩
      obtain ⟨M, hM, ⟨e⟩⟩ := hess _ (Y.2.2 q)
      let e' : L.obj ((homologyFunctor A q).obj (Plus.ι.obj X)) ≅
          (homologyFunctor B q).obj Y.1 :=
        ((L.mapDerivedCategoryHomologyIso q).app (Plus.ι.obj X)).symm ≪≫
          (homologyFunctor B q).mapIso (Plus.ι.mapIso (asIso (adj'.counit.app K)))
      exact P.prop_of_iso (adj.fullyFaithfulLOfIsIsoUnit.preimageIso (e ≪≫ e'.symm)) hM
    exact ⟨⟨Plus.ι.obj X, hX⟩, ⟨(derivedCategoryBPlus Q).fullyFaithfulι.preimageIso
      (Plus.ι.mapIso (asIso (adj'.counit.app K)))⟩⟩⟩
  have := hFF.full
  have := hFF.faithful
  exact { }

/-- The bounded below objects of `D(ℬ)` whose cohomology objects lie in the essential image of
`L`, as a property of objects of `D⁺(ℬ)`. -/
abbrev plusEssImage : ObjectProperty (Plus B) :=
  (derivedCategoryBPlus L.essImage).inverseImage Plus.ι

omit [EnoughInjectives A] [EnoughInjectives B] [R.Additive] in
/-- `L` applied termwise carries `D⁺(𝒜)` into `D⁺_{L(𝒜)}(ℬ)`. -/
theorem plusEssImage_mapDerivedCategoryPlus_obj (K : Plus A) :
    plusEssImage L (L.mapDerivedCategoryPlus.obj K) := by
  obtain ⟨n, hn⟩ := K.2
  exact derivedCategoryBPlus_mapDerivedCategory_obj L ⊤ L.essImage
    (fun M _ ↦ L.obj_mem_essImage M) (Plus.ι.obj K)
    ⟨(isBoundedBelow_iff_exists_isGE _).2 ⟨n, hn⟩, fun _ ↦ trivial⟩

/-- **The equivalence `D⁺(𝒜) ≌ D⁺_{L(𝒜)}(ℬ)` with quasi-inverse `RR`** ([Stacks, Tag 09B1] (2)
in general form). Let `L ⊣ R` be an adjunction with `L` exact, invertible unit, and `L` carrying
injective objects to objects right acyclic for `R`. Then `L` applied termwise is an equivalence
from `D⁺(𝒜)` to the bounded below objects of `D(ℬ)` whose cohomology objects lie in the
essential image of `L`, with quasi-inverse the right derived functor of `R`: the unit of the
derived adjunction is invertible, and so is its counit on these objects. -/
def plusEquivalenceEssImage : Plus A ≌ (plusEssImage L).FullSubcategory :=
  have : L.PreservesHomology := Functor.preservesHomologyOfExact L
  let adj' : L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
    adj.rightDerivedFunctorPlus.ofNatIsoLeft L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
  letI : R.rightDerivedFunctorPlus.CommShift ℤ := adj'.rightAdjointCommShift ℤ
  have : adj'.CommShift ℤ := adj'.commShift_of_leftAdjoint ℤ
  have hff := fullyFaithfulMapDerivedCategoryPlus L adj hR
  have : L.mapDerivedCategoryPlus.Full := hff.full
  have : L.mapDerivedCategoryPlus.Faithful := hff.faithful
  have hc : ∀ K : (plusEssImage L).FullSubcategory, IsIso (adj'.counit.app K.1) := fun K ↦
    isIso_counit_app_of_cohomology L L.essImage adj hR adj'
      (fun K m _ ↦ R.isGE_rightDerivedFunctorPlus_obj K m) (fun _ h ↦ h) K.1 K.2.2
  CategoryTheory.Equivalence.mk
    ((plusEssImage L).lift L.mapDerivedCategoryPlus (plusEssImage_mapDerivedCategoryPlus_obj L))
    ((plusEssImage L).ι ⋙ R.rightDerivedFunctorPlus)
    (asIso adj'.unit)
    (NatIso.ofComponents (fun K ↦ (plusEssImage L).fullyFaithfulι.preimageIso
      (@asIso _ _ _ _ (adj'.counit.app K.1) (hc K)))
      fun f ↦ (plusEssImage L).fullyFaithfulι.map_injective (adj'.counit.naturality f.hom))

/-- The functor of `plusEquivalenceEssImage` is `L` applied termwise. -/
theorem plusEquivalenceEssImage_functor_comp_ι :
    (plusEquivalenceEssImage L adj hR).functor ⋙ (plusEssImage L).ι = L.mapDerivedCategoryPlus :=
  rfl

/-- The quasi-inverse of `plusEquivalenceEssImage` is the right derived functor of `R`. -/
theorem plusEquivalenceEssImage_inverse :
    (plusEquivalenceEssImage L adj hR).inverse =
      (plusEssImage L).ι ⋙ R.rightDerivedFunctorPlus :=
  rfl

include adj hR in
/-- **The bounded below objects of `D(ℬ)` with cohomology in the essential image of `L` are the
bounded below objects of the essential image of `L` on derived categories**, when `L` is exact
with a right adjoint `R`, the unit of `L ⊣ R` is invertible and `L` carries injective objects to
objects right acyclic for `R`: an object of `D⁺_{L(𝒜)}(ℬ)` is `L` of its image under `RR`. -/
theorem derivedCategoryBPlus_essImage_iff (X : DerivedCategory B) :
    derivedCategoryBPlus L.essImage X ↔
      IsBoundedBelow X ∧ L.mapDerivedCategory.essImage X := by
  refine ⟨fun hX ↦ ⟨hX.1, ?_⟩, fun hX ↦
    ⟨hX.1, derivedCategoryB_essImage_of_essImage_mapDerivedCategory L hX.2⟩⟩
  let Y : (plusEssImage L).FullSubcategory :=
    ⟨⟨X, (isBoundedBelow_iff_exists_isGE X).1 hX.1⟩, hX⟩
  let e := plusEquivalenceEssImage L adj hR
  exact ⟨Plus.ι.obj (e.inverse.obj Y),
    ⟨Plus.ι.mapIso ((plusEssImage L).ι.mapIso (e.counitIso.app Y))⟩⟩

end DerivedCategoryB

end
