module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel

/-!
# First lemmas on pseudo-coherent complexes on a ringed space

`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean` defines `m`-pseudo-coherence and
pseudo-coherence of a complex of `𝒪_X`-modules and of an object of the derived category
(Stacks 08CB), but proves nothing about them. This file is the start of that theory: the lemmas
below are the ones whose proofs are immediate from the definition, and they are the facts the
genuine content of the section — the two-out-of-three property in a distinguished triangle
(Stacks 08CD) and finite-typeness of the top cohomology sheaf (Stacks 08DN) — is phrased in terms
of.

## Main results

* `AlgebraicGeometry.RingedSpace.isStrictlyPerfect_restrictComplex`: the restriction of a strictly
  perfect complex to an open subspace is strictly perfect.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplex_of_isStrictlyPerfect` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_Q_obj_of_isStrictlyPerfect`: a strictly perfect
  complex is pseudo-coherent, as a complex and as an object of the derived category.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom.mono` and
  `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.mono`: `m`-pseudo-coherence is monotone in
  `m` — a weaker approximation is asked for as `m` grows.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_isZero`: a zero object of the derived category
  is pseudo-coherent.
* `CategoryTheory.Functor.retractMapBiproduct`: for an *additive* functor `F`, the object
  `F(⨁ f)` is a retract of `⨁ F(f)` — no preservation of biproducts needed.

## Implementation notes

That restriction preserves strict perfection is the one lemma here with content, and the shape of
its proof is worth recording. Strict perfection of a complex asks each term to be a retract of a
finite free module `𝒪_X^{⊕n}` (`StrictlyPerfect.IsDirectSummandOfFiniteFree`). Restriction sends
`𝒪_X` to `𝒪_U` *definitionally* — the morphism of sheaves of rings that
`AlgebraicGeometry.RingedSpace.restrictModules` pushes forward along is the identity — so the only
question is what it does to a finite biproduct. One does not need it to *preserve* the biproduct:
for any additive functor `F` the two comparison morphisms satisfy
`biproductComparison ≫ biproductComparison' = 𝟙`, because the composite is
`∑ j, F(π j) ≫ F(ι j) = F(∑ j, π j ≫ ι j) = F(𝟙)`. That exhibits `F(⨁ f)` as a retract of
`⨁ F(f)`, which composes with the given retract and is all that strict perfection needs. This
avoids the preservation-of-limits route, which for `SheafOfModules.pushforward` goes through
`SheafOfModules.pullbackPushforwardAdjunction` and is expensive to elaborate.

Additivity of `AlgebraicGeometry.RingedSpace.restrictModules` itself is immediate: restriction
does not change sections, so it does not change the sum of two morphisms.

Monotonicity in `m` is the one direction that holds: being `m`-pseudo-coherent asks for an
isomorphism on cohomology in degrees above `m` and an epimorphism in degree `m`, and both clauses
weaken as `m` grows, the degree-`m'` epimorphism for `m < m'` being supplied by the isomorphism
there.

## References

* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 20.46.1 (08C4)](https://stacks.math.columbia.edu/tag/08C4)
* [The Stacks Project, Lemma 20.46.5 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [The Stacks Project, Lemma 20.46.6 (08CD)](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- For an additive functor `F` and a finite family `f`, the object `F(⨁ f)` is a retract of
`⨁ F(f)`: the two biproduct comparison morphisms compose to the identity on `F(⨁ f)`, since
`∑ j, F(π j) ≫ F(ι j) = F(∑ j, π j ≫ ι j) = F(𝟙)`.

This is weaker than preservation of the biproduct, which would make the comparison an
isomorphism, but it is enough to transport "is a direct summand of a finite free module". -/
public def retractMapBiproduct [Preadditive C] [Preadditive D] {J : Type} [Fintype J]
    (F : C ⥤ D) [F.Additive] (f : J → C) [HasBiproduct f] [HasBiproduct (F.obj ∘ f)] :
    Retract (F.obj (⨁ f)) (⨁ F.obj ∘ f) where
  i := F.biproductComparison f
  r := F.biproductComparison' f
  retract := by
    rw [CategoryTheory.Functor.biproductComparison, CategoryTheory.Functor.biproductComparison',
      biproduct.lift_desc,
      show (∑ j : J, F.map (biproduct.π f j) ≫ F.map (biproduct.ι f j)) =
        ∑ j : J, F.map (biproduct.π f j ≫ biproduct.ι f j) from
          Finset.sum_congr rfl fun j _ => (F.map_comp _ _).symm,
      ← F.map_sum, biproduct.total, CategoryTheory.Functor.map_id]

/-- A functor preserving zero morphisms sends a zero object to a zero object: an object is zero
exactly when its identity is the zero morphism, and that is preserved. -/
public theorem isZero_obj [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {A : C} (h : IsZero A) : IsZero (F.obj A) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [← F.map_id, h, F.map_zero]

end CategoryTheory.Functor

namespace StrictlyPerfect

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- A complex of `𝒪_X`-modules all of whose terms are zero is strictly perfect: the set of
degrees where it is nonzero is empty, and a zero module is a direct summand of a finite free
module. -/
public theorem isStrictlyPerfect_of_forall_isZero
    {E : CochainComplex (OXMod.{u, u} X) ℤ} (h : ∀ i, IsZero (E.X i)) : IsStrictlyPerfect E where
  bounded := by
    convert Set.finite_empty
    exact Set.eq_empty_iff_forall_notMem.2 fun i hi => hi (h i)
  directSummand i := isDirectSummandOfFiniteFree_of_isZero (h i)

end StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- Restriction of sheaves of modules to an open subspace is additive: it does not change the
sections of a morphism, hence not the sum of two morphisms. -/
public instance restrictModules_additive (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (restrictModules X U).Additive where
  map_add := by intros; ext _ _; rfl

/-- Restriction to an open subspace preserves "is a direct summand of a finite free module":
the given retract of `𝒪_X^{⊕n}` maps to a retract of the restriction of `𝒪_X^{⊕n}`, which is in
turn a retract of `𝒪_U^{⊕n}` because restriction is additive and sends `𝒪_X` to `𝒪_U`. -/
public theorem isDirectSummandOfFiniteFree_restrictModules (U : Opens X.carrier)
    {A : StrictlyPerfect.OXMod.{u, u} X}
    (h : StrictlyPerfect.IsDirectSummandOfFiniteFree A) :
    StrictlyPerfect.IsDirectSummandOfFiniteFree ((restrictModules X U).obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := h
  exact ⟨n, ⟨(ρ.map (restrictModules X U)).trans
    (((restrictModules X U).retractMapBiproduct
        fun _ : Fin n => StrictlyPerfect.structureModule X).map
      (StrictlyPerfect.moduleULift (X.restrict U.isOpenEmbedding)))⟩⟩

/-- The restriction of a strictly perfect complex of `𝒪_X`-modules to an open subspace is
strictly perfect: restriction sends a zero term to a zero term, so the complex stays bounded, and
it preserves being a direct summand of a finite free module. -/
public theorem isStrictlyPerfect_restrictComplex
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect E) (U : Opens X.carrier) :
    StrictlyPerfect.IsStrictlyPerfect (restrictComplex E U) where
  bounded := h.bounded.subset fun _ hi hz => hi ((restrictModules X U).isZero_obj hz)
  directSummand i := isDirectSummandOfFiniteFree_restrictModules U (h.directSummand i)

/-- A strictly perfect complex of `𝒪_X`-modules is `m`-pseudo-coherent for every `m`: it is its
own strictly perfect approximation on all of `X`, the approximating morphism being the identity. -/
public theorem isPseudoCoherentComplexFrom_of_isStrictlyPerfect
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect E) (m : ℤ) : IsPseudoCoherentComplexFrom E m :=
  fun _ => ⟨⊤, trivial, restrictComplex E ⊤, isStrictlyPerfect_restrictComplex h ⊤, 𝟙 _,
    fun _ _ => by rw [HomologicalComplex.homologyMap_id]; infer_instance,
    by rw [HomologicalComplex.homologyMap_id]; infer_instance⟩

/-- A strictly perfect complex of `𝒪_X`-modules is pseudo-coherent. -/
public theorem isPseudoCoherentComplex_of_isStrictlyPerfect
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect E) : IsPseudoCoherentComplex E :=
  fun m => isPseudoCoherentComplexFrom_of_isStrictlyPerfect h m

/-- The object of the derived category of `𝒪_X`-modules represented by a strictly perfect complex
is pseudo-coherent. -/
public theorem isPseudoCoherent_Q_obj_of_isStrictlyPerfect
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect P) : IsPseudoCoherent (DerivedCategory.Q.obj P) :=
  ⟨P, isPseudoCoherentComplex_of_isStrictlyPerfect h, ⟨Iso.refl _⟩⟩

open scoped ZeroObject in
/-- A zero object of the derived category of `𝒪_X`-modules is pseudo-coherent: it is represented
by the complex with zero terms, which is strictly perfect. -/
public theorem isPseudoCoherent_of_isZero
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} (h : IsZero E) : IsPseudoCoherent E :=
  ⟨0, isPseudoCoherentComplex_of_isStrictlyPerfect
      (StrictlyPerfect.isStrictlyPerfect_of_forall_isZero fun i =>
        (HomologicalComplex.eval _ _ i).isZero_obj (isZero_zero _)),
    ⟨(DerivedCategory.Q.isZero_obj (isZero_zero _)).iso h⟩⟩

/-- `m`-pseudo-coherence of a complex of `𝒪_X`-modules is monotone in `m`: a strictly perfect
approximation which is an isomorphism on cohomology above `m` and an epimorphism in degree `m` is
an isomorphism above any `m' ≥ m`, and in degree `m'` it is an epimorphism — by hypothesis when
`m' = m`, and because it is then an isomorphism when `m' > m`. -/
public theorem IsPseudoCoherentComplexFrom.mono
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} {m m' : ℤ}
    (h : IsPseudoCoherentComplexFrom E m) (hm : m ≤ m') : IsPseudoCoherentComplexFrom E m' := by
  intro x
  obtain ⟨U, hxU, P, hP, α, hiso, hepi⟩ := h x
  refine ⟨U, hxU, P, hP, α, fun j hj => hiso j (lt_of_le_of_lt hm hj), ?_⟩
  rcases eq_or_lt_of_le hm with rfl | hlt
  · exact hepi
  · have := hiso m' hlt
    infer_instance

/-- `m`-pseudo-coherence of an object of the derived category of `𝒪_X`-modules is monotone
in `m`. -/
public theorem IsPseudoCoherentFrom.mono
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} {m m' : ℤ}
    (h : IsPseudoCoherentFrom E m) (hm : m ≤ m') : IsPseudoCoherentFrom E m' := by
  obtain ⟨K, hK, e⟩ := h
  exact ⟨K, hK.mono hm, e⟩

/-- A pseudo-coherent complex of `𝒪_X`-modules is `m`-pseudo-coherent for every `m`. -/
public theorem IsPseudoCoherentComplex.isPseudoCoherentComplexFrom
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (h : IsPseudoCoherentComplex E)
    (m : ℤ) : IsPseudoCoherentComplexFrom E m := h m

/-- A pseudo-coherent object of the derived category of `𝒪_X`-modules is `m`-pseudo-coherent for
every `m`: the single pseudo-coherent complex representing it is in particular
`m`-pseudo-coherent. -/
public theorem IsPseudoCoherent.isPseudoCoherentFrom
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} (h : IsPseudoCoherent E) (m : ℤ) :
    IsPseudoCoherentFrom E m := by
  obtain ⟨K, hK, e⟩ := h
  exact ⟨K, hK m, e⟩

end AlgebraicGeometry.RingedSpace

end
