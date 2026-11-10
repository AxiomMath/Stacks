module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Order.Int.ConditionallyCompleteOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hom complex computes derived `Hom`

Let `C` be a preadditive category and let `L`, `M` be cochain complexes in `C` indexed by `ℤ`.
The degree-`n` cohomology of the Hom complex `Hom^•(L, M)` is canonically identified with the
morphisms `L ⟶ M⟦n⟧` in the homotopy category `K(C)`. Passing to the derived category, the
resulting comparison `Hⁿ(Hom^•(L, M)) → Hom_{D(C)}(L, M⟦n⟧)` is bijective as soon as one of the
two arguments is adapted to the localization: it suffices that `L` be a bounded above complex of
projectives, or that `M` be K-injective. In either case `Hom^•(L, M)` represents `RHom(L, M)`.

Representability is not merely a counting statement: the identification is additive, it is
natural in both variables, and it is compatible with the computation of `RHom` through a
K-injective resolution of the second variable. All three are recorded here.

## Main definitions

* `homComplexHomologyAddEquiv`: the canonical additive equivalence
  `Hⁿ(Hom^•(L, M)) ≃+ Hom_{K(C)}(L, M⟦n⟧)` ([stacks 0A5X]).
* `cohomologyClassPrecomp`, `cohomologyClassPostcomp`: the maps induced on cohomology classes of
  the Hom complex by a morphism in the first (contravariantly) and second (covariantly) variable.
* `qhMapAddEquivOfBijective`: an additive equivalence packaging a bijective instance of the
  localization map `Hom_{K(C)}(X, Y) → Hom_{D(C)}(X, Y)`.
* `cohomologyClassRHomAddEquivOfIsKInjective`: for `I` K-injective, the comparison isomorphism
  `CohomologyClass L I n ≃+ Hom_{D(C)}(L, I⟦n⟧)` underlying [stacks 0A64].
* `cohomologyClassRHomAddEquiv`: for `P` a bounded above complex of projective `R`-modules, the
  comparison isomorphism `CohomologyClass P L n ≃+ Hom_{D(R)}(P, L⟦n⟧)` ([stacks 0A66]).
* `homComplexHomologyRHomAddEquiv`: the same isomorphism read on the homology of the Hom complex,
  `Hⁿ(Hom^•(P, L)) ≃+ Hom_{D(R)}(P, L⟦n⟧)` ([stacks 0A66]).

## Main results

* `homComplex_of_isKInjective_represents_RHom`: for `I` K-injective, the map
  `Hⁿ(Hom^•(L, I)) → Hom_{D(C)}(L, I⟦n⟧)` is bijective for every `n` ([stacks 0A64]); a corollary
  of `cohomologyClassRHomAddEquivOfIsKInjective`.
* `cohomologyClassRHomAddEquiv_naturality_left` and
  `cohomologyClassRHomAddEquiv_naturality_right`: the comparison isomorphism of [stacks 0A66] is
  natural in both variables — contravariantly in `P`, covariantly in `L`.
* `homComplexRHom_isKInjective_model_comm` and `homComplexRHom_eq_isKInjective_model_route`: the
  comparison of [stacks 0A66] agrees with the comparison of [stacks 0A64] along a K-injective
  model `L ⟶ I`, and is computed by it.
* `homComplex_represents_RHom`: the underlying pointwise statement of [stacks 0A66], that the
  map `Hⁿ(Hom^•(P, L)) → Hom_{D(R)}(P, L⟦n⟧)` is bijective for every `n`; a corollary of the
  bundled isomorphism.

## Implementation notes

Cohomology classes of the Hom complex are represented by
`CochainComplex.HomComplex.CohomologyClass`, which Mathlib builds as a quotient of cocycles rather
than through the homology API; `CochainComplex.HomComplex.homologyAddEquiv` converts between the
two presentations, so every statement below can be read either way.

The displayed equality of [stacks 0A66] is *an isomorphism of abelian groups*, and the faithful
Lean reading of "the Hom complex represents `RHom`" is a bundled `≃+` together with its
naturality, not the bare predicate `Function.Bijective`. A bijectivity predicate forgets the
additivity, forgets which map is being compared, and — decisively — cannot be asked to commute
with anything, so it cannot express that the comparison is a morphism of functors or that it
reconciles with the K-injective route of [stacks 0A64]. Hence `cohomologyClassRHomAddEquiv` is the
primary form here and `homComplex_represents_RHom` is derived from it by `AddEquiv.bijective`.

Naturality is stated pointwise (`∀ c, ...`) rather than as an equality of functors: Mathlib does
not provide `CochainComplex.HomComplex.CohomologyClass` as a bifunctor, so the induced maps
`cohomologyClassPrecomp` and `cohomologyClassPostcomp` are constructed here out of
`CochainComplex.HomComplex.Cocycle.precomp` and `.postcomp` by descent along
`CohomologyClass.descAddMonoidHom`. Their naturality against
`CochainComplex.HomComplex.CohomologyClass.toHom` holds already in the homotopy category and for
an arbitrary preadditive `C` (`toHom_cohomologyClassPrecomp`, `toHom_cohomologyClassPostcomp`);
the derived-category statements are obtained from those by applying `DerivedCategory.Qh`.

Neither naturality statement needs `P'` or `L'` to be adapted to the localization for the square
to commute; the hypotheses making `P'` bounded above with projective terms are present only so
that the source of the square is itself a comparison *isomorphism*. For the same reason
`homComplexRHom_isKInjective_model_comm` is stated without a quasi-isomorphism hypothesis on
`L ⟶ I`, which is needed only for the factorization
`homComplexRHom_eq_isKInjective_model_route`; there it supplies the invertibility of the bottom
edge, via the instance `isIso_Qh_map_quotient_map_of_quasiIso`.

Both compatibility statements name the [stacks 0A64] comparison in its bundled form
`cohomologyClassRHomAddEquivOfIsKInjective`, so the reconciliation square really has a comparison
isomorphism on each of its vertical edges.

[stacks 0A5X] needs no abelian-category hypothesis, because Mathlib builds Hom complexes as
complexes of abelian groups.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex

universe v u

/-- **Stacks 0A5X**.
The canonical identification `Hⁿ(Hom^•(L, M)) ≃+ Hom_{K(C)}(L, M⟦n⟧)` of the degree-`n`
cohomology of the Hom complex with morphisms in the homotopy category. -/
@[stacks 0A5X, simps! apply symm_apply]
noncomputable def homComplexHomologyAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C] (L M : CochainComplex C ℤ) (n : ℤ) :
    (L.HomComplex M).homology n ≃+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (M⟦n⟧)) :=
  (CochainComplex.HomComplex.homologyAddEquiv L M n).trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition with `f : K' ⟶ K`, as an additive map on degree-`n` cocycles of the Hom
complex. -/
def cocyclePrecompAddMonoidHom {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cocycle K L n →+ CochainComplex.HomComplex.Cocycle K' L n where
  toFun z := z.precomp f
  map_zero' := by ext p q hpq; simp
  map_add' z₁ z₂ := by ext p q hpq; simp

/-- Postcomposition with `g : L ⟶ L'`, as an additive map on degree-`n` cocycles of the Hom
complex. -/
def cocyclePostcompAddMonoidHom (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ}
    (g : L ⟶ L') (n : ℤ) :
    CochainComplex.HomComplex.Cocycle K L n →+ CochainComplex.HomComplex.Cocycle K L' n where
  toFun z := z.postcomp g
  map_zero' := by ext p q hpq; simp
  map_add' z₁ z₂ := by ext p q hpq; simp

/-- The map `Hⁿ(Hom^•(K, L)) → Hⁿ(Hom^•(K', L))` induced by a morphism `f : K' ⟶ K`: the Hom
complex is contravariant in its first variable. -/
def cohomologyClassPrecomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K) (L : CochainComplex C ℤ)
    (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass K L n →+
      CochainComplex.HomComplex.CohomologyClass K' L n :=
  CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
    ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom K' L n).comp
      (cocyclePrecompAddMonoidHom f L n)) (by
      rintro z ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom_apply,
        CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
      rw [CochainComplex.HomComplex.mem_coboundaries_iff _ m hm]
      exact ⟨(CochainComplex.HomComplex.Cochain.ofHom f).comp β (zero_add m), by
        simp [cocyclePrecompAddMonoidHom, CochainComplex.HomComplex.δ_ofHom_comp, hβ]⟩)

/-- The map `Hⁿ(Hom^•(K, L)) → Hⁿ(Hom^•(K, L'))` induced by a morphism `g : L ⟶ L'`: the Hom
complex is covariant in its second variable. -/
def cohomologyClassPostcomp (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ} (g : L ⟶ L')
    (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass K L n →+
      CochainComplex.HomComplex.CohomologyClass K L' n :=
  CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
    ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom K L' n).comp
      (cocyclePostcompAddMonoidHom K g n)) (by
      rintro z ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom_apply,
        CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
      rw [CochainComplex.HomComplex.mem_coboundaries_iff _ m hm]
      exact ⟨β.comp (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero m), by
        simp [cocyclePostcompAddMonoidHom, CochainComplex.HomComplex.δ_comp_ofHom, hβ]⟩)

/-- `cohomologyClassPrecomp f L n` sends the class of a cocycle `z` to the class of
`z.precomp f`. -/
@[simp]
lemma cohomologyClassPrecomp_mk {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : CochainComplex.HomComplex.Cocycle K L n) :
    cohomologyClassPrecomp f L n (CochainComplex.HomComplex.CohomologyClass.mk z) =
      CochainComplex.HomComplex.CohomologyClass.mk (z.precomp f) :=
  rfl

/-- `cohomologyClassPostcomp K g n` sends the class of a cocycle `z` to the class of
`z.postcomp g`. -/
@[simp]
lemma cohomologyClassPostcomp_mk (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ}
    (g : L ⟶ L') (n : ℤ) (z : CochainComplex.HomComplex.Cocycle K L n) :
    cohomologyClassPostcomp K g n (CochainComplex.HomComplex.CohomologyClass.mk z) =
      CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp g) :=
  rfl

/-- Naturality of `CohomologyClass.toHom` in the first variable: the identification of
[stacks 0A5X] turns precomposition on cohomology classes into precomposition in the homotopy
category. -/
lemma toHom_cohomologyClassPrecomp {K K' L : CochainComplex C ℤ} (f : K' ⟶ K) (n : ℤ)
    (c : CochainComplex.HomComplex.CohomologyClass K L n) :
    CochainComplex.HomComplex.CohomologyClass.toHom (cohomologyClassPrecomp f L n c) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f ≫
        CochainComplex.HomComplex.CohomologyClass.toHom c := by
  obtain ⟨z, rfl⟩ := c.mk_surjective
  rw [cohomologyClassPrecomp_mk, CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

/-- Naturality of `CohomologyClass.toHom` in the second variable: the identification of
[stacks 0A5X] turns postcomposition on cohomology classes into postcomposition with the shifted
morphism in the homotopy category. -/
lemma toHom_cohomologyClassPostcomp {K L L' : CochainComplex C ℤ} (g : L ⟶ L') (n : ℤ)
    (c : CochainComplex.HomComplex.CohomologyClass K L n) :
    CochainComplex.HomComplex.CohomologyClass.toHom (cohomologyClassPostcomp K g n c) =
      CochainComplex.HomComplex.CohomologyClass.toHom c ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (g⟦n⟧') := by
  obtain ⟨z, rfl⟩ := c.mk_surjective
  rw [cohomologyClassPostcomp_mk, CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

end Functoriality

section Localization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- When the localization map `Hom_{K(C)}(X, Y) → Hom_{D(C)}(X, Y)` is bijective, it is an
isomorphism of abelian groups, because `DerivedCategory.Qh` is additive. -/
noncomputable def qhMapAddEquivOfBijective {X Y : HomotopyCategory C (ComplexShape.up ℤ)}
    (h : Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y) → _)) :
    (X ⟶ Y) ≃+ (DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y) :=
  AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom h

/-- `qhMapAddEquivOfBijective h` is the map `f ↦ DerivedCategory.Qh.map f`. -/
@[simp]
lemma qhMapAddEquivOfBijective_apply {X Y : HomotopyCategory C (ComplexShape.up ℤ)}
    (h : Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y) → _)) (f : X ⟶ Y) :
    qhMapAddEquivOfBijective h f = DerivedCategory.Qh.map f :=
  rfl

/-- `DerivedCategory.Qh` inverts the image in the homotopy category of a quasi-isomorphism of
cochain complexes. -/
instance isIso_Qh_map_quotient_map_of_quasiIso {K L : CochainComplex C ℤ} (g : K ⟶ L)
    [QuasiIso g] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g)) :=
  Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
    (by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
      infer_instance)

/-- For `I` K-injective, the comparison of [stacks 0A64] bundled as an isomorphism of abelian
groups `CohomologyClass L I n ≃+ Hom_{D(C)}(L, I⟦n⟧)`. -/
noncomputable def cohomologyClassRHomAddEquivOfIsKInjective (L I : CochainComplex C ℤ)
    [I.IsKInjective] (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass L I n ≃+
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (I⟦n⟧))) :=
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    (qhMapAddEquivOfBijective (CochainComplex.IsKInjective.Qh_map_bijective _ _))

/-- `cohomologyClassRHomAddEquivOfIsKInjective L I n` sends a class `c` to the image under
`DerivedCategory.Qh` of the morphism `L ⟶ I⟦n⟧` in the homotopy category that `c` represents. -/
@[simp]
lemma cohomologyClassRHomAddEquivOfIsKInjective_apply (L I : CochainComplex C ℤ)
    [I.IsKInjective] (n : ℤ) (c : CochainComplex.HomComplex.CohomologyClass L I n) :
    cohomologyClassRHomAddEquivOfIsKInjective L I n c =
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c) :=
  rfl

/-- **Stacks 0A64**.
If `I` is K-injective, then the degree-`n` cohomology of the Hom complex `Hom^•(L, I)` is
canonically identified with the morphisms `L ⟶ I⟦n⟧` in the derived category; equivalently, when
`I` represents `M`, this is `Hⁿ(RHom(L, M)) = Hom(L, M⟦n⟧)`. -/
@[stacks 0A64]
theorem homComplex_of_isKInjective_represents_RHom (L I : CochainComplex C ℤ) [I.IsKInjective]
    (n : ℤ) :
    Function.Bijective
      (fun (c : CochainComplex.HomComplex.CohomologyClass L I n) ↦
        DerivedCategory.Qh.map
          (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c)) :=
  (cohomologyClassRHomAddEquivOfIsKInjective L I n).bijective

end Localization

section Projective

variable {R : Type*} [Ring R] [HasDerivedCategory (ModuleCat R)]

/-- **Stacks 0A66**.
Let `P` be a bounded above complex of projective `R`-modules and `L` a complex of `R`-modules.
The degree-`n` cohomology classes of `Hom^•(P, L)` are canonically *isomorphic as abelian groups*
to `Hom_{D(R)}(P, L⟦n⟧)`, the isomorphism sending a class to the image under
`DerivedCategory.Qh` of the corresponding morphism `P ⟶ L⟦n⟧` in the homotopy category. This is
the assertion that `Hom^•(P, L)` represents `RHom_R(P, L)`. -/
@[stacks 0A66]
noncomputable def cohomologyClassRHomAddEquiv (P L : CochainComplex (ModuleCat R) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)] :
    CochainComplex.HomComplex.CohomologyClass P L n ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj P) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    (qhMapAddEquivOfBijective (CochainComplex.IsKProjective.Qh_map_bijective P _))

/-- `cohomologyClassRHomAddEquiv P L d n` sends a class `c` to the image under
`DerivedCategory.Qh` of the morphism `P ⟶ L⟦n⟧` in the homotopy category that `c` represents. -/
@[simp]
lemma cohomologyClassRHomAddEquiv_apply (P L : CochainComplex (ModuleCat R) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)]
    (c : CochainComplex.HomComplex.CohomologyClass P L n) :
    cohomologyClassRHomAddEquiv P L d n c =
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c) :=
  rfl

/-- **Stacks 0A66**.
The comparison isomorphism of [stacks 0A66] read on the homology of the Hom complex: for `P` a
bounded above complex of projective `R`-modules,
`Hⁿ(Hom^•(P, L)) ≃+ Hom_{D(R)}(P, L⟦n⟧)`, so `Hom^•(P, L)` represents `RHom_R(P, L)`. -/
@[stacks 0A66]
noncomputable def homComplexHomologyRHomAddEquiv (P L : CochainComplex (ModuleCat R) ℤ)
    (d n : ℤ) [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)] :
    (P.HomComplex L).homology n ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj P) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
  (CochainComplex.HomComplex.homologyAddEquiv P L n).trans
    (cohomologyClassRHomAddEquiv P L d n)

/-- `homComplexHomologyRHomAddEquiv P L d n` sends a homology class `x` to the image under
`DerivedCategory.Qh` of the morphism `P ⟶ L⟦n⟧` that `homComplexHomologyAddEquiv` attaches
to `x`. -/
@[simp]
lemma homComplexHomologyRHomAddEquiv_apply (P L : CochainComplex (ModuleCat R) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)]
    (x : (P.HomComplex L).homology n) :
    homComplexHomologyRHomAddEquiv P L d n x =
      DerivedCategory.Qh.map (homComplexHomologyAddEquiv P L n x) :=
  rfl

/-- **Stacks 0A66**.
Let `P` be a bounded above complex of projective `R`-modules and `L` a complex of `R`-modules.
For every `n : ℤ`, the map from degree-`n` cohomology classes of `Hom^•(P, L)` to
`Hom_{D(R)}(P, L⟦n⟧)`, sending a class to the image under `DerivedCategory.Qh` of the corresponding
morphism `P ⟶ L⟦n⟧` in the homotopy category, is bijective; that is, `Hom^•(P, L)` represents
`RHom_R(P, L)`.

This is the pointwise shadow of `cohomologyClassRHomAddEquiv`, from which it is derived. -/
@[stacks 0A66,
  sga "4 XVII 5.5.6.3" "more general",
  sga "4½ Rapport 4.3" "more general",
  sga "5 IIIB 5.7" "partial",
  sga "6 I 7.1.1" "partial"]
theorem homComplex_represents_RHom (P L : CochainComplex (ModuleCat R) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)] :
    Function.Bijective
      (fun (c : CochainComplex.HomComplex.CohomologyClass P L n) =>
        DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c)) :=
  (cohomologyClassRHomAddEquiv P L d n).bijective

/-- **Stacks 0A66**.
Naturality of the comparison isomorphism in the first variable: for `f : P' ⟶ P` a morphism of
bounded above complexes of projectives, the square formed by `cohomologyClassRHomAddEquiv` at `P`
and at `P'`, precomposition by `f` on cohomology classes, and precomposition by the image of `f`
in `D(R)` commutes. Thus `Hom^•(-, L)` represents `RHom_R(-, L)` contravariantly. -/
@[stacks 0A66]
theorem cohomologyClassRHomAddEquiv_naturality_left (P P' L : CochainComplex (ModuleCat R) ℤ)
    (f : P' ⟶ P) (d d' n : ℤ) [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)]
    [P'.IsStrictlyLE d'] [∀ i, CategoryTheory.Projective (P'.X i)]
    (c : CochainComplex.HomComplex.CohomologyClass P L n) :
    cohomologyClassRHomAddEquiv P' L d' n (cohomologyClassPrecomp f L n c) =
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
        cohomologyClassRHomAddEquiv P L d n c := by
  simp only [cohomologyClassRHomAddEquiv_apply,
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply, toHom_cohomologyClassPrecomp,
    Functor.map_comp]

/-- **Stacks 0A66**.
Naturality of the comparison isomorphism in the second variable: for `g : L ⟶ L'` the square
formed by `cohomologyClassRHomAddEquiv` at `L` and at `L'`, postcomposition by `g` on cohomology
classes, and postcomposition by the image of `g⟦n⟧'` in `D(R)` commutes. Thus `Hom^•(P, -)`
represents `RHom_R(P, -)` covariantly. -/
@[stacks 0A66]
theorem cohomologyClassRHomAddEquiv_naturality_right (P L L' : CochainComplex (ModuleCat R) ℤ)
    (g : L ⟶ L') (d n : ℤ) [P.IsStrictlyLE d] [∀ i, CategoryTheory.Projective (P.X i)]
    (c : CochainComplex.HomComplex.CohomologyClass P L n) :
    cohomologyClassRHomAddEquiv P L' d n (cohomologyClassPostcomp P g n c) =
      cohomologyClassRHomAddEquiv P L d n c ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (g⟦n⟧')) := by
  simp only [cohomologyClassRHomAddEquiv_apply,
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply, toHom_cohomologyClassPostcomp,
    Functor.map_comp]

/-- **Stacks 0A66**.
Compatibility of the two routes to `RHom`: for `g : L ⟶ I` with `I` K-injective, the square whose
left edge is the comparison of [stacks 0A66] for `(P, L)`, whose right edge is the comparison of
[stacks 0A64] for `(P, I)`, whose top edge is the map on cohomology classes induced by `g`, and
whose bottom edge is postcomposition with the image of `g⟦n⟧'` in `D(R)`, commutes. No
quasi-isomorphism hypothesis is needed for commutativity. -/
@[stacks 0A66]
theorem homComplexRHom_isKInjective_model_comm (P L I : CochainComplex (ModuleCat R) ℤ)
    (g : L ⟶ I) [I.IsKInjective] (d n : ℤ) [P.IsStrictlyLE d]
    [∀ i, CategoryTheory.Projective (P.X i)]
    (c : CochainComplex.HomComplex.CohomologyClass P L n) :
    cohomologyClassRHomAddEquivOfIsKInjective P I n (cohomologyClassPostcomp P g n c) =
      cohomologyClassRHomAddEquiv P L d n c ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (g⟦n⟧')) :=
  cohomologyClassRHomAddEquiv_naturality_right P L I g d n c

/-- **Stacks 0A66**.
The comparison of [stacks 0A66] is *computed by* the comparison of [stacks 0A64] through a
K-injective model: if `g : L ⟶ I` is a quasi-isomorphism with `I` K-injective, then the bottom
edge of the square of `homComplexRHom_isKInjective_model_comm` is invertible, and the
[stacks 0A66] comparison for `(P, L)` is the [stacks 0A64] comparison for `(P, I)` applied to the
transported class, followed by that inverse. So the two representability statements agree. -/
@[stacks 0A66]
theorem homComplexRHom_eq_isKInjective_model_route (P L I : CochainComplex (ModuleCat R) ℤ)
    (g : L ⟶ I) [I.IsKInjective] [QuasiIso g] (d n : ℤ) [P.IsStrictlyLE d]
    [∀ i, CategoryTheory.Projective (P.X i)]
    (c : CochainComplex.HomComplex.CohomologyClass P L n) :
    cohomologyClassRHomAddEquiv P L d n c =
      cohomologyClassRHomAddEquivOfIsKInjective P I n (cohomologyClassPostcomp P g n c) ≫
        CategoryTheory.inv (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (g⟦n⟧'))) := by
  rw [homComplexRHom_isKInjective_model_comm P L I g d n c, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

end Projective
