module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexInduction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantComplexModelsTransport
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# One constant model over a connected base

Let `C` be a small site with pullbacks and `Λ` a Noetherian ring. A bounded object `K` of the
derived category of sheaves of `Λ`-modules with locally constant finite-type cohomology becomes,
over the members of a covering family of an object `X`, the constant complex attached to a
bounded complex of finite `Λ`-modules; the complex depends a priori on the member. When the site
over `X` has a connected topological realization, a single complex works on a covering family:
the derived models at two members whose images meet are isomorphic over `Λ`, so the covering
family splits into open pieces indexed by the isomorphism class of the model and connectedness
leaves one piece.

## Main results

* `Stacks.ConstantSheaf.exists_iso_of_constantComplexModels_of_point`: two constant derived
  models of one complex of sheaves, over two objects carrying lifts of one point of the site,
  have isomorphic complexes of coefficients.
* `Stacks.ConstantSheaf.exists_cover_uniform_constantComplex_representation`: one bounded
  finite-type complex of `Λ`-modules whose constant complex represents `K` over every member of
  a covering family.
* `Stacks.ConstantSheaf.isPerfect_of_hasFlatRepresentative`: a bounded complex of finite modules
  over a Noetherian ring with a bounded flat representative is perfect.
* `Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_isPerfect`: the same
  covering family carries a model by finite *projective* `Λ`-modules as soon as the complex of
  coefficients is perfect.
* `Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex`: the three results
  combined — one finite complex of finite projective `Λ`-modules on one covering family, under
  the hypothesis that the constant local models of `K` have finite Tor dimension over `Λ`.
* `Stacks.ConstantSheaf.hasFlatRepresentative_of_constantComplexModel_of_point`: a flat
  representative of the derived fibre at a point lifting to `U` of a complex with a constant
  model over `U` is a flat representative of the complex of coefficients.
* `Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_point`: the same
  conclusion with the Tor-dimension hypothesis asked for only at the objects of the site which
  carry a point, which is where it holds.

Each of these except the last two is also proved with the site of arbitrary size, under the primed
name: `exists_iso_of_constantComplexModels_of_point'`, `isPerfect_of_hasFlatRepresentative'`,
`exists_cover_uniform_constantComplex_representation'`,
`exists_cover_constantFiniteProjectiveComplex_of_isPerfect'`,
`hasFlatRepresentative_of_constantComplexModel_of_point'` and
`exists_cover_constantFiniteProjectiveComplex_of_point'`. The objects of the site, its morphisms
and the ring lie in three unrelated universes `u`, `v` and `r`, and the sections are taken in
`max u v r`.

## Implementation notes

The connectedness hypothesis is carried by a *realization* `img : C → Set Z` in a connected
space `Z`: the images are open, a family of arrows to `X` is covering exactly when its images
cover `Z`, and two objects whose images meet have a point of the site lifting to both. Those
are the three properties of the small étale site of a connected scheme that the argument uses,
and keeping them as hypotheses keeps the proof inside the site.

The complexes of coefficients are compared at a point of the site rather than by a universal
property: the fibre of a constant sheaf is its value, the fibre functor is exact, so it carries a
derived isomorphism of constant complexes to one of the complexes of coefficients. Two objects
are first replaced by a common refinement, which exists because the neighbourhoods of a point
form a cofiltered category.

Finite Tor dimension of the complex of coefficients is *not* derived here: it is the one input
that membership of `K` in a category of complexes of finite Tor dimension supplies, and it is a
hypothesis of `exists_cover_constantFiniteProjectiveComplex`. What is proved is that it is
enough: over a Noetherian ring a bounded complex of finite modules is pseudo-coherent, because
its cohomology is a quotient of a submodule of a finite module in every degree, so finite Tor
dimension makes it perfect.

On a site of arbitrary size the point of the site and the sections are taken in the same universe
`max u v r`. There the exactness inputs of the argument carry no hypothesis: the site is locally
small and the ring is small in that universe, so filtered colimits of modules are exact there, and
the fibre functor is exact for that reason alone. The identification of the fibre of a constant
sheaf is taken through `CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`
rather than `CategoryTheory.Sites.constantSheafFiberIso`: the fibre functor on sheaves is a
localization of the fibre functor on presheaves, which inverts the sheafification map of the
constant presheaf with no concreteness of the coefficients, whereas the concrete route would ask
for `GrothendieckTopology.WEqualsLocallyBijective` at a carrier universe the module universe does
not have.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe u

attribute [local instance] HasDerivedCategory.standard

-- The fibre of a constant sheaf is read off the fibre of the constant *presheaf*, and the
-- constant sheaf functor is the constant presheaf followed by sheafification; the comparison is
-- definitional but goes through `constantSheaf`, so that is made transparent to unification.
attribute [local implicit_reducible] CategoryTheory.constantSheaf

/-! ### Constant sheaves and continuous pushforward -/

/-- The constant sheaf functor commutes with the pushforward along a continuous left adjoint
whose right adjoint is continuous as well. -/
private noncomputable def constantSheafPushforwardIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type*) [Category A] [HasWeakSheafify J A] [HasWeakSheafify K A]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.IsContinuous J K] [R.IsContinuous K J] {T : D} (hT : IsTerminal T) :
    constantSheaf K A ⋙ L.sheafPushforwardContinuous A J K ≅ constantSheaf J A := by
  letI := adj.isRightAdjoint
  exact ((constantSheafAdj K A hT).comp (adj.sheafPushforwardContinuous J K)).leftAdjointUniq
    (constantSheafAdj J A (hT.isTerminalObj R T))

/-- Restricting a constant sheaf on a slice along an arrow of the base gives the constant sheaf
with the same value. -/
private noncomputable def overMapPullbackConstantSheafIso
    {C : Type*} [Category C] [HasPullbacks C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    {U V : C} [HasWeakSheafify (J.over U) A] [HasWeakSheafify (J.over V) A]
    (f : V ⟶ U) :
    constantSheaf (J.over U) A ⋙ J.overMapPullback A f ≅ constantSheaf (J.over V) A :=
  constantSheafPushforwardIso (J.over V) (J.over U) A (Over.mapPullbackAdj f)
    (Over.mkIdTerminal (X := U))

/-! ### The fibre of a constant sheaf and of a constant complex -/

/-- The fibre at a point of the site of a constant sheaf of `Λ`-modules is its value, naturally
in the value. -/
private noncomputable def constantSheafFiberNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (p : J.Point.{u}) :
    constantSheaf J (ModuleCat.{u} Λ) ⋙ p.sheafFiber ≅ 𝟭 (ModuleCat.{u} Λ) :=
  NatIso.ofComponents (fun M => Sites.constantSheafFiberIso p M)
    (fun f => (Sites.constantSheafFiberIso_naturality p f).symm)

/-- The derived fibre at a point of the site of the constant complex attached to a complex of
`Λ`-modules is that complex. -/
private noncomputable def constantComplexFiberIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (p : J.Point.{u})
    [(p.sheafFiber (A := ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits (p.sheafFiber (A := ModuleCat.{u} Λ))]
    [PreservesFiniteColimits (p.sheafFiber (A := ModuleCat.{u} Λ))]
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    (p.sheafFiber (A := ModuleCat.{u} Λ)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj P :=
  (p.sheafFiber (A := ModuleCat.{u} Λ)).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
          (constantSheafFiberNatIso J Λ p) (.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} Λ) (.up ℤ)).app P)

/-- Two constant complexes that become isomorphic in the derived category of a site with a point
have isomorphic complexes of coefficients. -/
private lemma exists_iso_of_constantComplexIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (p : J.Point.{u})
    [(p.sheafFiber (A := ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits (p.sheafFiber (A := ModuleCat.{u} Λ))]
    [PreservesFiniteColimits (p.sheafFiber (A := ModuleCat.{u} Λ))]
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (e : DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (.up ℤ)).obj Q)) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :=
  ⟨(constantComplexFiberIso J Λ p P).symm ≪≫
    (p.sheafFiber (A := ModuleCat.{u} Λ)).mapDerivedCategory.mapIso e ≪≫
      constantComplexFiberIso J Λ p Q⟩

/-! ### Transport of a constant model along an arrow of the base -/

/-- A constant derived model over an object of the site restricts to a constant derived model,
with the same coefficients, over any object above it. -/
public lemma exists_constantComplexModel_of_hom
    {C : Type*} [Category C] [HasPullbacks C]
    (J : GrothendieckTopology C) (A : Type*) [Category A] [Abelian A]
    [HasSheafify J A] [∀ U : C, HasSheafify (J.over U) A]
    {U V : C} (f : V ⟶ U)
    [(J.overPullback A U).Additive] [(J.overPullback A V).Additive]
    [(J.overMapPullback A f).Additive]
    [PreservesFiniteLimits (J.overMapPullback A f)]
    [PreservesFiniteColimits (J.overMapPullback A f)]
    (T : CochainComplex (Sheaf J A) ℤ) (P : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj
        (((J.overPullback A U).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) A).mapHomologicalComplex (.up ℤ)).obj P)) :
    Nonempty (DerivedCategory.Q.obj
        (((J.overPullback A V).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over V) A).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let F := J.overMapPullback A f
  let er : J.overPullback A U ⋙ F ≅ J.overPullback A V :=
    NatIso.ofComponents (fun S => S.pushforwardOverMapIso f) (by
      intro S S' a
      ext Z
      show a.hom.app (op Z.unop.left) ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.app (op Z.unop.left)
      simp)
  let ec : constantSheaf (J.over U) A ⋙ F ≅ constantSheaf (J.over V) A :=
    overMapPullbackConstantSheafIso J A f
  exact ⟨(DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso er (.up ℤ)).app T)).symm ≪≫
    (F.mapDerivedCategoryFactors.app _).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso ec (.up ℤ)).app P)⟩

/-- Constant derived models of one complex of sheaves over two objects carrying lifts of one
point of the site have isomorphic complexes of coefficients. -/
theorem exists_iso_of_constantComplexModels_of_point
    {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ]
    (p : J.Point.{u}) {U V : C} (x : p.fiber.obj U) (y : p.fiber.obj V)
    (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ)
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (eU : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapHomologicalComplex (.up ℤ)).obj P))
    (eV : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over V) (ModuleCat.{u} Λ)).mapHomologicalComplex (.up ℤ)).obj Q)) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  have : AB5OfSize.{u, u} (ModuleCat.{u} Λ) :=
    ⟨fun I _ _ => HasExactColimitsOfShape.domain_of_functor I (forget (ModuleCat.{u} Λ))⟩
  have (W : C) : (J.overPullback (ModuleCat.{u} Λ) W).Additive :=
    Functor.additive_of_preserves_binary_products _
  let a := p.fiber.elementsMk U x
  let b := p.fiber.elementsMk V y
  let z := IsCofiltered.min a b
  let g := (IsCofiltered.minToLeft a b).1
  let h := (IsCofiltered.minToRight a b).1
  have : (J.overMapPullback (ModuleCat.{u} Λ) g).IsLeftAdjoint :=
    ((Over.mapPullbackAdj g).sheafPushforwardContinuous (J.over z.1) (J.over U)).isLeftAdjoint
  have : (J.overMapPullback (ModuleCat.{u} Λ) h).IsLeftAdjoint :=
    ((Over.mapPullbackAdj h).sheafPushforwardContinuous (J.over z.1) (J.over V)).isLeftAdjoint
  have : (J.overMapPullback (ModuleCat.{u} Λ) g).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (J.overMapPullback (ModuleCat.{u} Λ) h).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((p.over z.2).sheafFiber (A := ModuleCat.{u} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨eP⟩ := exists_constantComplexModel_of_hom J (ModuleCat.{u} Λ) g T P eU
  obtain ⟨eQ⟩ := exists_constantComplexModel_of_hom J (ModuleCat.{u} Λ) h T Q eV
  exact exists_iso_of_constantComplexIso (J.over z.1) Λ (p.over z.2) P Q (eP.symm ≪≫ eQ)

/-- An isomorphism of complexes of coefficients in the derived category induces one of the
associated constant complexes. -/
private noncomputable def constantComplexIsoOfIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (A : Type*) [Category A] [Abelian A] [HasSheafify J A]
    [(constantSheaf J A).Additive]
    [PreservesFiniteLimits (constantSheaf J A)]
    [PreservesFiniteColimits (constantSheaf J A)]
    {P Q : CochainComplex A ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    DerivedCategory.Q.obj (((constantSheaf J A).mapHomologicalComplex (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj (((constantSheaf J A).mapHomologicalComplex (.up ℤ)).obj Q) :=
  ((constantSheaf J A).mapDerivedCategoryFactors.app P).symm ≪≫
    (constantSheaf J A).mapDerivedCategory.mapIso e ≪≫
      (constantSheaf J A).mapDerivedCategoryFactors.app Q

/-- A constant derived model over `U` keeps being one when its complex of coefficients is replaced
by one with the same image in the derived category. -/
private lemma nonempty_iso_constantComplex_of_iso.{u₁, v₁, r₁}
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type r₁) [CommRing Λ]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u₁ v₁ r₁} Λ)) ℤ) (U : C)
    {P Q : CochainComplex (ModuleCat.{max u₁ v₁ r₁} Λ) ℤ}
    (hmodel : Nonempty (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u₁ v₁ r₁} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    Nonempty (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u₁ v₁ r₁} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q)) := by
  have : (constantSheaf (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)).Additive := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ)) := by
    unfold constantSheaf
    infer_instance
  exact ⟨hmodel.some ≪≫ constantComplexIsoOfIso (J.over U) (ModuleCat.{max u₁ v₁ r₁} Λ) e⟩

/-! ### Connectedness -/

/-- A family of open sets covering a connected space, labelled by objects of a category so that
the labels at two members through a common point are isomorphic, has a subfamily which still
covers and all of whose labels are isomorphic to one of them. -/
public lemma exists_index_iUnion_eq_univ_of_connected
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z]
    {I : Type*} {A : Type*} [Category A] (S : I → Set Z) (P : I → A)
    (hcover : (⋃ i, S i) = Set.univ) (hopen : ∀ i, IsOpen (S i))
    (hagree : ∀ (i j : I) (z : Z), z ∈ S i → z ∈ S j → Nonempty (P i ≅ P j)) :
    ∃ i₀ : I, (⋃ i : {i : I // Nonempty (P i ≅ P i₀)}, S i.1) = Set.univ := by
  classical
  obtain ⟨z₀⟩ := ‹ConnectedSpace Z›.toNonempty
  obtain ⟨i₀, hi₀⟩ := Set.iUnion_eq_univ_iff.mp hcover z₀
  have hcompl : (⋃ i : {i : I // Nonempty (P i ≅ P i₀)}, S i.1)ᶜ =
      ⋃ i : {i : I // ¬Nonempty (P i ≅ P i₀)}, S i.1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hcover z
      exact Set.mem_iUnion.mpr ⟨⟨i, fun hiso => hz (Set.mem_iUnion.mpr ⟨⟨i, hiso⟩, hi⟩)⟩, hi⟩
    · rintro hz hW
      obtain ⟨⟨i, hi⟩, hzi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨⟨j, hj⟩, hzj⟩ := Set.mem_iUnion.mp hW
      obtain ⟨e⟩ := hagree i j z hzi hzj
      exact hi ⟨e ≪≫ hj.some⟩
  refine ⟨i₀, IsClopen.eq_univ ⟨?_, ?_⟩ ⟨z₀, Set.mem_iUnion.mpr ⟨⟨i₀, ⟨Iso.refl _⟩⟩, hi₀⟩⟩⟩
  · rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun i => hopen i.1
  · exact isOpen_iUnion fun i => hopen i.1

/-! ### Finite Tor dimension upgrades a finite-type model to a finite projective one -/

/-- A bounded complex of finite modules over a Noetherian ring with a bounded flat representative
is perfect, for any carrier universe of the modules containing the ring's. -/
private lemma isPerfect_of_hasFlatRepresentative_aux.{r₁, m₁} {Λ : Type r₁} [CommRing Λ]
    [IsNoetherianRing Λ] (P : CochainComplex (ModuleCat.{max r₁ m₁} Λ) ℤ) (a b : ℤ)
    (hvanish : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (P.X n))
    (hfg : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) (c d : ℤ)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) := by
  have : Small.{max r₁ m₁} Λ := small_max.{max r₁ m₁} Λ
  have hfin (n : ℤ) : Module.Finite Λ (P.X n) := (ModuleCat.isFG_iff _).mp (hfg n)
  have hhom (i : ℤ) : Module.Finite Λ (P.homology i) := by
    have : Module.Finite Λ (P.cycles i) :=
      Module.Finite.of_injective (P.iCycles i).hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
    exact Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hbridge (i : ℤ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{max r₁ m₁} Λ) i).obj (DerivedCategory.Q.obj P) ≅
        P.homology i := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max r₁ m₁} Λ) i).app P
  have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj P) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (DerivedCategory.Q.obj P) 0 (ULift.{m₁} Λ)).2.1.mpr
      ⟨⟨b, fun i hi => (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc i)
          (hvanish i (by simp only [Set.mem_Icc]; omega))).of_iso (hbridge i)⟩,
        fun i => Module.Finite.equiv (hbridge i).toLinearEquiv.symm⟩
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension
    (DerivedCategory.Q.obj P)).1.mpr ⟨hpseudo, c, d, hflat⟩

/-- A bounded complex of finite modules over a Noetherian ring which has a bounded flat
representative in the derived category is a perfect object: it is pseudo-coherent because its
cohomology is finite in every degree, so [stacks 0658] applies. -/
@[sga "6 I 5.0" "partial"]
theorem isPerfect_of_hasFlatRepresentative {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ)
    (hvanish : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (P.X n))
    (hfg : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) (c d : ℤ)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) := by
  exact isPerfect_of_hasFlatRepresentative_aux.{u, u} P a b hvanish hfg c d hflat

/-! ### One constant model on a covering family -/

/-- **Tag 09BI, the trivialization by one complex.** Let `C` be a small site with pullbacks, `Λ` a
Noetherian ring and `X` an object whose site has a connected realization `img` in a topological
space. A bounded object `K` of the derived category of sheaves of `Λ`-modules with locally
constant finite-type cohomology is, over the members of one covering family of `X`, the constant
complex attached to a single bounded complex of finite `Λ`-modules. -/
theorem exists_cover_uniform_constantComplex_representation
    {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (X : C)
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type u} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{u}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u} Λ)) n).obj K.obj)) :
    ∃ (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T)
      (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ),
      (∀ n : ℤ, n ∉ Set.Icc a b → IsZero (P.X n)) ∧ (∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) ∧
      ∃ (I : Type u) (U : I → C) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ J X ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{u} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  classical
  obtain ⟨T, e, I, U, f, hcov, hmodel⟩ :=
    exists_cover_constantComplex_representation J Λ X K hK
  choose P a b hPvanish hPfg hPmodel using hmodel
  have hagree : ∀ (i j : I) (z : Z), z ∈ img (U i) → z ∈ img (U j) →
      Nonempty (DerivedCategory.Q.obj (P i) ≅ DerivedCategory.Q.obj (P j)) := by
    intro i j z hi hj
    obtain ⟨p, ⟨x⟩, ⟨y⟩⟩ := hpoint (U i) (U j) z hi hj
    exact exists_iso_of_constantComplexModels_of_point J Λ p x y T (P i) (P j)
      (hPmodel i).some (hPmodel j).some
  obtain ⟨i₀, hi₀⟩ := exists_index_iUnion_eq_univ_of_connected
    (fun i => img (U i)) (fun i => DerivedCategory.Q.obj (P i))
    ((himgCover U f).mp hcov) (fun i => himgOpen (U i)) hagree
  refine ⟨T, e, P i₀, a i₀, b i₀, hPvanish i₀, hPfg i₀,
    {i : I // Nonempty (DerivedCategory.Q.obj (P i) ≅ DerivedCategory.Q.obj (P i₀))},
    fun i => U i.1, fun i => f i.1, (himgCover _ _).mpr hi₀, fun i => ?_⟩
  exact nonempty_iso_constantComplex_of_iso J Λ T (U i.1) (hPmodel i.1) i.property.some

/-- **Tag 09BI, the passage to finite projective coefficients.** A constant derived model whose
complex of coefficients is a perfect object of the derived category of `Λ`-modules may be taken
to consist of finite projective `Λ`-modules, on the same family of objects. -/
theorem exists_cover_constantFiniteProjectiveComplex_of_isPerfect
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ]
    (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P))
    {I : Type u} (U : I → C)
    (hmodel : ∀ i, Nonempty (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{u} Λ) (U i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))) :
    ∃ (E : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∀ i, Nonempty (DerivedCategory.Q.obj
          (((J.overPullback (ModuleCat.{u} Λ) (U i)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj
          (((constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨E, a, b, hGE, hLE, hfinite, hprojective, ⟨eE⟩⟩ := hP
  refine ⟨E, a, b, hGE, hLE, hfinite, hprojective, fun i => ?_⟩
  exact nonempty_iso_constantComplex_of_iso J Λ T (U i) (hmodel i) eE

/-- **Tag 09BI, with its Tor-dimension input named.** Let `C` be a small site with pullbacks, `Λ`
a Noetherian ring and `X` an object whose site has a connected realization in a topological
space. A bounded object `K` of the derived category of sheaves of `Λ`-modules with locally
constant finite-type cohomology, all of whose constant local models have finite Tor dimension
over `Λ`, is the constant complex of a single finite complex of finite projective `Λ`-modules
over the members of one covering family of `X`.

The hypothesis `htor` quantifies over every object of `C`, so it cannot be discharged on a site
having an object covered by the empty family: there every sheaf vanishes, every `P` is a model,
and `htor` would make every complex of `Λ`-modules have a bounded flat representative. The small
étale site is such a site, so use `exists_cover_constantFiniteProjectiveComplex_of_point`, whose
`htor` is asked only at objects a point of the site lifts to. -/
theorem exists_cover_constantFiniteProjectiveComplex
    {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (X : C)
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type u} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{u}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u} Λ)) n).obj K.obj))
    (htor : ∀ (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ) (U : C)
      (P : CochainComplex (ModuleCat.{u} Λ) ℤ), (K.obj ≅ DerivedCategory.Q.obj T) →
      (DerivedCategory.Q.obj (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj (((constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) →
      ∃ c d : ℤ, StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d) :
    ∃ (E : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ)
      (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ) (_e : K.obj ≅ DerivedCategory.Q.obj T),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type u) (U : I → C) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ J X ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{u} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨T, e, P, a, b, hvan, hfg, I, U, f, hcov, hmodel⟩ :=
    exists_cover_uniform_constantComplex_representation J Λ X img himgOpen himgCover hpoint K hK
  obtain ⟨z₀⟩ := ‹ConnectedSpace Z›.toNonempty
  obtain ⟨i, -⟩ := Set.iUnion_eq_univ_iff.mp ((himgCover U f).mp hcov) z₀
  obtain ⟨c, d, hflat⟩ := htor T (U i) P e (hmodel i).some
  obtain ⟨E, a', b', hGE, hLE, hfinite, hprojective, hmodel'⟩ :=
    exists_cover_constantFiniteProjectiveComplex_of_isPerfect J Λ T P
      (isPerfect_of_hasFlatRepresentative P a b hvan hfg c d hflat) U hmodel
  exact ⟨E, a', b', T, e, hGE, hLE, hfinite, hprojective, I, U, f, hcov, hmodel'⟩

/-! ### The Tor-dimension input read at a point of the site -/

/-- The derived fibre, at a point of the site lifting to `U`, of a complex of sheaves carrying a
constant model over `U` is the complex of coefficients; so a flat representative in `[c, d]` of
that derived fibre is one of the complex of coefficients. -/
theorem hasFlatRepresentative_of_constantComplexModel_of_point
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (p : J.Point.{u}) {U : C} (x : p.fiber.obj U)
    [((p.over x).sheafFiber (A := ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits ((p.over x).sheafFiber (A := ModuleCat.{u} Λ))]
    [PreservesFiniteColimits ((p.over x).sheafFiber (A := ModuleCat.{u} Λ))]
    (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (e : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))
    (c d : ℤ)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative
      (((p.over x).sheafFiber (A := ModuleCat.{u} Λ)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj T))) c d) :
    StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d := by
  obtain ⟨E, hEflat, hEGE, hELE, ⟨g⟩⟩ := hflat
  exact ⟨E, hEflat, hEGE, hELE,
    ⟨(((p.over x).sheafFiber (A := ModuleCat.{u} Λ)).mapDerivedCategory.mapIso e ≪≫
      constantComplexFiberIso (J.over U) Λ (p.over x) P).symm ≪≫ g⟩⟩

/-- **Tag 09BI, with its Tor-dimension input named at the points of the site.** Let `C` be a
small site with pullbacks, `Λ` a Noetherian ring and `X` an object whose site has a connected
realization in a topological space. A bounded object `K` of the derived category of sheaves of
`Λ`-modules with locally constant finite-type cohomology, whose constant local models over the
objects carrying a point of the site have finite Tor dimension over `Λ`, is the constant complex
of a single finite complex of finite projective `Λ`-modules over the members of one covering
family of `X`. -/
theorem exists_cover_constantFiniteProjectiveComplex_of_point
    {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (X : C)
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type u} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{u}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u} Λ)) n).obj K.obj))
    (htor : ∀ (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ) (U : C)
      (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (p : J.Point.{u}), p.fiber.obj U →
      (K.obj ≅ DerivedCategory.Q.obj T) →
      (DerivedCategory.Q.obj (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj (((constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) →
      ∃ c d : ℤ, StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d) :
    ∃ (E : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ)
      (T : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ) (_e : K.obj ≅ DerivedCategory.Q.obj T),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type u) (U : I → C) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ J X ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{u} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨T, e, P, a, b, hvan, hfg, I, U, f, hcov, hmodel⟩ :=
    exists_cover_uniform_constantComplex_representation J Λ X img himgOpen himgCover hpoint K hK
  obtain ⟨z₀⟩ := ‹ConnectedSpace Z›.toNonempty
  obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp ((himgCover U f).mp hcov) z₀
  obtain ⟨p, ⟨x⟩, -⟩ := hpoint (U i) (U i) z₀ hi hi
  obtain ⟨c, d, hflat⟩ := htor T (U i) P p x e (hmodel i).some
  obtain ⟨E, a', b', hGE, hLE, hfinite, hprojective, hmodel'⟩ :=
    exists_cover_constantFiniteProjectiveComplex_of_isPerfect J Λ T P
      (isPerfect_of_hasFlatRepresentative P a b hvan hfg c d hflat) U hmodel
  exact ⟨E, a', b', T, e, hGE, hLE, hfinite, hprojective, I, U, f, hcov, hmodel'⟩

/-! ### The fibre of a constant sheaf without concreteness of the coefficients -/

universe v r m w u₂ v₂

/-- The identification of the fibre at a point of the site of a constant presheaf with its value
is natural in the value. -/
private lemma constantPresheafFiberIso_naturality {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {D : Type u₂} [Category.{v₂} D] [HasColimitsOfSize.{w, w} D]
    (Φ : J.Point.{w}) {A B : D} (f : A ⟶ B) :
    (Sites.constantPresheafFiberIso Φ A).hom ≫ f =
      Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫
        (Sites.constantPresheafFiberIso Φ B).hom := by
  apply Φ.presheafFiber_hom_ext
  intro V q
  calc Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          (Sites.constantPresheafFiberIso Φ A).hom ≫ f
      = (Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          (Sites.constantPresheafFiberIso Φ A).hom) ≫ f := by rw [Category.assoc]
    _ = ((Functor.const Cᵒᵖ).map f).app (op V) ≫
          (Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj B) ≫
            (Sites.constantPresheafFiberIso Φ B).hom) := by
          rw [Sites.constantPresheafFiberIso_ι, Sites.constantPresheafFiberIso_ι]
          simp
    _ = Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫
            (Sites.constantPresheafFiberIso Φ B).hom := by
          rw [← Category.assoc, ← Φ.toPresheafFiber_naturality, Category.assoc]

/-- The fibre at a point of the site of a constant presheaf is its value, naturally in the
value. -/
private noncomputable def constantPresheafFiberNatIso {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {D : Type u₂} [Category.{v₂} D] [HasColimitsOfSize.{w, w} D]
    (Φ : J.Point.{w}) :
    (Functor.const Cᵒᵖ : D ⥤ _) ⋙ Φ.presheafFiber ≅ 𝟭 D :=
  NatIso.ofComponents (fun M => Sites.constantPresheafFiberIso Φ M)
    (fun f => (constantPresheafFiberIso_naturality Φ f).symm)

/-- The fibre at a point of the site of a constant sheaf with values in a category having products
and colimits indexed by the universe of the point is its value, naturally in the value.

No concreteness of the coefficients is needed, unlike for
`CategoryTheory.Sites.constantSheafFiberIso`: the fibre functor on sheaves is a localization of the
fibre functor on presheaves at the morphisms that sheafification inverts, so the sheafification map
of a constant presheaf is invertible on fibres for that reason alone. -/
private noncomputable def constantSheafFiberNatIso' {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {D : Type u₂} [Category.{v₂} D] [HasColimitsOfSize.{w, w} D]
    [HasProducts.{w} D] [HasWeakSheafify J D] (Φ : J.Point.{w}) :
    constantSheaf J D ⋙ Φ.sheafFiber ≅ 𝟭 D :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (Φ.presheafToSheafCompSheafFiberIso D) ≪≫
      constantPresheafFiberNatIso Φ

/-! ### Exactness on a site of arbitrary size -/

/-- Restriction of sheaves to a slice site preserves finite limits: on underlying presheaves it is
precomposition with the forgetful functor of the slice, and limits of sheaves are created by the
inclusion into presheaves. -/
private lemma overPullback_preservesFiniteLimits' {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [Abelian A] [HasSheafify J A]
    [∀ U : C, HasSheafify (J.over U) A] (W : C) :
    PreservesFiniteLimits (J.overPullback A W) := by
  have : PreservesFiniteLimits (J.overPullback A W ⋙ sheafToPresheaf (J.over W) A) := by
    show PreservesFiniteLimits
      (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget W).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf (J.over W) A)

/-- Filtered colimits of modules are exact in any module universe containing the ring: the
forgetful functor to that universe is exact and preserves them, the latter because the ring has a
small model there. -/
@[sga "3 I 3.1.1" "special case", sga "6 II 3.1" "special case"]
private lemma ab5OfSize_moduleCat (Λ : Type r) [Ring Λ] [Small.{m} Λ] :
    AB5OfSize.{m, m} (ModuleCat.{m} Λ) :=
  have : PreservesFilteredColimits (forget (ModuleCat.{m} Λ)) := by
    let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (Shrink.ringEquiv Λ : Shrink.{m} Λ ≃+* Λ)
    show PreservesFilteredColimits (e.functor ⋙ forget (ModuleCat.{m} (Shrink.{m} Λ)))
    infer_instance
  ⟨fun I _ _ => HasExactColimitsOfShape.domain_of_functor I (forget (ModuleCat.{m} Λ))⟩

/-! ### Tag 09BI on a site of arbitrary size -/

/-- The derived fibre at a point of the site of the constant complex attached to a complex of
`Λ`-modules is that complex, on a site whose objects, morphisms and coefficient ring lie in
unrelated universes. -/
private noncomputable def constantComplexFiberIso'
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v r} Λ)] (p : J.Point.{max u v r})
    [(p.sheafFiber (A := ModuleCat.{max u v r} Λ)).Additive]
    [PreservesFiniteLimits (p.sheafFiber (A := ModuleCat.{max u v r} Λ))]
    (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) :
    (p.sheafFiber (A := ModuleCat.{max u v r} Λ)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((constantSheaf J (ModuleCat.{max u v r} Λ)).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj P :=
  (p.sheafFiber (A := ModuleCat.{max u v r} Λ)).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (constantSheafFiberNatIso' p) (.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v r} Λ) (.up ℤ)).app P)

/-- Two constant complexes that become isomorphic in the derived category of a site with a point
have isomorphic complexes of coefficients, on a site of arbitrary size. -/
private lemma exists_iso_of_constantComplexIso'
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v r} Λ)] (p : J.Point.{max u v r})
    [(p.sheafFiber (A := ModuleCat.{max u v r} Λ)).Additive]
    [PreservesFiniteLimits (p.sheafFiber (A := ModuleCat.{max u v r} Λ))]
    (P Q : CochainComplex (ModuleCat.{max u v r} Λ) ℤ)
    (e : DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{max u v r} Λ)).mapHomologicalComplex (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{max u v r} Λ)).mapHomologicalComplex (.up ℤ)).obj Q)) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :=
  ⟨(constantComplexFiberIso' J Λ p P).symm ≪≫
    (p.sheafFiber (A := ModuleCat.{max u v r} Λ)).mapDerivedCategory.mapIso e ≪≫
      constantComplexFiberIso' J Λ p Q⟩

/-- Constant derived models of one complex of sheaves over two objects carrying lifts of one
point of the site have isomorphic complexes of coefficients, on a site of arbitrary size. -/
theorem exists_iso_of_constantComplexModels_of_point'
    {C : Type u} [Category.{v} C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ]
    [HasSheafify J (ModuleCat.{max u v r} Λ)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (p : J.Point.{max u v r}) {U V : C} (x : p.fiber.obj U) (y : p.fiber.obj V)
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
    (P Q : CochainComplex (ModuleCat.{max u v r} Λ) ℤ)
    (eU : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u v r} Λ) U).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
          (.up ℤ)).obj P))
    (eV : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u v r} Λ) V).mapHomologicalComplex (.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over V) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
          (.up ℤ)).obj Q)) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  have : Small.{max u v r} Λ := small_max.{max u v r} Λ
  have : AB5OfSize.{max u v r, max u v r} (ModuleCat.{max u v r} Λ) := ab5OfSize_moduleCat Λ
  have : LocallySmall.{max u v r} C := CategoryTheory.locallySmall_max.{max u v r, v, u}
  have (W : C) : (J.overPullback (ModuleCat.{max u v r} Λ) W).Additive :=
    have := overPullback_preservesFiniteLimits' J (ModuleCat.{max u v r} Λ) W
    Functor.additive_of_preserves_binary_products _
  let a := p.fiber.elementsMk U x
  let b := p.fiber.elementsMk V y
  let z := IsCofiltered.min a b
  let g := (IsCofiltered.minToLeft a b).1
  let h := (IsCofiltered.minToRight a b).1
  have : (J.overMapPullback (ModuleCat.{max u v r} Λ) g).IsLeftAdjoint :=
    ((Over.mapPullbackAdj g).sheafPushforwardContinuous (J.over z.1) (J.over U)).isLeftAdjoint
  have : (J.overMapPullback (ModuleCat.{max u v r} Λ) h).IsLeftAdjoint :=
    ((Over.mapPullbackAdj h).sheafPushforwardContinuous (J.over z.1) (J.over V)).isLeftAdjoint
  have : (J.overMapPullback (ModuleCat.{max u v r} Λ) g).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (J.overMapPullback (ModuleCat.{max u v r} Λ) h).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : LocallySmall.{max u v r} (Over z.1) :=
    CategoryTheory.locallySmall_max.{max u v r, v, max u v}
  have : PreservesFiniteLimits ((p.over z.2).sheafFiber (A := ModuleCat.{max u v r} Λ)) :=
    inferInstance
  have : ((p.over z.2).sheafFiber (A := ModuleCat.{max u v r} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨eP⟩ := exists_constantComplexModel_of_hom J (ModuleCat.{max u v r} Λ) g T P eU
  obtain ⟨eQ⟩ := exists_constantComplexModel_of_hom J (ModuleCat.{max u v r} Λ) h T Q eV
  exact exists_iso_of_constantComplexIso' (J.over z.1) Λ (p.over z.2) P Q (eP.symm ≪≫ eQ)

/-- A bounded complex of finite modules over a Noetherian ring which has a bounded flat
representative in the derived category is a perfect object, with the carrier universe of the
modules independent of the universe of the ring. -/
theorem isPerfect_of_hasFlatRepresentative' {Λ : Type r} [CommRing Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (ModuleCat.{max r m} Λ) ℤ) (a b : ℤ)
    (hvanish : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (P.X n))
    (hfg : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) (c d : ℤ)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj P) c d) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) := by
  exact isPerfect_of_hasFlatRepresentative_aux.{r, m} P a b hvanish hfg c d hflat

/-- **Tag 09BI, the trivialization by one complex, on a site of arbitrary size.** Let `C` be a site
with pullbacks, `Λ` a Noetherian ring and `X` an object whose site has a connected realization
`img` in a topological space. A bounded object `K` of the derived category of sheaves of
`Λ`-modules with locally constant finite-type cohomology is, over the members of one covering
family of `X`, the constant complex attached to a single bounded complex of finite `Λ`-modules. -/
theorem exists_cover_uniform_constantComplex_representation'
    {C : Type u} [Category.{v} C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify J (ModuleCat.{max u v r} Λ)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (X : C) {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type (max u v r)} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{max u v r}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{max u v r} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v r} Λ)) n).obj K.obj)) :
    ∃ (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T)
      (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) (a b : ℤ),
      (∀ n : ℤ, n ∉ Set.Icc a b → IsZero (P.X n)) ∧ (∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) ∧
      ∃ (I : Type (max u v r)) (U : I → C) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ J X ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v r} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.over (U i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  classical
  obtain ⟨T, e, I, U, f, hcov, hmodel⟩ :=
    exists_cover_constantComplex_representation' J Λ X K hK
  choose P a b hPvanish hPfg hPmodel using hmodel
  have hagree : ∀ (i j : I) (z : Z), z ∈ img (U i) → z ∈ img (U j) →
      Nonempty (DerivedCategory.Q.obj (P i) ≅ DerivedCategory.Q.obj (P j)) := by
    intro i j z hi hj
    obtain ⟨p, ⟨x⟩, ⟨y⟩⟩ := hpoint (U i) (U j) z hi hj
    exact exists_iso_of_constantComplexModels_of_point' J Λ p x y T (P i) (P j)
      (hPmodel i).some (hPmodel j).some
  obtain ⟨i₀, hi₀⟩ := exists_index_iUnion_eq_univ_of_connected
    (fun i => img (U i)) (fun i => DerivedCategory.Q.obj (P i))
    ((himgCover U f).mp hcov) (fun i => himgOpen (U i)) hagree
  refine ⟨T, e, P i₀, a i₀, b i₀, hPvanish i₀, hPfg i₀,
    {i : I // Nonempty (DerivedCategory.Q.obj (P i) ≅ DerivedCategory.Q.obj (P i₀))},
    fun i => U i.1, fun i => f i.1, (himgCover _ _).mpr hi₀, fun i => ?_⟩
  exact nonempty_iso_constantComplex_of_iso J Λ T (U i.1) (hPmodel i.1) i.property.some

/-- **Tag 09BI, the passage to finite projective coefficients, on a site of arbitrary size.** A
constant derived model whose complex of coefficients is a perfect object of the derived category of
`Λ`-modules may be taken to consist of finite projective `Λ`-modules, on the same family of
objects. -/
theorem exists_cover_constantFiniteProjectiveComplex_of_isPerfect'
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ)
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P))
    {I : Type*} (U : I → C)
    (hmodel : ∀ i, Nonempty (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u v r} Λ) (U i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over (U i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))) :
    ∃ (E : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) (a b : ℤ),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∀ i, Nonempty (DerivedCategory.Q.obj
          (((J.overPullback (ModuleCat.{max u v r} Λ) (U i)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj
          (((constantSheaf (J.over (U i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨E, a, b, hGE, hLE, hfinite, hprojective, ⟨eE⟩⟩ := hP
  refine ⟨E, a, b, hGE, hLE, hfinite, hprojective, fun i => ?_⟩
  exact nonempty_iso_constantComplex_of_iso J Λ T (U i) (hmodel i) eE

/-- The derived fibre, at a point of the site lifting to `U`, of a complex of sheaves carrying a
constant model over `U` is the complex of coefficients; so a flat representative in `[c, d]` of
that derived fibre is one of the complex of coefficients. Stated on a site of arbitrary size. -/
theorem hasFlatRepresentative_of_constantComplexModel_of_point'
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (p : J.Point.{max u v r}) {U : C} (x : p.fiber.obj U)
    [((p.over x).sheafFiber (A := ModuleCat.{max u v r} Λ)).Additive]
    [PreservesFiniteLimits ((p.over x).sheafFiber (A := ModuleCat.{max u v r} Λ))]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ)
    (e : DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{max u v r} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over U) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))
    (c d : ℤ)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative.{r, max u v}
      (((p.over x).sheafFiber (A := ModuleCat.{max u v r} Λ)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((J.overPullback (ModuleCat.{max u v r} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj T))) c d) :
    StacksDraft.Perfect.HasFlatRepresentative.{r, max u v} (DerivedCategory.Q.obj P) c d := by
  obtain ⟨E, hEflat, hEGE, hELE, ⟨g⟩⟩ := hflat
  exact ⟨E, hEflat, hEGE, hELE,
    ⟨(((p.over x).sheafFiber (A := ModuleCat.{max u v r} Λ)).mapDerivedCategory.mapIso e ≪≫
      constantComplexFiberIso' (J.over U) Λ (p.over x) P).symm ≪≫ g⟩⟩

/-- **Tag 09BI, with its Tor-dimension input named at the points of the site, on a site of
arbitrary size.** Let `C` be a site with pullbacks, `Λ` a Noetherian ring and `X` an object whose
site has a connected realization in a topological space. A bounded object `K` of the derived
category of sheaves of `Λ`-modules with locally constant finite-type cohomology, whose constant
local models over the objects carrying a point of the site have finite Tor dimension over `Λ`, is
the constant complex of a single finite complex of finite projective `Λ`-modules over the members
of one covering family of `X`. -/
theorem exists_cover_constantFiniteProjectiveComplex_of_point'
    {C : Type u} [Category.{v} C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify J (ModuleCat.{max u v r} Λ)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (X : C) {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type (max u v r)} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{max u v r}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{max u v r} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v r} Λ)) n).obj K.obj))
    (htor : ∀ (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ) (U : C)
      (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) (p : J.Point.{max u v r}),
      p.fiber.obj U → (K.obj ≅ DerivedCategory.Q.obj T) →
      (DerivedCategory.Q.obj (((J.overPullback (ModuleCat.{max u v r} Λ) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj
          (((constantSheaf (J.over U) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) →
      ∃ c d : ℤ, StacksDraft.Perfect.HasFlatRepresentative.{r, max u v}
        (DerivedCategory.Q.obj P) c d) :
    ∃ (E : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) (a b : ℤ)
      (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type (max u v r)) (U : I → C) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ J X ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v r} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.over (U i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨T, e, P, a, b, hvan, hfg, I, U, f, hcov, hmodel⟩ :=
    exists_cover_uniform_constantComplex_representation' J Λ X img himgOpen himgCover hpoint K hK
  obtain ⟨z₀⟩ := ‹ConnectedSpace Z›.toNonempty
  obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp ((himgCover U f).mp hcov) z₀
  obtain ⟨p, ⟨x⟩, -⟩ := hpoint (U i) (U i) z₀ hi hi
  obtain ⟨c, d, hflat⟩ := htor T (U i) P p x e (hmodel i).some
  obtain ⟨E, a', b', hGE, hLE, hfinite, hprojective, hmodel'⟩ :=
    exists_cover_constantFiniteProjectiveComplex_of_isPerfect' J Λ T P
      (isPerfect_of_hasFlatRepresentative'.{r, max u v} P a b hvan hfg c d hflat) U hmodel
  exact ⟨E, a', b', T, e, hGE, hLE, hfinite, hprojective, I, U, f, hcov, hmodel'⟩

end Stacks.ConstantSheaf

end
