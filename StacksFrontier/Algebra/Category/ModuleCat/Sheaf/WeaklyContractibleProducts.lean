module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksCore.Tactic.StacksAttribute

/-!
# Products of sheaves of modules are exact on a site with enough weakly contractible objects

Let `J` be a Grothendieck topology on a category `C`, let `R : Sheaf J RingCat` be a sheaf of
rings, and suppose `C` has a collection `B` of objects which is *covering* (every object of `C`
has a `J`-covering by members of `B`) and all of whose members are *weakly contractible* (every
locally surjective morphism of sheaves of sets is surjective on sections over them). Then
products in `SheafOfModules R` are exact, i.e. `SheafOfModules R` satisfies the Grothendieck
axiom AB4*. This is Stacks 0947(4), deduced from Stacks 0947(1).

The index set is arbitrary, as in the source: no finiteness and no countability. It is also free
to live in any universe; the lone condition is that it admit a model in the universe `t` of the
modules, which is what makes the product exist in `SheafOfModules.{t} R` at all.

The proof is the three-step one of the source. Products of sheaves of modules are computed
sectionwise, and in abelian groups a product of surjections is surjective; so a product of
epimorphisms is still surjective on sections over the objects of `B`. Since `B` covers, a
morphism which is surjective on sections over every member of `B` is locally surjective, and a
locally surjective morphism of sheaves of modules is an epimorphism. Hence the product functor
preserves epimorphisms, and in an abelian category a limit functor preserving epimorphisms is
exact.

## Main definitions

* `sectionsOver`: the functor sending a sheaf of modules to its abelian group of sections over
  a fixed object.

## Main results

* `isLocallySurjective_of_surjective_of_hasEnoughObjects`: a morphism of presheaves valued in a
  concrete category which is surjective on sections over every object of a covering collection
  is locally surjective.
* `surjective_sections_of_epi`: an epimorphism of sheaves of modules is surjective on sections
  over a weakly contractible object.
* `preservesEpimorphisms_lim`: the product functor over an arbitrary index type on sheaves of
  modules preserves epimorphisms.
* `hasExactLimitsOfShape_discrete`: **Stacks 0947(4)**, products of sheaves of modules over an
  arbitrary index type are exact.
* `ab4Star`: the same, packaged as the Grothendieck axiom AB4*.
* `hasExactLimitsOfShape_discrete_nat`: the countable case, in which the derived-limit arguments
  of Stacks 0945 consume it.

## Implementation notes

The universes of the ring and of the modules are kept independent: `R : Sheaf J RingCat.{w}`
and `SheafOfModules.{t} R`. That independence is what the situation of Stacks 0945 needs, since
it tests weak contractibility on sheaves of sets in the *module* universe while the sheaf of
rings lives in an unrelated one. Both directions of the epimorphism/local-surjectivity
dictionary are cited with the module universe independent of the ring universe: "locally
surjective implies epimorphism" from `Stacks.SheafOfModules.EpiMono` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective`, where it is proved with no
hypotheses, and the converse from `Stacks.SheafOfModules.ImageSubsheaf` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf`.

The only hypothesis on the ringed site beyond the weakly contractible covering is
`Abelian (SheafOfModules.{t} R)`, which is what the statement of exactness needs in order to
mean anything. It is deliberately *not* strengthened to the pair `HasSheafify J AddCommGrpCat.{t}`
and `J.WEqualsLocallyBijective AddCommGrpCat.{t}` that Mathlib uses to produce an abelian
structure: "epimorphism implies locally surjective" is proved in `EpiImageSubsheaf` from the
abelian structure alone, by factoring a morphism through the subsheaf of sections lying locally
in its range, so no sheafification of presheaves of modules is needed. That matters for the
consumers: an abelian structure carried as a hypothesis, as in the derived-limit cohomology
sequence of Stacks 0945, does not produce the sheafification hypotheses, so a form of this
result assuming them could not be applied there.

Weak contractibility is phrased as a bare hypothesis on an object rather than through a bundled
structure, so that the result applies to any packaging of the situation of Stacks 0945.

The index type is kept in its own universe rather than being forced into the module universe `t`:
the consumers index by `ℕ : Type 0` while the modules live in an unrelated `t`, so a form stated
for `ι : Type t` would not apply to them. `Small.{t} ι` is what the statement needs and is
discharged for `ℕ` by `small_zero`.

The conclusion `HasExactLimitsOfShape (Discrete ι) (SheafOfModules.{t} R)` does not mention the
abelian structure (all of `HasExactLimitsOfShape`, `PreservesFiniteColimits` and
`HasLimitsOfShape` are propositions), so it may be consumed in a context carrying an
independently supplied `Abelian (SheafOfModules.{t} R)` instance -- and, with the hypothesis
above being exactly such an instance, it may also be *proved* there.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), parts (1) and (4)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory Limits Opposite Functor

universe t w w' v' u' v u u₀

namespace Stacks.SheafOfModules.WeaklyContractible

section Covering

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

/-- If every object of `C` has a `J`-covering by objects satisfying `B`, then a morphism of
presheaves which is surjective on sections over every object satisfying `B` is locally
surjective. This is the only use made of the covering hypothesis of Stacks 090L(3). -/
theorem isLocallySurjective_of_surjective_of_hasEnoughObjects {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hsurj : ∀ U : C, B U → Function.Surjective (f.app (op U))) :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    obtain ⟨I, Ui, p, hp, hUi⟩ := hB U
    refine J.superset_covering ?_ hp
    rintro V q hq
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hq
    obtain ⟨u, hu⟩ := hsurj (Ui i) (hUi i) (G.map (p i).op s)
    refine ⟨F.map a.op u, ?_⟩
    rw [NatTrans.naturality_apply f, hu, ← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp]

end Covering

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The functor taking a sheaf of `R`-modules to its abelian group of sections over `U`. -/
noncomputable abbrev sectionsOver (R : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{t} R ⥤ AddCommGrpCat.{t} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{t}).obj (op U)

variable {R : Sheaf J RingCat.{w}} [Abelian (SheafOfModules.{t} R)]

/-- **Stacks 0947(1)**, the module case: an epimorphism of sheaves of modules is surjective on
sections over a weakly contractible object. Weak contractibility is tested on sheaves of sets in
the universe of the modules. -/
theorem surjective_sections_of_epi {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] (U : C)
    (hU : ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op U))) :
    Function.Surjective ((sectionsOver.{t} R U).map f) := by
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
    ImageSubsheaf.isLocallySurjective_of_epi f
  exact hU _ _ ((sheafCompose J (forget AddCommGrpCat.{t})).map ((SheafOfModules.toSheaf R).map f))
    inferInstance

end Sections

section Exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [Abelian (SheafOfModules.{t} R)]

/-- A functor preserving limits of shape `K` turns the induced map on `K`-limits into the induced
map on the limits of the images, up to canonical isomorphism; so if the latter is an epimorphism,
so is the former. Nothing here is special to a particular shape. -/
private lemma epi_map_limMap {K : Type*} [Category* K] {D : Type*} [Category* D] {E : Type*}
    [Category* E] [HasLimitsOfShape K D] [HasLimitsOfShape K E] (T : D ⥤ E)
    [PreservesLimitsOfShape K T] {F G : K ⥤ D} (φ : F ⟶ G)
    (h : Epi (limMap (Functor.whiskerRight φ T))) : Epi (T.map (limMap φ)) := by
  have e := preservesLimitNatIso T (J := K)
  have : Epi (((whiskeringRight K D E).obj T ⋙ lim).map φ) := h
  have : Epi (T.map (limMap φ) ≫ e.hom.app G) := by
    show Epi ((lim ⋙ T).map φ ≫ e.hom.app G)
    rw [e.hom.naturality φ]
    exact epi_comp _ _
  rw [show T.map (limMap φ) = (T.map (limMap φ) ≫ e.hom.app G) ≫ inv (e.hom.app G) by simp]
  exact epi_comp _ _

/-- Products of abelian groups are exact at every index type with a `t`-small model, not only at
index types which already live in the universe `t` of the groups. `AB4Star AddCommGrpCat.{t}` is
Mathlib's instance for `ι : Type t`; the index type of a family of sheaves of modules need not be
in that universe, so it is transported along `Discrete (Shrink.{t} ι) ≌ Discrete ι`. -/
private lemma hasExactLimitsOfShape_discrete_addCommGrpCat (ι : Type u₀) [Small.{t} ι] :
    HasExactLimitsOfShape (Discrete ι) AddCommGrpCat.{t} :=
  HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{t}
    (Discrete.equivalence (equivShrink.{t} ι).symm)

/-- The product functor over an arbitrary index type on sheaves of modules preserves
epimorphisms, on a site all of whose objects are covered by weakly contractible ones. -/
theorem preservesEpimorphisms_lim (ι : Type u₀) [Small.{t} ι] (B : ObjectProperty C)
    (hB : J.HasEnoughObjects B)
    (hwc : ∀ ⦃U : C⦄, B U → ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    (lim (J := Discrete ι) (C := SheafOfModules.{t} R)).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    have := hφ
    have : HasExactLimitsOfShape (Discrete ι) AddCommGrpCat.{t} :=
      hasExactLimitsOfShape_discrete_addCommGrpCat ι
    refine EpiMono.epi_of_isLocallySurjective (limMap φ)
      (isLocallySurjective_of_surjective_of_hasEnoughObjects J _ B hB fun U hU ↦ ?_)
    have happ : ∀ n, Epi ((Functor.whiskerRight φ (sectionsOver.{t} R U)).app n) := fun n ↦
      (AddCommGrpCat.epi_iff_surjective _).2
        (surjective_sections_of_epi (φ.app n) U fun _ _ _ h ↦ hwc hU _ _ _ h)
    have hepi : Epi (Functor.whiskerRight φ (sectionsOver.{t} R U)) :=
      NatTrans.epi_of_epi_app _
    exact (AddCommGrpCat.epi_iff_surjective _).1 <| epi_map_limMap (sectionsOver.{t} R U) φ
      ((lim (J := Discrete ι) (C := AddCommGrpCat.{t})).map_epi _)

/-- **Stacks 0947(4).** On a site every object of which has a covering by weakly contractible
objects, products of sheaves of modules are exact -- over an *arbitrary* index type `ι`, in an
arbitrary universe, subject only to the `t`-smallness that makes the product exist at all. -/
@[stacks 0947 "(4)"]
theorem hasExactLimitsOfShape_discrete (ι : Type u₀) [Small.{t} ι] (B : ObjectProperty C)
    (hB : J.HasEnoughObjects B)
    (hwc : ∀ ⦃U : C⦄, B U → ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    HasExactLimitsOfShape (Discrete ι) (SheafOfModules.{t} R) :=
  have := preservesEpimorphisms_lim (R := R) ι B hB hwc
  hasExactLimitsOfShape_of_preservesEpi _ _

/-- **Stacks 0947(4)** in Mathlib's own formulation: `Mod(O)` satisfies the Grothendieck axiom
AB4\*, products are exact. -/
theorem ab4Star (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hwc : ∀ ⦃U : C⦄, B U → ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    AB4StarOfSize.{t} (SheafOfModules.{t} R) where
  ofShape ι := hasExactLimitsOfShape_discrete ι B hB hwc

/-- **Stacks 0947(4)** at the countable index set `ℕ`, the shape in which the derived-limit
arguments of Stacks 0945 consume it. -/
theorem hasExactLimitsOfShape_discrete_nat (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hwc : ∀ ⦃U : C⦄, B U → ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{t} R) :=
  have : Small.{t} ℕ := small_zero ℕ
  hasExactLimitsOfShape_discrete ℕ B hB hwc

end Exact

end Stacks.SheafOfModules.WeaklyContractible

end
