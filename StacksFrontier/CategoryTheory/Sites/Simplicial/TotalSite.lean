module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplexIso

/-!
# The total site of a simplicial site

A simplicial object in sites has an underlying cosimplicial diagram of categories: a map
`φ : [m] ⟶ [n]` induces the functor `u φ : C m ⟶ C n` underlying the oppositely directed
morphism of sites. Its total category is the contravariant Grothendieck construction. A family
in the total category is covering precisely when it comes from a covering family in one fibre.

## Main definitions

* `CategoryTheory.SimplicialSite`: a simplicial object in sites, packaging the fibre sites and
  their transition morphisms.
* `CategoryTheory.SimplicialSite.totalPseudofunctor`: the strict pseudofunctor whose
  contravariant Grothendieck construction is the total category.
* `CategoryTheory.SimplicialSite.totalCoverage`: the fibrewise collection of covering families.
* `CategoryTheory.SimplicialSite.totalTopology`: the topology it generates.

## Main results

* `CategoryTheory.SimplicialSite.totalCoverage_hasIsos`: the fibrewise covering families
  contain the singleton isomorphisms.
* `CategoryTheory.SimplicialSite.totalCoverage_isStableUnderComposition`: they are stable
  under composition in the total category.

## Implementation notes

Mathlib's `Pretopology` requires all pullbacks in the underlying category. The Stacks definition
only requires pullbacks along members of covering families. We therefore use Mathlib's
`Precoverage` together with its four site-axiom classes; this states the construction without
adding an all-pullbacks hypothesis absent from the source. The induced Grothendieck topology is
`totalCoverage.toGrothendieck`.

The total category, its objects, and its morphisms are the existing Mathlib declarations
`CoGrothendieck`, `CoGrothendieck.Hom`, and `CoGrothendieck.category`. For the pseudofunctor
below, a morphism from `(n, U)` to `(m, V)` is therefore a pair consisting of `φ : [m] ⟶ [n]`
and `U ⟶ u φ (V)`, exactly as in the source.

Stacks 09WC asserts in addition that the fibrewise covering families admit pullbacks and are
stable under base change. Those two assertions, and the recording of the tag against the
declarations below and against Mathlib's `CoGrothendieck` family, are in
`StacksFrontier/CategoryTheory/Sites/Simplicial/TotalPullbacks.lean`, which is where the whole
covering set of the tag is carried.

## References

* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

/-- A simplicial object in sites, represented in the direction of its underlying functors.

Thus `underlying` is cosimplicial: its map attached to `φ : [m] ⟶ [n]` is the functor
`u φ : C m ⟶ C n` which represents the morphism of sites in the opposite direction.
The last two fields are the two clauses of continuity from Stacks 00WV. -/
structure SimplicialSite where
  /-- The underlying cosimplicial diagram of categories. -/
  underlying : CategoryTheory.Functor SimplexCategory Cat.{u, u}
  /-- The covering families in each degree. -/
  coverage : ∀ n, Precoverage (underlying.obj n)
  /-- Singleton isomorphisms cover in each degree. -/
  coverage_hasIsos : ∀ n, (coverage n).HasIsos
  /-- Pullbacks along members of covering families exist in each degree. -/
  coverage_hasPullbacks : ∀ n, (coverage n).HasPullbacks
  /-- Covering families are stable under base change in each degree. -/
  coverage_isStableUnderBaseChange : ∀ n, (coverage n).IsStableUnderBaseChange
  /-- Covering families are stable under composition in each degree. -/
  coverage_isStableUnderComposition : ∀ n, (coverage n).IsStableUnderComposition
  /-- Every transition is a morphism of the associated Grothendieck sites. -/
  isMorphismOfSites : ∀ {m n} (φ : m ⟶ n),
    (underlying.map φ).toFunctor.IsMorphismOfSites
      ((coverage m).toGrothendieck) ((coverage n).toGrothendieck)
  /-- A transition functor takes covering families to covering families. -/
  coverPreserving : ∀ {m n} (φ : m ⟶ n),
    coverage m ≤ (coverage n).comap (underlying.map φ).toFunctor
  /-- A transition functor preserves the pullback of a covering arrow along any arrow. -/
  preservesPullbacks : ∀ {m n} (φ : m ⟶ n) {V : underlying.obj m}
    {R : Presieve V}, R ∈ coverage m V →
    ∀ {W : underlying.obj m} {g : W ⟶ V}, R g →
      ∀ {T : underlying.obj m} (f : T ⟶ V),
        PreservesLimit (cospan f g) (underlying.map φ).toFunctor

namespace SimplicialSite

/-- The strict pseudofunctor whose contravariant Grothendieck construction is the total
category of a simplicial site. -/
def totalPseudofunctor (C : SimplicialSite.{u}) :
    Pseudofunctor (LocallyDiscrete (SimplexCategoryᵒᵖ)ᵒᵖ) Cat.{u, u} :=
  (CategoryTheory.unopUnop SimplexCategory ⋙ C.underlying).toPseudofunctor'

/-- The covering families of the total site: a family covers exactly when it is the image of a
covering family in the component containing its target. -/
@[sga "4 VI 7.4.1" "simplicial case", sga "4 VI 7.4" "simplicial case"]
def totalCoverage (C : SimplicialSite.{u}) :
    Precoverage (CoGrothendieck C.totalPseudofunctor) where
  coverings U := { R | ∃ S : Presieve U.fiber,
    S ∈ C.coverage U.base.unop U.fiber ∧
      S.map (CoGrothendieck.ι C.totalPseudofunctor U.base) = R }

/-- The Grothendieck topology generated by the covering families of the total site. -/
@[sga "4 VI 7.4.1" "special case"]
abbrev totalTopology (C : SimplicialSite.{u}) :
    GrothendieckTopology (CoGrothendieck C.totalPseudofunctor) :=
  C.totalCoverage.toGrothendieck

/-- A faithful functor injective on objects reflects equality of presieves. -/
theorem presieve_map_injective_of_faithful {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) [F.Faithful] (hobj : Function.Injective F.obj) {X : D}
    {R Q : Presieve X} (h : Presieve.map F R = Presieve.map F Q) : R = Q := by
  have key {R Q : Presieve X} (h : Presieve.map F R ≤ Presieve.map F Q) : R ≤ Q := by
    intro Y f hf
    obtain ⟨Z, hZ, g, hg, hfg⟩ := Presieve.map_iff.mp (h _ _ (Presieve.map.of hf))
    obtain rfl := hobj hZ
    obtain rfl : g = f := F.map_injective (by simpa using hfg)
    exact hg
  exact le_antisymm (key h.le) (key h.ge)

/-- The fibres of the total category of a simplicial site, exhibited as fibres of the forgetful
functor to the opposite simplex category. -/
@[instance_reducible]
private def hasFibersForget (C : SimplicialSite.{u}) :
    HasFibers (CoGrothendieck.forget C.totalPseudofunctor) where
  Fib := fun b => C.totalPseudofunctor.obj ⟨Opposite.op b⟩
  ι := CoGrothendieck.ι C.totalPseudofunctor
  comp_const := CoGrothendieck.comp_const C.totalPseudofunctor
  equiv := fun b => by infer_instance

attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-- The fibrewise covering families contain singleton isomorphisms. -/
@[instance]
theorem totalCoverage_hasIsos (C : SimplicialSite.{u}) :
    C.totalCoverage.HasIsos := by
  with_unfolding_all
    constructor
    intro S T f hf
    let p := CoGrothendieck.forget C.totalPseudofunctor
    let := C.hasFibersForget
    obtain ⟨bS, fiberS⟩ := S
    obtain ⟨bT, fiberT⟩ := T
    let : IsIso f := hf
    have : IsIso f.base := Functor.map_isIso p f
    obtain ⟨hbase, hfbase⟩ := SimplexCategory.exists_eq_eqToHom_of_isIso f.base
    cases hbase
    have hfid : f.base = 𝟙 bS := by simpa using hfbase
    let Φ : (HasFibers.ι (p := p) bS).obj fiberS ≅
        (HasFibers.ι (p := p) bS).obj fiberT :=
      { hom := f
        inv := @CategoryTheory.inv _ _ _ _ f hf
        hom_inv_id := @IsIso.hom_inv_id _ _ _ _ f hf
        inv_hom_id := @IsIso.inv_hom_id _ _ _ _ f hf }
    have hfLift : p.IsHomLift (𝟙 bS) Φ.hom :=
      (show p.map Φ.hom = 𝟙 bS from hfid) ▸ IsHomLift.map (p := p) Φ.hom
    let e := HasFibers.Fib.isoMk (p := p) (Φ := Φ) hfLift
    refine ⟨Presieve.singleton e.hom,
      @Precoverage.HasIsos.mem_coverings_of_isIso _ _ (C.coverage bS.unop)
        (C.coverage_hasIsos bS.unop) fiberS fiberT e.hom e.isIso_hom, ?_⟩
    have hmap : (HasFibers.ι (p := p) bS).map e.hom = Φ.hom := by
      simp only [e]
      exact HasFibers.Fib.map_homMk Φ.hom
    have hmap' : (CoGrothendieck.ι C.totalPseudofunctor bS).map e.hom = f := by
      show (HasFibers.ι (p := p) bS).map e.hom = f
      simpa [Φ] using hmap
    rw [← hmap']
    exact Presieve.map_singleton e.hom

/-- The fibrewise covering families are stable under composition in the total category. -/
@[instance]
theorem totalCoverage_isStableUnderComposition (C : SimplicialSite.{u}) :
    C.totalCoverage.IsStableUnderComposition := by
  with_unfolding_all
    constructor
    rintro ι S X f ⟨R, hR, hR_eq⟩ σ Y g hg
    classical
    let ιS := CoGrothendieck.ι C.totalPseudofunctor S.base
    let p := CoGrothendieck.forget C.totalPseudofunctor
    let := C.hasFibersForget
    have : ιS.Faithful := (inferInstance : (HasFibers.ι (p := p) S.base).Faithful)
    have hobj : Function.Injective ιS.obj := by
      intro U V h
      change ({ base := S.base, fiber := U } : C.totalPseudofunctor.CoGrothendieck) =
        { base := S.base, fiber := V } at h
      exact eq_of_heq (CoGrothendieck.mk.inj h).2
    have houter (i : ι) : ∃ (x : C.totalPseudofunctor.obj ⟨Opposite.op S.base⟩)
        (hx : ιS.obj x = X i) (a : x ⟶ S.fiber), R a ∧
          ιS.map a = eqToHom hx ≫ f i :=
      Presieve.map_iff.mp (hR_eq ▸ ⟨i⟩ : R.map ιS (f i))
    choose x hx a ha hfa using houter
    have hX : X = fun i => ιS.obj (x i) := funext fun i => (hx i).symm
    cases hX
    have hfa' (i : ι) : f i = ιS.map (a i) := by rw [hfa i, eqToHom_refl, Category.id_comp]
    have hR' : R = Presieve.ofArrows x a := by
      apply presieve_map_injective_of_faithful ιS hobj
      rw [hR_eq, funext hfa', Presieve.map_ofArrows]
      rfl
    have hinner (i : ι) : ∃ Ri : Presieve (x i),
        Ri ∈ C.coverage (Opposite.unop S.base) (x i) ∧
          Presieve.map ιS Ri = Presieve.ofArrows (Y i) (g i) := hg i
    choose Ri hRi hRieq using hinner
    have hinnerArrow (i : ι) (j : σ i) :
        ∃ (z : C.totalPseudofunctor.obj ⟨Opposite.op S.base⟩)
          (hz : ιS.obj z = Y i j) (b : z ⟶ x i), Ri i b ∧
            ιS.map b = eqToHom hz ≫ g i j :=
      Presieve.map_iff.mp (hRieq i ▸ ⟨j⟩ : (Ri i).map ιS (g i j))
    choose z hz b hb hgb using hinnerArrow
    have hY : Y = fun i j => ιS.obj (z i j) := funext₂ fun i j => (hz i j).symm
    cases hY
    have hgb' (i : ι) (j : σ i) : g i j = ιS.map (b i j) := by
      rw [hgb i j, eqToHom_refl, Category.id_comp]
    have hRiFamily (i : ι) : Ri i = Presieve.ofArrows (z i) (b i) := by
      apply presieve_map_injective_of_faithful ιS hobj
      rw [hRieq i, Presieve.map_ofArrows, funext (hgb' i)]
    refine ⟨Presieve.ofArrows (fun k : Σ i, σ i => z k.1 k.2) (fun k => b k.1 k.2 ≫ a k.1),
      (C.coverage_isStableUnderComposition S.base.unop).comp_mem_coverings (f := a) (hR' ▸ hR)
        (g := b) (fun i => hRiFamily i ▸ hRi i), ?_⟩
    rw [Presieve.map_ofArrows]
    simp only [ιS, Functor.map_comp, hgb', hfa']
    rfl

end SimplicialSite

end CategoryTheory

end
