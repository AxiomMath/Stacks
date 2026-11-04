module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.Identity

/-!
# The constant simplicial site on the point

The simplicial site of case (A) of Stacks 09WE whose component in every degree is the point, the
category with one object and one morphism, with the topology in which a sieve covers only if it is
maximal, and whose transitions are the identity functor. Its total site has the simplex category as
underlying category, and again only maximal sieves cover, so a sheaf on it is any presheaf. A
cosimplicial commutative ring therefore defines a sheaf of rings on its total site.

## Main definitions

* `CategoryTheory.PointSimplicialSite.coverage`: the coverage of the point by nonempty families.
* `CategoryTheory.PointSimplicialSite.simplicialSite`: the constant simplicial site on the point.
* `CategoryTheory.PointSimplicialSite.situation`: it, as a simplicial-site situation.
* `CategoryTheory.PointSimplicialSite.ringSheaf`: the sheaf of rings on the total site attached to
  a cosimplicial commutative ring.

## Main results

* `CategoryTheory.PointSimplicialSite.toGrothendieck_coverage`: the topology of the point is the
  trivial one.
* `CategoryTheory.PointSimplicialSite.totalTopology_eq_bot`: so is the topology of the total site.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

namespace PointSimplicialSite

noncomputable section

/-- The point: one object, one morphism. -/
abbrev Pt : Type u := Discrete PUnit.{u + 1}

/-- The object of the point. -/
def pt : Pt.{u} := ⟨PUnit.unit⟩

/-- The point has exactly one object. -/
instance subsingleton_pt : Subsingleton Pt.{u} :=
  ⟨fun ⟨⟨⟩⟩ ⟨⟨⟩⟩ => rfl⟩

/-- The point has at most one morphism between any two objects. -/
instance subsingleton_hom (X Y : Pt.{u}) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => by cases f; cases g; rfl⟩

/-- A morphism between any two objects of the point. -/
def homOf (X Y : Pt.{u}) : X ⟶ Y := eqToHom (Subsingleton.elim X Y)

/-- The coverage of the point: the nonempty families. -/
def coverage : Precoverage Pt.{u} where
  coverings X := {R | ∃ (Y : Pt.{u}) (f : Y ⟶ X), R f}

/-- An isomorphism of the point, as a one-member family, is a covering family. -/
instance coverage_hasIsos : coverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ := ⟨_, f, Presieve.singleton.mk⟩

/-- Two morphisms of the point with a common target have a pullback. -/
instance hasPullback_pt {X Y Z : Pt.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨⟨PullbackCone.mk (homOf X X) (homOf X Y) (Subsingleton.elim _ _),
    PullbackCone.IsLimit.mk _ (fun _ => homOf _ _) (fun _ => Subsingleton.elim _ _)
      (fun _ => Subsingleton.elim _ _) (fun _ _ _ _ => Subsingleton.elim _ _)⟩⟩⟩

/-- The coverage of the point has pullbacks of its covering families. -/
instance coverage_hasPullbacks : coverage.{u}.HasPullbacks where
  hasPullbacks_of_mem _ _ := ⟨fun _ => inferInstance⟩

/-- The base change of a nonempty family on the point is nonempty. -/
instance coverage_isStableUnderBaseChange : coverage.{u}.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι S X} f hf Y g P p₁ p₂ _ := by
    obtain ⟨Z, h, ⟨i⟩⟩ := hf
    exact ⟨_, p₁ i, Presieve.ofArrows.mk i⟩

/-- The composite of nonempty families on the point is nonempty. -/
instance coverage_isStableUnderComposition : coverage.{u}.IsStableUnderComposition where
  comp_mem_coverings {ι S X} f hf σ Y g hg := by
    obtain ⟨Z, h, ⟨i⟩⟩ := hf
    obtain ⟨W, k, ⟨j⟩⟩ := hg i
    exact ⟨_, _, Presieve.ofArrows.mk (ι := Σ i, σ i) ⟨i, j⟩⟩

/-- A nonempty family on the point generates the maximal sieve. -/
theorem generate_eq_top {X : Pt.{u}} {R : Presieve X} (hR : R ∈ coverage.{u}.coverings X) :
    Sieve.generate R = ⊤ := by
  obtain ⟨Y, f, hf⟩ := hR
  rw [← Sieve.id_mem_iff_eq_top]
  exact ⟨Y, homOf X Y, f, hf, Subsingleton.elim _ _⟩

/-- The topology of the point is the trivial topology. -/
theorem toGrothendieck_coverage : coverage.{u}.toGrothendieck = ⊥ := by
  refine le_antisymm (Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2 ?_) bot_le
  intro X R hR
  show Sieve.generate R ∈ (⊥ : GrothendieckTopology Pt.{u}) X
  rw [generate_eq_top hR]
  exact GrothendieckTopology.top_mem _ _

/-- The constant cosimplicial diagram of categories on the point. -/
abbrev underlying : SimplexCategory ⥤ Cat.{u, u} := (Functor.const _).obj (Cat.of Pt.{u})

/-- Every transition of the constant diagram on the point is the identity functor. -/
theorem underlying_map_toFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    (underlying.{u}.map φ).toFunctor = 𝟭 Pt.{u} := rfl

/-- The constant simplicial site on the point, in case (A) of Stacks 09WE. -/
def simplicialSite : SimplicialSite.{u} where
  underlying := underlying.{u}
  coverage _ := coverage.{u}
  coverage_hasIsos _ := coverage_hasIsos
  coverage_hasPullbacks _ := coverage_hasPullbacks
  coverage_isStableUnderBaseChange _ := coverage_isStableUnderBaseChange
  coverage_isStableUnderComposition _ := coverage_isStableUnderComposition
  isMorphismOfSites _ := Functor.isMorphismOfSites_id _
  coverPreserving _ _ R hR := by
    obtain ⟨Y, f, hf⟩ := hR
    exact ⟨Y, f, Presieve.map.of hf⟩
  preservesPullbacks := by
    intros
    rw [underlying_map_toFunctor]
    exact preservesPullback_symmetry (𝟭 _) _ _

/-- The constant simplicial site on the point, as a simplicial-site situation. -/
def situation : SimplicialSiteSituation.{u} := ⟨Sum.inl simplicialSite.{u}⟩

/-- The topology of each component is the trivial one. -/
theorem componentTopology_eq_bot (n : SimplexCategory) :
    situation.{u}.componentTopology n = ⊥ :=
  toGrothendieck_coverage

/-- The topology of the total site is the trivial one. -/
theorem totalTopology_eq_bot : situation.{u}.totalTopology = ⊥ := by
  refine le_antisymm (Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2 ?_) bot_le
  rintro U R ⟨S, ⟨Y, f, hf⟩, rfl⟩
  let ι := Pseudofunctor.CoGrothendieck.ι simplicialSite.{u}.totalPseudofunctor U.base
  have h : homOf U.fiber Y ≫ f = 𝟙 U.fiber :=
    (subsingleton_hom.{u} U.fiber U.fiber).elim _ _
  have e : ι.map (homOf U.fiber Y) ≫ ι.map f = 𝟙 (ι.obj U.fiber) :=
    (ι.map_comp _ _).symm.trans ((congrArg ι.map h).trans (ι.map_id _))
  exact GrothendieckTopology.bot_covering.2
    (Sieve.id_mem_iff_eq_top.1 ⟨_, ι.map (homOf U.fiber Y), ι.map f, Presieve.map.of hf, e⟩)

/-- Every presheaf on the total site is a sheaf. -/
theorem isSheaf_total {A : Type*} [Category A] (P : situation.{u}.totalCategoryᵒᵖ ⥤ A) :
    Presheaf.IsSheaf situation.{u}.totalTopology P := by
  rw [totalTopology_eq_bot]
  exact Presheaf.isSheaf_bot P

/-- Every presheaf on a component is a sheaf. -/
theorem isSheaf_component {A : Type*} [Category A] (n : SimplexCategory)
    (P : (situation.{u}.component n)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (situation.{u}.componentTopology n) P := by
  rw [componentTopology_eq_bot]
  exact Presheaf.isSheaf_bot P

/-- The presheaf of rings on the total site attached to a cosimplicial commutative ring: its value
on the object of degree `n` is the ring in degree `n`. -/
def ringPresheaf (A : SimplexCategory ⥤ CommRingCat.{u}) :
    situation.{u}.totalCategoryᵒᵖ ⥤ CommRingCat.{u} :=
  (situation.{u}.totalSimplexDegree).op ⋙ unopUnop SimplexCategory ⋙ A

/-- The sheaf of rings on the total site attached to a cosimplicial commutative ring. -/
def ringSheaf (A : SimplexCategory ⥤ CommRingCat.{u}) :
    Sheaf situation.{u}.totalTopology CommRingCat.{u} :=
  ⟨ringPresheaf A, isSheaf_total _⟩

end

end PointSimplicialSite

end CategoryTheory

end
