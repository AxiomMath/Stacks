module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion

/-!
# Sheaves on the big ph site of an algebraic space

Let `S` be a scheme, `T` a big ph site of algebraic spaces over `S` (Stacks 0DFK) and `X` an
algebraic space of that site. A presheaf of sets on the big ph site of `X` (Stacks 0DFL) is a
sheaf if and only if it satisfies étale descent and descent along every proper surjective
morphism of the site.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleSheafOver` and
  `AlgebraicGeometry.Space.IsProperSurjectiveSheafOver` — the two descent conditions.
* `AlgebraicGeometry.Space.phSpaceCoverage` — the chosen ph covering families of the site,
  packaged as a coverage.

## Main results

* `AlgebraicGeometry.Space.isSheaf_iff_isEtaleSheafOver_and_isProperSurjectiveSheafOver` —
  **Stacks 0DFM**: a presheaf of sets on the big ph site of `X` is a sheaf if and only if it
  satisfies étale descent and descent along every proper surjective morphism of the site.
* `AlgebraicGeometry.Space.isSheaf_of_etale_and_properSurjective` — the sufficiency half of
  **Stacks 0DFM**: étale descent together with proper-surjective descent implies the ph sheaf
  condition.
* `AlgebraicGeometry.Space.isEtaleSheafOver_of_isSheaf` and
  `AlgebraicGeometry.Space.isProperSurjectiveSheafOver_of_isSheaf` — the two clauses of the
  necessity half of **Stacks 0DFM**: a ph sheaf satisfies étale descent, and it satisfies
  descent along every proper surjective morphism of the site.
* `AlgebraicGeometry.Space.generate_presieve₀_mem_topology` and
  `AlgebraicGeometry.Space.isSheafFor_singleton_of_isSheaf` — a ph covering family of the site
  generates a covering sieve, and a ph sheaf therefore satisfies descent along any single
  morphism whose singleton family is a ph covering.

## References

* [Stacks Project, Tag 0DFM](https://stacks.math.columbia.edu/tag/0DFM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (T : BigPHSpaceSite S) (X : T.Spaces)
  (F : (BigPHSpaceOver T X)ᵒᵖ ⥤ Type w)

/-! ### The two descent conditions -/

/-- Étale descent for a presheaf on the big ph site of the algebraic space `X`: the sheaf
condition holds for every family in the slice at `X` whose underlying family of morphisms of
algebraic spaces is an étale covering in the sense of Stacks 041E. -/
def IsEtaleSheafOver : Prop :=
  ∀ (U : BigPHSpaceOver T X) (E : PreZeroHypercover.{u + 2} U),
    IsEtaleCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (E.X i).left.1) (fun i ↦ (E.f i).left.hom) →
    Presieve.IsSheafFor F E.presieve₀

/-- Descent along a proper surjective morphism of the big ph site of the algebraic space `X`:
the sheaf condition holds for the singleton presieve of every morphism of the slice at `X`
whose underlying morphism of algebraic spaces is proper (Stacks 03ZM) and surjective
(Stacks 03ME). -/
def IsProperSurjectiveSheafOver : Prop :=
  ∀ (U V : BigPHSpaceOver T X) (f : V ⟶ U),
    IsProper T.fppfSite S T.fppf_mem f.left.hom →
    IsSurjective T.fppfSite S T.fppf_mem f.left.hom →
    Presieve.IsSheafFor F (Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f))

/-! ### The chosen ph covering families as a coverage -/

/-- The chosen ph covering families of a big ph site of algebraic spaces, packaged as a
coverage. -/
def phSpaceCoverage : Coverage T.Spaces where
  toPrecoverage := T.precoverage
  pullback := by
    intro Y Z f R hR
    obtain ⟨E, rfl, hE⟩ := (T.mem_precoverage_iff).mp hR
    obtain ⟨P, p, q, hpq, hP⟩ := T.isSite.2.2 ⟨Y, E⟩ hE Z f
    refine ⟨Presieve.ofArrows P q, ⟨⟨E.I₀, P, q⟩, rfl, hP⟩, ?_⟩
    rintro W g ⟨i⟩
    exact ⟨E.X i, p i, E.f i, ⟨i⟩, (hpq i).w⟩

/-- The precoverage of a big ph site of algebraic spaces is the one underlying
`AlgebraicGeometry.Space.phSpaceCoverage`. -/
theorem phSpaceCoverage_toPrecoverage :
    (phSpaceCoverage T).toPrecoverage = T.precoverage := rfl

/-! ### Fibre products in the slice -/

/-- The fibre product of two morphisms of the big ph site of `X`, as an object of that site:
the fibre product of algebraic spaces, viewed over `X` through the first projection. -/
noncomputable def slicePullback {U V W : BigPHSpaceOver T X} (f : V ⟶ U) (g : W ⟶ U) :
    BigPHSpaceOver T X :=
  Over.mk ((ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom) :
    AlgebraicSpaces.fiberProduct T.fppfSite S T.fppf_mem f.left g.left ⟶ V.left) ≫ V.hom)

/-- The first projection of `AlgebraicGeometry.Space.slicePullback`. -/
noncomputable def slicePullbackFst {U V W : BigPHSpaceOver T X} (f : V ⟶ U) (g : W ⟶ U) :
    slicePullback T X f g ⟶ V :=
  Over.homMk (ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom)) rfl

/-- The second projection of `AlgebraicGeometry.Space.slicePullback`. -/
noncomputable def slicePullbackSnd {U V W : BigPHSpaceOver T X} (f : V ⟶ U) (g : W ⟶ U) :
    slicePullback T X f g ⟶ W :=
  Over.homMk (ObjectProperty.homMk (pullback.snd f.left.hom g.left.hom)) (by
    change (ObjectProperty.homMk (pullback.snd f.left.hom g.left.hom) :
        AlgebraicSpaces.fiberProduct T.fppfSite S T.fppf_mem f.left g.left ⟶ W.left) ≫ W.hom =
      (ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom) :
        AlgebraicSpaces.fiberProduct T.fppfSite S T.fppf_mem f.left g.left ⟶ V.left) ≫ V.hom
    rw [← g.w, ← f.w, ← Category.assoc, ← Category.assoc,
      (AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem f.left g.left).w])

/-- `AlgebraicGeometry.Space.slicePullback` is a fibre product in the big ph site of `X`. -/
theorem slicePullback_isPullback {U V W : BigPHSpaceOver T X} (f : V ⟶ U) (g : W ⟶ U) :
    IsPullback (slicePullbackFst T X f g) (slicePullbackSnd T X f g) f g :=
  IsPullback.of_map_of_faithful (Over.forget X)
    (AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem f.left g.left)

/-! ### Objects of the big fppf site cut out by a morphism of schemes -/

/-- The object of the big fppf site over `S` determined by a morphism of schemes into the
underlying scheme of a site object, the structure morphism being the composite. -/
abbrev schemeOverOfHom (U : BigFppfOver T.fppfSite S T.fppf_mem) {V : Scheme.{u}}
    (g : V ⟶ (BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj U)
    (hV : T.fppfSite.Contains V) : BigFppfOver T.fppfSite S T.fppf_mem :=
  Over.mk (ObjectProperty.homMk (g ≫ T.fppfSite.inclusion.map U.hom) :
    T.fppfSite.obj hV ⟶ T.fppfSite.obj T.fppf_mem)

/-- The morphism of the big fppf site over `S` underlying
`AlgebraicGeometry.Space.schemeOverOfHom`. -/
abbrev schemeOverOfHomMap (U : BigFppfOver T.fppfSite S T.fppf_mem) {V : Scheme.{u}}
    (g : V ⟶ (BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj U)
    (hV : T.fppfSite.Contains V) : schemeOverOfHom T U g hV ⟶ U :=
  Over.homMk (ObjectProperty.homMk g) rfl

/-! ### Membership in the finest topology for which `F` is a sheaf -/

/-- A sieve covers as soon as some covering family pulls it back to a covering sieve of each
member. -/
private theorem covering_of_pullbacks {C : Type*} [Category C] (J : GrothendieckTopology C)
    {U : C} {I : Type*} {V : I → C} {f : ∀ i, V i ⟶ U}
    (hf : Sieve.ofArrows V f ∈ J U) (R : Sieve U)
    (hR : ∀ i, R.pullback (f i) ∈ J (V i)) : R ∈ J U := by
  refine J.transitive hf R fun W g hg ↦ ?_
  obtain ⟨i, a, rfl⟩ := Sieve.ofArrows.exists hg
  rw [Sieve.pullback_comp]
  exact J.pullback_stable a (hR i)

/-- Raising the index type of a family to a larger universe does not change its presieve. -/
private theorem ofArrows_uliftIndex {C : Type*} [Category C] {U : C} {I : Type v} {V : I → C}
    (f : ∀ i, V i ⟶ U) :
    Presieve.ofArrows (fun i : ULift.{u + 2} I ↦ V i.down) (fun i ↦ f i.down) =
      Presieve.ofArrows V f :=
  Presieve.ofArrows_comp_eq_of_surjective f (a := ULift.down) fun i ↦ ⟨⟨i⟩, rfl⟩

/-- Granted étale descent, an étale covering family of the big ph site of `X` indexed in the
site's own index universe is a covering family for the finest topology for which `F` is a
sheaf. -/
private theorem etale_mem_finestTopology (h₁ : IsEtaleSheafOver T X F)
    {U : BigPHSpaceOver T X} {I : Type (u + 2)} {V : I → BigPHSpaceOver T X} {f : ∀ i, V i ⟶ U}
    (hf : IsEtaleCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (V i).left.1) (fun i ↦ (f i).left.hom)) :
    Sieve.ofArrows V f ∈ Sheaf.finestTopologySingle F U := by
  intro W g
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback f
    fun i ↦ slicePullback_isPullback T X g (f i)]
  refine (Presieve.isSheafFor_iff_generate _).mp (h₁ W
    ⟨I, fun i ↦ slicePullback T X g (f i), fun i ↦ slicePullbackFst T X g (f i)⟩ ?_)
  exact isEtaleCovering_pullback T.fppfSite S T.fppf_mem g.left.hom W.left.property
    (fun i ↦ (V i).left.1) (fun i ↦ (f i).left.hom) hf

/-- Granted étale descent, an étale covering family of the big ph site of `X` indexed in
`Type u` is a covering family for the finest topology for which `F` is a sheaf. -/
private theorem etale_mem_finestTopology_small (h₁ : IsEtaleSheafOver T X F)
    {U : BigPHSpaceOver T X} {I : Type u} {V : I → BigPHSpaceOver T X} {f : ∀ i, V i ⟶ U}
    (hf : IsEtaleCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (V i).left.1) (fun i ↦ (f i).left.hom)) :
    Sieve.ofArrows V f ∈ Sheaf.finestTopologySingle F U := by
  change Sieve.generate (Presieve.ofArrows V f) ∈ _
  rw [← ofArrows_uliftIndex.{u} f]
  refine etale_mem_finestTopology T X F h₁
    ⟨hf.target_isAlgebraicSpace, fun i ↦ hf.source_isAlgebraicSpace i.down,
      fun i ↦ hf.etale i.down, Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.jointly_surjective x)
  exact Set.mem_iUnion.mpr ⟨ULift.up i, hi⟩

/-- Granted proper-surjective descent, the singleton family of a proper surjective morphism of
the big ph site of `X` is a covering family for the finest topology for which `F` is a sheaf. -/
private theorem properSurjective_mem_finestTopology (h₂ : IsProperSurjectiveSheafOver T X F)
    {U V : BigPHSpaceOver T X} {f : V ⟶ U}
    (hp : IsProper T.fppfSite S T.fppf_mem f.left.hom)
    (hs : IsSurjective T.fppfSite S T.fppf_mem f.left.hom) :
    Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f) ∈ Sheaf.finestTopologySingle F U := by
  intro W g
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback (fun _ : Unit ↦ f)
    fun _ ↦ slicePullback_isPullback T X g f]
  refine (Presieve.isSheafFor_iff_generate _).mp
    (h₂ W (slicePullback T X g f) (slicePullbackFst T X g f) ?_ ?_)
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := properProperty T.fppfSite S T.fppf_mem)
      (AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem g.left f.left).flip hp
  · exact isSurjective_of_isPullback T.fppfSite S T.fppf_mem
      (AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem g.left f.left).flip hs

/-- **A standard ph covering of an affine object of the big fppf site is a covering family for
the finest topology for which `F` is a sheaf**, over any point of `X` with that object as
source. -/
private theorem standardPH_mem_finestTopology (h₁ : IsEtaleSheafOver T X F)
    (h₂ : IsProperSurjectiveSheafOver T X F)
    (U : BigFppfOver T.fppfSite S T.fppf_mem)
    [IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj U)]
    (a : (schemeSpaceFunctor T.fppfSite S T.fppf_mem).obj U ⟶ X)
    (E : PreZeroHypercover.{u} U)
    (hE : StandardPHCovering (E.map (BigFppfOver.toScheme T.fppfSite S T.fppf_mem)).f) :
    Sieve.ofArrows (X := Over.mk a)
      (fun i ↦ Over.mk ((schemeSpaceFunctor T.fppfSite S T.fppf_mem).map (E.f i) ≫ a))
      (fun i ↦ Over.homMk ((schemeSpaceFunctor T.fppfSite S T.fppf_mem).map (E.f i)) rfl) ∈
      Sheaf.finestTopologySingle F (Over.mk a) := by
  let B := T.fppfSite
  let q := BigFppfOver.toScheme B S T.fppf_mem
  let A := schemeSpaceFunctor B S T.fppf_mem
  obtain ⟨W, g, j, hg, hs, hj, hcov, hcomp⟩ := hE.exists_presentation
  have _ : _root_.AlgebraicGeometry.IsProper g := hg
  have hW : B.Contains W :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g U.left.property
  let W' := schemeOverOfHom T U g hW
  let g' : W' ⟶ U := schemeOverOfHomMap T U g hW
  let j' : ∀ i, E.X i ⟶ W' := fun i ↦
    Over.homMk (ObjectProperty.homMk (j i)) (by
      apply B.inclusion.map_injective
      change j i ≫ g ≫ B.inclusion.map U.hom = B.inclusion.map (E.X i).hom
      rw [← Category.assoc, hcomp i]
      exact congrArg (fun m ↦ B.inclusion.map m) (E.f i).w)
  have hjcomp : ∀ i, j' i ≫ g' = E.f i := fun i ↦ q.map_injective (hcomp i)
  let f' : Over.mk (A.map g' ≫ a) ⟶ Over.mk a := Over.homMk (A.map g') rfl
  let k : ∀ i, Over.mk (A.map (E.f i) ≫ a) ⟶ Over.mk (A.map g' ≫ a) := fun i ↦
    Over.homMk (A.map (j' i)) (by
      change A.map (j' i) ≫ A.map g' ≫ a = A.map (E.f i) ≫ a
      rw [← Category.assoc, ← A.map_comp, hjcomp i])
  have hk : IsEtaleCovering B S T.fppf_mem
      (fun i ↦ (Over.mk (A.map (E.f i) ≫ a)).left.1) (fun i ↦ (k i).left.hom) :=
    isEtaleCovering_yoneda_of_etale B S T.fppf_mem E.X j'
      (fun i ↦ by
        have _ : _root_.AlgebraicGeometry.IsOpenImmersion (j i) := hj i
        exact inferInstanceAs (_root_.AlgebraicGeometry.Etale (j i)))
      (fun x ↦ Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov x))
  refine covering_of_pullbacks _
    (properSurjective_mem_finestTopology T X F h₂ (f := f')
      (isProper_yoneda_map B S T.fppf_mem g' hg)
      (isSurjective_yoneda_map B S T.fppf_mem g' hs)) _ fun _ ↦ ?_
  refine (Sheaf.finestTopologySingle F).superset_covering ?_
    (etale_mem_finestTopology_small T X F h₁ (f := k) hk)
  rw [Sieve.generate_le_iff]
  rintro Z z ⟨i⟩
  change Sieve.ofArrows _ _ (k i ≫ f')
  have heq : k i ≫ f' = Over.homMk (A.map (E.f i)) rfl :=
    Over.OverMorphism.ext ((A.map_comp (j' i) g').symm.trans (congrArg A.map (hjcomp i)))
  rw [heq]
  exact Sieve.ofArrows_mk _ _ i

/-- **A sieve of the big ph site of `X` covers as soon as it covers over every object
represented by an affine scheme of the big fppf site**, for the finest topology for which `F` is
a sheaf, granted étale descent. -/
private theorem covering_of_affine_pullbacks (h₁ : IsEtaleSheafOver T X F)
    (U : BigPHSpaceOver T X) (R : Sieve U)
    (hR : ∀ (V : BigFppfOver T.fppfSite S T.fppf_mem)
      [IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V)]
      (a : (schemeSpaceFunctor T.fppfSite S T.fppf_mem).obj V ⟶ U.left),
      R.pullback (Over.homMk a rfl : Over.mk (a ≫ U.hom) ⟶ U) ∈
        Sheaf.finestTopologySingle F (Over.mk (a ≫ U.hom))) :
    R ∈ Sheaf.finestTopologySingle F U := by
  let B := T.fppfSite
  let A := schemeSpaceFunctor B S T.fppf_mem
  obtain ⟨V, a, haSurj, haEtale⟩ := U.left.property.exists_atlas
  let a' : A.obj V ⟶ U.left := ObjectProperty.homMk a
  let f : Over.mk (a' ≫ U.hom) ⟶ U := Over.homMk a' rfl
  have hf : IsEtaleCovering B S T.fppf_mem
      (fun _ : ULift.{u + 2} Unit ↦ (A.obj V).1) (fun _ ↦ a) := by
    refine ⟨U.left.property, fun _ ↦ (A.obj V).property,
      fun _ ↦ (isEtale_iff_presheaf_of_yoneda B S T.fppf_mem a).2 haEtale, ?_⟩
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.mpr ((presheafSurjective_iff_isSurjective_yoneda B S T.fppf_mem
      U.left.1 U.left.property V a).mp haSurj)
  refine covering_of_pullbacks _
    (etale_mem_finestTopology T X F h₁ (f := fun _ : ULift.{u + 2} Unit ↦ f) hf) R fun _ ↦ ?_
  obtain ⟨I, V', c, hV'affine, hV'cover⟩ :=
    exists_affine_isEtaleCovering_yoneda B S T.fppf_mem V
  let b : ∀ i, A.obj (V' i) ⟶ U.left := fun i ↦ A.map (c i) ≫ a'
  let k : ∀ i, (Over.mk (b i ≫ U.hom) : BigPHSpaceOver T X) ⟶ Over.mk (a' ≫ U.hom) := fun i ↦
    Over.homMk (A.map (c i)) (by
      change A.map (c i) ≫ a' ≫ U.hom = (A.map (c i) ≫ a') ≫ U.hom
      rw [Category.assoc])
  have hk : IsEtaleCovering B S T.fppf_mem
      (fun i ↦ (Over.mk (b i ≫ U.hom) : BigPHSpaceOver T X).left.1)
      (fun i ↦ (k i).left.hom) := hV'cover
  refine covering_of_pullbacks _
    (etale_mem_finestTopology_small T X F h₁ (f := k) hk) _ fun i ↦ ?_
  rw [← Sieve.pullback_comp]
  have _ : IsAffine ((BigFppfOver.toScheme B S T.fppf_mem).obj (V' i)) := hV'affine i
  exact hR (V' i) (b i)

/-- **Granted étale and proper-surjective descent, every ph covering family of the big ph site
of `X` is a covering family for the finest topology for which `F` is a sheaf.** -/
private theorem ph_mem_finestTopology (h₁ : IsEtaleSheafOver T X F)
    (h₂ : IsProperSurjectiveSheafOver T X F)
    (U : BigPHSpaceOver T X) (E : PreZeroHypercover.{u + 2} U)
    (hE : IsPHCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (E.X i).left.1) (fun i ↦ (E.f i).left.hom)) :
    Sieve.ofArrows E.X E.f ∈ Sheaf.finestTopologySingle F U := by
  refine covering_of_affine_pullbacks T X F h₁ U _ fun V hV a ↦ ?_
  obtain ⟨D, hD, ⟨r⟩⟩ := hE.affine_refinement V a.hom
  refine (Sheaf.finestTopologySingle F).superset_covering ?_
    (standardPH_mem_finestTopology T X F h₁ h₂ V (a ≫ U.hom) D hD)
  rw [Sieve.generate_le_iff]
  rintro Z z ⟨i⟩
  let b : (Over.mk ((schemeSpaceFunctor T.fppfSite S T.fppf_mem).map (D.f i) ≫ a ≫ U.hom) :
      BigPHSpaceOver T X) ⟶ E.X (r.s₀ i) :=
    Over.homMk (ObjectProperty.homMk (r.h₀ i)) (by
      apply ObjectProperty.hom_ext
      change r.h₀ i ≫ (E.X (r.s₀ i)).hom.hom =
        yoneda.map (D.f i) ≫ a.hom ≫ U.hom.hom
      have hw : (E.f (r.s₀ i)).left.hom ≫ U.hom.hom = (E.X (r.s₀ i)).hom.hom :=
        congrArg (fun z ↦ z.hom) (E.f (r.s₀ i)).w
      have hr : r.h₀ i ≫ (E.f (r.s₀ i)).left.hom = yoneda.map (D.f i) ≫ a.hom := r.w₀ i
      rw [← hw, ← Category.assoc, hr]
      exact Category.assoc (yoneda.map (D.f i)) a.hom U.hom.hom)
  change Sieve.ofArrows E.X E.f _
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr
    ⟨r.s₀ i, b, Over.OverMorphism.ext (ObjectProperty.hom_ext _ (r.w₀ i).symm)⟩

/-! ### The sufficiency half of Stacks 0DFM -/

/-- The sieve on an object `U` of the big ph site of `X` cut out, through the bijection between
sieves on `U` and sieves on its underlying algebraic space, by the sieve generated by a
covering family of that algebraic space: it is generated by the same family, each member
regarded over `X` through its composite with the structure morphism of `U`. -/
private theorem overEquiv_symm_generate_presieve₀ {U : BigPHSpaceOver T X}
    (E : PreZeroHypercover.{u + 2} U.left) :
    (Sieve.overEquiv U).symm (Sieve.generate E.presieve₀) =
      Sieve.ofArrows (fun i ↦ (Over.mk (E.f i ≫ U.hom) : BigPHSpaceOver T X))
        (fun i ↦ (Over.homMk (E.f i) : Over.mk (E.f i ≫ U.hom) ⟶ U)) := by
  ext Z g
  rw [Sieve.overEquiv_symm_iff]
  constructor
  · rintro ⟨W, p, c, ⟨i⟩, hpc⟩
    refine ⟨Over.mk (E.f i ≫ U.hom), Over.homMk p ?_, Over.homMk (E.f i), ⟨i⟩, ?_⟩
    · change p ≫ E.f i ≫ U.hom = Z.hom
      rw [← Category.assoc, hpc]
      exact Over.w g
    · exact Over.OverMorphism.ext hpc
  · rintro ⟨W, p, c, ⟨i⟩, hpc⟩
    exact ⟨E.X i, p.left, E.f i, ⟨i⟩, congrArg Over.Hom.left hpc⟩

/-- A presheaf of sets on the big ph site of an algebraic space `X` of a big ph site of
algebraic spaces is a sheaf as soon as it satisfies étale descent and descent along every proper
surjective morphism of the site. -/
@[stacks 0DFM
  "sufficiency: etale descent plus proper-surjective descent imply the ph sheaf condition"]
theorem isSheaf_of_etale_and_properSurjective (h₁ : IsEtaleSheafOver T X F)
    (h₂ : IsProperSurjectiveSheafOver T X F) :
    Presieve.IsSheaf (BigPHSpaceOver.topology T X) F := by
  have hle : BigPHSpaceOver.topology T X ≤ Sheaf.finestTopologySingle F := by
    change T.precoverage.toGrothendieck.over X ≤ _
    rw [← phSpaceCoverage_toPrecoverage T, Coverage.toGrothendieck_toPrecoverage]
    refine over_le_of_coverage (phSpaceCoverage T) X _ fun U R hR ↦ ?_
    obtain ⟨E, rfl, hE⟩ := (T.mem_precoverage_iff).mp hR
    rw [overEquiv_symm_generate_presieve₀ T X E]
    exact ph_mem_finestTopology T X F h₁ h₂ U
      ⟨E.I₀, fun i ↦ Over.mk (E.f i ≫ U.hom), fun i ↦ Over.homMk (E.f i)⟩ hE.ph
  intro U R hR
  simpa using hle U hR U (𝟙 U)

/-! ### The necessity half of Stacks 0DFM -/

/-- The index type of a ph covering may be raised to a larger universe. -/
private theorem isPHCovering_uliftIndex {I : Type v}
    {Y : (BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u}
    {Z : I → (BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u} {g : ∀ i, Z i ⟶ Y}
    (h : IsPHCovering T.fppfSite S T.fppf_mem Z g) :
    IsPHCovering T.fppfSite S T.fppf_mem (fun i : ULift.{u + 2} I ↦ Z i.down)
      (fun i ↦ g i.down) := by
  refine ⟨h.target_isAlgebraicSpace, fun i ↦ h.source_isAlgebraicSpace i.down,
    fun i ↦ h.locallyOfFiniteType i.down, fun W _ a ↦ ?_⟩
  obtain ⟨E, hE, ⟨φ⟩⟩ := h.affine_refinement W a
  exact ⟨E, hE, ⟨⟨fun q ↦ ⟨φ.s₀ q⟩, φ.h₀, φ.w₀⟩⟩⟩

/-- **A family of the big ph site of `X` whose underlying family of morphisms of algebraic
spaces is a ph covering generates a covering sieve.** -/
theorem generate_presieve₀_mem_topology {U : BigPHSpaceOver T X}
    (E : PreZeroHypercover.{u + 2} U)
    (hE : IsPHCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (E.X i).left.1) (fun i ↦ (E.f i).left.hom)) :
    Sieve.generate E.presieve₀ ∈ BigPHSpaceOver.topology T X U := by
  obtain ⟨⟨V, G⟩, hG, hbase, hcomb⟩ :=
    T.covering_representative ⟨U.left, E.map (Over.forget X)⟩ hE
  change U.left = V at hbase
  subst hbase
  have hpres : (E.map (Over.forget X)).presieve₀ = G.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv U (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  change Sieve.generate (E.map (Over.forget X)).presieve₀ ∈ _
  rw [hpres]
  exact Precoverage.generate_mem_toGrothendieck ((T.mem_precoverage_iff).2 ⟨G, rfl, hG⟩)

/-- **A sheaf on the big ph site of `X` satisfies descent along a single morphism of the site
whose singleton family is a ph covering.** -/
theorem isSheafFor_singleton_of_isSheaf (h : Presieve.IsSheaf (BigPHSpaceOver.topology T X) F)
    {U V : BigPHSpaceOver T X} (f : V ⟶ U)
    (hf : IsPHCovering T.fppfSite S T.fppf_mem
      (fun _ : Unit ↦ V.left.1) (fun _ ↦ f.left.hom)) :
    Presieve.IsSheafFor F (Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f)) := by
  rw [← ofArrows_uliftIndex.{u} (fun _ : Unit ↦ f)]
  exact (Presieve.isSheafFor_iff_generate _).2
    (h _ (generate_presieve₀_mem_topology T X
      ⟨ULift.{u + 2} Unit, fun _ ↦ V, fun _ ↦ f⟩ (isPHCovering_uliftIndex T hf)))

/-- A sheaf of sets on the big ph site of an algebraic space `X` of a big ph site of algebraic
spaces satisfies étale descent. -/
@[stacks 0DFM "necessity, etale descent: a ph sheaf satisfies etale descent"]
theorem isEtaleSheafOver_of_isSheaf (h : Presieve.IsSheaf (BigPHSpaceOver.topology T X) F) :
    IsEtaleSheafOver T X F := fun _ E hE ↦
  (Presieve.isSheafFor_iff_generate E.presieve₀).2
    (h _ (generate_presieve₀_mem_topology T X E
      (isPHCovering_of_isEtaleCovering T.fppfSite S T.fppf_mem hE)))

/-- A sheaf of sets on the big ph site of an algebraic space `X` of a big ph site of algebraic
spaces satisfies descent along every proper surjective morphism of the site. -/
@[stacks 0DFM "necessity, proper-surjective descent: a ph sheaf satisfies descent along every \
proper surjective morphism of the site"]
theorem isProperSurjectiveSheafOver_of_isSheaf
    (h : Presieve.IsSheaf (BigPHSpaceOver.topology T X) F) :
    IsProperSurjectiveSheafOver T X F := fun U V f hp hs ↦
  isSheafFor_singleton_of_isSheaf T X F h f
    (isPHCovering_of_isProper_isSurjective T.fppfSite S T.fppf_mem f.left.hom
      U.left.property V.left.property hp hs)

/-! ### Stacks 0DFM -/

/-- A presheaf of sets on the big ph site of an algebraic space `X` of a big ph site of
algebraic spaces is a sheaf if and only if it satisfies étale descent and descent along every
proper surjective morphism of the site. -/
@[stacks 0DFM "the biconditional"]
theorem isSheaf_iff_isEtaleSheafOver_and_isProperSurjectiveSheafOver :
    Presieve.IsSheaf (BigPHSpaceOver.topology T X) F ↔
      IsEtaleSheafOver T X F ∧ IsProperSurjectiveSheafOver T X F :=
  ⟨fun h ↦ ⟨isEtaleSheafOver_of_isSheaf T X F h,
      isProperSurjectiveSheafOver_of_isSheaf T X F h⟩,
    fun h ↦ isSheaf_of_etale_and_properSurjective T X F h.1 h.2⟩

end AlgebraicGeometry.Space

end
