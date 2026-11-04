module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.SetTheory.Cardinal.Regular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDiagonalQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction

/-!
# Embedding an affine scheme into affine space over an algebraic space

An affine scheme `U` locally of finite type over a locally separated algebraic space `X`
admits an immersion into a relative affine space `𝔸ⁿ_X`.  Writing `U = Spec A` and `A` as the
filtered union of its finite type `ℤ`-subalgebras `Aᵢ`, the morphism `U ⟶ X ⨯ U` is the graph
of `f`, hence an immersion because `X` is locally separated; the system `X ⨯ Spec Aᵢ` has
limit `X ⨯ U` with affine transition morphisms, so `U ⟶ X ⨯ Spec Aᵢ` is already an immersion
for some `i`; and `Spec Aᵢ` is a closed subscheme of affine space over `ℤ`.

## Main results

* `AlgebraicGeometry.Space.exists_isImmersion_affineSpaceOver_of_isAbsolutelyQuasiSeparated`
  is **Stacks 088L**, under exactly its hypotheses: `X` quasi-separated and locally separated.
* `AlgebraicGeometry.Space.exists_isImmersion_affineSpaceOver` is the variant which drops
  quasi-separatedness of `X` at the price of the cardinality side condition below.
* `AlgebraicGeometry.Space.exists_isImmersion_affineSpaceOver_of_isRegular` is that variant
  over a big fppf site whose cutoff is a regular cardinal, where the cardinality side
  condition is automatic.

## Implementation notes

Stacks 088L carries no cardinality hypothesis, and neither does its formalization
`exists_isImmersion_affineSpaceOver_of_isAbsolutelyQuasiSeparated`: there the stages
`X ⨯ Spec Aᵢ` are quasi-separated because `X` is, and Stacks 0828, part (2)
(`AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ`) places no bound on the index
set of a directed system with quasi-separated stages.  This is the route of the Stacks proof.

The variant `exists_isImmersion_affineSpaceOver` does not assume `X` quasi-separated, which
Stacks 088M leaves open.  The hypothesis `hcard` there, that the ring of
sections of `U` is smaller than the cofinality of the site's cutoff, is an artifact of the
`AlgebraicGeometry.BigFppfSite` framework: the proof passes through a directed limit of
algebraic spaces, and both Stacks 07SF (`AlgebraicGeometry.Space.isAlgebraicSpace_limit`, which
is what makes such a limit an algebraic space) and the eventual immersion for stages which need
not be quasi-separated (`AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ_of_small`)
bound the index type by that cofinality.  The hypothesis cannot be removed by a better
choice of approximating system: a finite type `ℤ`-algebra is countable, so any directed system
of them with union `A` is indexed by a set of cardinality at least `#A`.  Nor can it be derived
from `B.Contains (Spec A)`, which gives only `#A < B.cutoff`: a big fppf site may have
`cutoff = ℶ_{ω₁}`, which is an uncountable strong prelimit of uncountable cofinality `ℵ₁`,
while `#A = ℶ_ω` satisfies `(Spec A).size < ℶ_{ω₁}` and exceeds `ℵ₁`.  That a bare
`#I < B.cutoff` cannot be upgraded to `#I < B.cutoff.ord.cof` is recorded in this development
at `StacksFrontier/AlgebraicGeometry/Descent/AffineBaseCoveringSieveDescent.lean:60-64`, together
with the three sanctioned ways around it at `:72-75`; regularity of the cutoff is the first of
them, and is the form the corollary takes.

The hypothesis `hZ` is not a restriction: it is part of the vocabulary of Stacks 03BS, which
defines "locally separated" for an algebraic space by relocalizing over the terminal scheme,
and `AlgebraicGeometry.BigFppfSite.contains_terminal` discharges it for every big fppf site.
Stacks 088W, the counterexample showing that local separatedness cannot be dropped, carries
it in the same place.

## References

* [Stacks Project, Tag 088L](https://stacks.math.columbia.edu/tag/088L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal Opposite
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Immersions of schemes respect isomorphisms, being stable under base change. -/
private theorem respectsIso_isImmersion :
    MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

attribute [local instance] respectsIso_isImmersion

/-! ### Scheme-level preliminaries for the site -/

/-- A property of schemes stable under base change remains so after pulling it back along
the forgetful functor from the objects of a big fppf site over `S`. -/
private abbrev schemeProperty_baseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange where
  of_isPullback sq hp := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (sq.map (BigFppfOver.toScheme B S hS)) hp

attribute [local instance] schemeProperty_baseChange

/-- The spectrum of a polynomial ring in finitely many variables over a ring whose spectrum
lies in a big fppf site lies in that site. -/
private theorem polynomialSpectrum_size_lt (B : BigFppfSite.{u}) (R : Type u) [CommRing R]
    (n : ℕ) (hR : (Spec (.of R)).size < B.cutoff) :
    (Spec (.of (MvPolynomial (ULift.{u} (Fin n)) R))).size < B.cutoff :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    R (MvPolynomial (ULift.{u} (Fin n)) R) hR

/-! ### Products with a fixed factor -/

section ProdDiagram

variable {C : Type*} [Category C] [HasBinaryProducts C] {J : Type*} [Category J]

/-- The product of a fixed object with a diagram. -/
@[reducible, simps]
private noncomputable def prodDiagram (X : C) (E : J ⥤ C) : J ⥤ C where
  obj j := X ⨯ E.obj j
  map f := prod.map (𝟙 X) (E.map f)
  map_id j := by simp
  map_comp f g := by simp [prod.map_map]

/-- The first projections out of the product diagram, as a natural transformation to the
constant diagram at the fixed factor. -/
@[reducible, simps]
private noncomputable def prodDiagramFst (X : C) (E : J ⥤ C) :
    prodDiagram X E ⟶ (Functor.const J).obj X where
  app _ := prod.fst
  naturality i j f := by simp

/-- The second projections out of the product diagram, as a natural transformation to the
diagram itself. -/
@[reducible, simps]
private noncomputable def prodDiagramSnd (X : C) (E : J ⥤ C) : prodDiagram X E ⟶ E where
  app _ := prod.snd
  naturality i j f := by simp

/-- The product of a fixed object with a cone. -/
@[reducible, simps]
private noncomputable def prodCone (X : C) {E : J ⥤ C} (c : Cone E) :
    Cone (prodDiagram X E) where
  pt := X ⨯ c.pt
  π :=
    { app := fun j => prod.map (𝟙 X) (c.π.app j)
      naturality := fun i j f => by simp [prod.map_map] }

/-- The first components of a cone over a product diagram agree along any morphism of the
index category. -/
private theorem prodCone_fst_eq_of_hom (X : C) (E : J ⥤ C) (s : Cone (prodDiagram X E))
    {i j : J} (f : i ⟶ j) : s.π.app j ≫ prod.fst = s.π.app i ≫ prod.fst := by
  rw [← s.w f, prodDiagram_map, Category.assoc, prod.map_fst, Category.comp_id]

/-- **Taking the product with a fixed object preserves a limit whose first components are
constant.**  The second components form a cone on the original diagram, and the first
components, being all equal, are determined by the value at `j₀`. -/
private noncomputable def prodCone_isLimit (X : C) {E : J ⥤ C} {c : Cone E} (hc : IsLimit c)
    (j₀ : J) (hfst : ∀ (s : Cone (prodDiagram X E)) (j : J),
      s.π.app j₀ ≫ prod.fst = s.π.app j ≫ prod.fst) :
    IsLimit (prodCone X c) := by
  let d (s : Cone (prodDiagram X E)) : Cone E :=
    { pt := s.pt, π := s.π ≫ prodDiagramSnd X E }
  refine IsLimit.mk (fun s ↦ prod.lift (s.π.app j₀ ≫ prod.fst) (hc.lift (d s))) ?_ ?_
  · intro s j
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prodCone_π_app, prod.map_fst, Category.comp_id, prod.lift_fst]
      exact hfst s j
    · rw [Category.assoc, prodCone_π_app, prod.map_snd, ← Category.assoc, prod.lift_snd]
      exact hc.fac (d s) j
  · intro s m hm
    refine prod.hom_ext ?_ ?_
    · rw [prod.lift_fst]
      have h : (m ≫ (prodCone X c).π.app j₀) ≫ prod.fst = s.π.app j₀ ≫ prod.fst :=
        congrArg (· ≫ prod.fst) (hm j₀)
      rwa [Category.assoc, prodCone_π_app, prod.map_fst, Category.comp_id] at h
    · rw [prod.lift_snd]
      refine hc.hom_ext fun j ↦ ?_
      rw [hc.fac]
      have h : (m ≫ (prodCone X c).π.app j) ≫ prod.snd = s.π.app j ≫ prod.snd :=
        congrArg (· ≫ prod.snd) (hm j)
      rwa [Category.assoc, prodCone_π_app, prod.map_snd, ← Category.assoc] at h

/-- Taking the product with a fixed object preserves a limit over a codirected diagram. -/
private noncomputable def prodCone_isLimit_of_directed {I : Type*} [Preorder I]
    [IsDirected I (· ≤ ·)] (X : C) {E : Iᵒᵖ ⥤ C} {c : Cone E} (hc : IsLimit c) (i₀ : I) :
    IsLimit (prodCone X c) :=
  prodCone_isLimit X hc (op i₀) fun s i ↦ by
    obtain ⟨k, hk₀, hki⟩ := IsDirected.directed (r := (· ≤ ·)) i₀ i.unop
    exact (prodCone_fst_eq_of_hom X E s (homOfLE hk₀).op).trans
      (prodCone_fst_eq_of_hom X E s (homOfLE hki).op).symm

/-- The projections of a product cone kill the second factor. -/
private theorem prodCone_π_comp_fst (X : C) {E : J ⥤ C} (c : Cone E) (j : J) :
    (prodCone X c).π.app j ≫ (prod.fst : X ⨯ E.obj j ⟶ X) = prod.fst := by
  rw [prodCone_π_app, prod.map_fst, Category.comp_id]

/-- A product with the identity kills the second factor on first projections. -/
private theorem prod_map_id_comp_fst {X Y Z : C} (g : Y ⟶ Z) :
    prod.map (𝟙 X) g ≫ (prod.fst : X ⨯ Z ⟶ X) = prod.fst := by
  rw [prod.map_fst, Category.comp_id]

/-- The graph of `f` followed by the product of the identity with `g` is the morphism with
components `f` and `g`. -/
private theorem prod_lift_id_comp_prod_map {X Y Z : C} (f : Y ⟶ X) (g : Y ⟶ Z) :
    prod.lift f (𝟙 Y) ≫ prod.map (𝟙 X) g = prod.lift f g := by
  refine prod.hom_ext ?_ ?_ <;> simp

/-- The cone obtained as a product with a fixed object commutes over the fixed object. -/
private theorem prodCone_π_comp_prodDiagramFst (X : C) {E : J ⥤ C} (c : Cone E) :
    (prodCone X c).π ≫ prodDiagramFst X E
      = (Functor.const J).map (prod.fst : X ⨯ c.pt ⟶ X) :=
  NatTrans.ext (funext fun j => prodCone_π_comp_fst X c j)

end ProdDiagram

/-! ### Restriction of a representable property along a change of base scheme -/

/-- A test object of the restricted presheaf of a representable morphism is a test object of
the morphism itself: for `q : A ⟶ (Over.map g).obj T` the fibre square identifying `A` over
`T` is the one below. -/
private theorem isPullback_restrict_yoneda (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS' ⟶ B.obj hS)
    (T : BigFppfOver B S' hS') (A : BigFppfOver B S hS) (q : A ⟶ (Over.map g).obj T) :
    let R := OverShriek.relocalizeRestrict g
    let A' : BigFppfOver B S' hS' := Over.mk (q.left ≫ T.hom)
    let q' : A' ⟶ T := Over.homMk q.left rfl
    let i : (Over.map g).obj A' ⟶ A :=
      Over.homMk (𝟙 _) (by simpa [A', Category.assoc] using q.w.symm)
    IsPullback (yonedaEquiv.symm i) (yoneda.map q')
      (R.map (yoneda.map q)) (yonedaEquiv.symm (𝟙 ((Over.map g).obj T))) := by
  let R := OverShriek.relocalizeRestrict g
  let M := Over.map g
  let A' : BigFppfOver B S' hS' := Over.mk (q.left ≫ T.hom)
  let q' : A' ⟶ T := Over.homMk q.left rfl
  let i : M.obj A' ⟶ A := Over.homMk (𝟙 _)
    (by simpa [M, A', Category.assoc] using q.w.symm)
  let j : yoneda.obj A' ⟶ R.obj (yoneda.obj A) := yonedaEquiv.symm i
  let d : yoneda.obj T ⟶ R.obj (yoneda.obj (M.obj T)) := yonedaEquiv.symm (𝟙 _)
  have hj : IsPullback j (yoneda.map q') (R.map (yoneda.map q)) d := by
    apply IsPullback.of_forall_isPullback_app
    intro X
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · ext x
      apply Over.OverMorphism.ext
      change (x.left ≫ 𝟙 _) ≫ q.left = x.left ≫ q.left ≫ 𝟙 _
      simp
    · intro x y hxy
      apply Over.OverMorphism.ext
      have e := congrArg Over.Hom.left hxy.1
      change x.left ≫ 𝟙 _ = y.left ≫ 𝟙 _ at e
      simpa using e
    · intro x y hxy
      have e : x.left ≫ q.left = y.left := by
        have e := congrArg Over.Hom.left hxy
        simpa [R, M, d, yonedaEquiv] using e
      let z : X.unop ⟶ A' := Over.homMk x.left (by
        change x.left ≫ q.left ≫ T.hom = X.unop.hom
        rw [← Category.assoc, e, y.w])
      refine ⟨z, ?_, ?_⟩
      · apply Over.OverMorphism.ext
        change x.left ≫ 𝟙 _ = x.left
        simp
      · exact Over.OverMorphism.ext e
  exact hj

/-- Restriction along a change of base scheme preserves a representable morphism property:
every test object of the restricted morphism comes from a test object upstairs. -/
theorem presheaf_restrict (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS' ⟶ B.obj hS)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    (P.inverseImage (BigFppfOver.toScheme B S' hS')).presheaf
      ((OverShriek.relocalizeRestrict g).map f) := by
  let R := OverShriek.relocalizeRestrict g
  let M := Over.map g
  apply MorphismProperty.relative.of_exists
  intro T t
  let ξ : G.obj (op (M.obj T)) := (yonedaEquiv t : (R.obj G).obj (op T))
  let t₀ : yoneda.obj (M.obj T) ⟶ G := yonedaEquiv.symm ξ
  obtain ⟨A, q, a, ha⟩ := hf.rep t₀
  let A' : BigFppfOver B S' hS' := Over.mk (q.left ≫ T.hom)
  let q' : A' ⟶ T := Over.homMk q.left rfl
  let i : M.obj A' ⟶ A := Over.homMk (𝟙 _) (by simpa [M, A', Category.assoc] using q.w.symm)
  let j : yoneda.obj A' ⟶ R.obj (yoneda.obj A) := yonedaEquiv.symm i
  let d : yoneda.obj T ⟶ R.obj (yoneda.obj (M.obj T)) := yonedaEquiv.symm (𝟙 _)
  have hj : IsPullback j (yoneda.map q') (R.map (yoneda.map q)) d :=
    isPullback_restrict_yoneda B S S' hS hS' g T A q
  have ht : d ≫ R.map t₀ = t := by
    apply yonedaEquiv.injective
    change G.map (𝟙 (M.obj T)).op ξ = ξ
    simp
  refine ⟨A', j ≫ R.map a, q', ?_, ?_⟩
  · simpa only [ht] using hj.paste_horiz (ha.map R)
  · exact hf.property t₀ a q ha

/-! ### The system of finite type `ℤ`-subalgebras -/

/-- Every commutative ring is an algebra over the integers of its own universe. -/
private abbrev instAlgebraULiftInt (A : Type u) [CommRing A] : Algebra (ULift.{u} ℤ) A :=
  RingHom.toAlgebra ((algebraMap ℤ A).comp
    (ULift.ringEquiv.{0, u} : ULift.{u} ℤ ≃+* ℤ).toRingHom)

attribute [local instance] instAlgebraULiftInt

/-- The finite type `ℤ`-subalgebras of `A` containing a fixed subalgebra `R₀`. -/
private abbrev ApproxIndex (A : Type u) [CommRing A] (R₀ : Subalgebra (ULift.{u} ℤ) A) :=
  {K : Subalgebra (ULift.{u} ℤ) A // R₀ ≤ K ∧ K.FG}

/-- The finite type subalgebras containing `R₀` are directed by inclusion, a supremum of two
of them being again of finite type. -/
private theorem approxIndex_isDirected {A : Type u} [CommRing A]
    (R₀ : Subalgebra (ULift.{u} ℤ) A) : IsDirected (ApproxIndex A R₀) (· ≤ ·) := by
  refine ⟨fun i j => ⟨⟨i.1 ⊔ j.1, le_trans i.2.1 le_sup_left, i.2.2.sup j.2.2⟩, ?_, ?_⟩⟩
  · change i.1 ≤ i.1 ⊔ j.1; exact le_sup_left
  · change j.1 ≤ i.1 ⊔ j.1; exact le_sup_right

/-- There are at most `max #A ℵ₀` finite type subalgebras of `A`: each is generated by a
finite subset, and choosing one such subset for each is injective. -/
private theorem mk_approxIndex_le (A : Type u) [CommRing A]
    (R₀ : Subalgebra (ULift.{u} ℤ) A) : #(ApproxIndex A R₀) ≤ max #A ℵ₀ := by
  classical
  have hex : ∀ i : ApproxIndex A R₀,
      ∃ s : Finset A, Algebra.adjoin (ULift.{u} ℤ) (↑s : Set A) = i.1 := fun i => i.2.2
  choose s hs using hex
  have hinj : Function.Injective s := by
    intro i j h
    exact Subtype.ext ((hs i).symm.trans (by rw [h]; exact hs j))
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rcases finite_or_infinite A with _ | _
  · exact (Cardinal.lt_aleph0_of_finite (Finset A)).le.trans (le_max_right _ _)
  · exact (Cardinal.mk_finset_of_infinite A).le.trans (le_max_left _ _)

/-- The diagram of finite type subalgebras of `A` containing `R₀`, as rings. -/
private abbrev approxDiagram {A : Type u} [CommRing A] (R₀ : Subalgebra (ULift.{u} ℤ) A) :
    ApproxIndex A R₀ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of i.1
  map := fun {i j} f => CommRingCat.ofHom (Subalgebra.inclusion f.down.down).toRingHom
  map_id := by intro i; apply CommRingCat.hom_ext; ext x; rfl
  map_comp := by intro i j k f g; apply CommRingCat.hom_ext; ext x; rfl

/-- The cocone on the finite type subalgebras of `A` given by their inclusions into `A`. -/
private abbrev approxCocone {A : Type u} [CommRing A] (R₀ : Subalgebra (ULift.{u} ℤ) A) :
    Cocone (approxDiagram R₀) where
  pt := CommRingCat.of A
  ι :=
    { app := fun i => CommRingCat.ofHom (Subalgebra.val i.1).toRingHom
      naturality := by intro i j f; apply CommRingCat.hom_ext; ext x; rfl }

/-- **A ring is the filtered union of its finite type `ℤ`-subalgebras.**  Every element lies
in the subalgebra it generates together with `R₀`, so the supremum of the system is all of
`A`, and the colimit is computed by `Subalgebra.iSupLift`. -/
private noncomputable def approxCocone_isColimit {A : Type u} [CommRing A]
    (R₀ : Subalgebra (ULift.{u} ℤ) A) (hR₀ : R₀.FG) : IsColimit (approxCocone R₀) := by
  classical
  letI : Nonempty (ApproxIndex A R₀) := ⟨⟨R₀, le_rfl, hR₀⟩⟩
  letI : IsDirected (ApproxIndex A R₀) (· ≤ ·) := approxIndex_isDirected R₀
  let K : ApproxIndex A R₀ → Subalgebra (ULift.{u} ℤ) A := Subtype.val
  have dir : Directed (· ≤ ·) K := fun i j => IsDirected.directed (r := (· ≤ ·)) i j
  have hmem (x : A) : ∃ i : ApproxIndex A R₀, x ∈ K i :=
    ⟨⟨R₀ ⊔ Algebra.adjoin (ULift.{u} ℤ) {x}, le_sup_left,
      hR₀.sup <| (Subalgebra.fg_iff_finiteType _).2
        (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))⟩,
      (le_sup_right (a := R₀) (Algebra.subset_adjoin (by simp)) :
        x ∈ R₀ ⊔ Algebra.adjoin (ULift.{u} ℤ) {x})⟩
  have sup : (⨆ i, K i) = ⊤ :=
    eq_top_iff.2 fun x _ => (hmem x).elim fun i hi => le_iSup K i hi
  let f (c : Cocone (approxDiagram R₀)) (i : ApproxIndex A R₀) :
      K i →ₐ[ULift.{u} ℤ] (↑c.pt) :=
        { toRingHom := (c.ι.app i).hom
          commutes' := fun ⟨z⟩ => by
            change (c.ι.app i).hom (Int.cast z) = (Int.cast z)
            exact map_intCast (c.ι.app i).hom z }
  have hf (c : Cocone (approxDiagram R₀)) :
      ∀ (i j : ApproxIndex A R₀) (h : K i ≤ K j),
        f c i = (f c j).comp (Subalgebra.inclusion h) := fun i j h => AlgHom.ext fun x => by
    simpa [approxDiagram, f] using
      (congrArg (fun k : CommRingCat.Hom _ _ => k.hom x) (c.w (homOfLE h))).symm
  let liftTop (c : Cocone (approxDiagram R₀)) :
      (↑(⊤ : Subalgebra (ULift.{u} ℤ) A)) →ₐ[ULift.{u} ℤ] (↑c.pt) :=
    Subalgebra.iSupLift K dir (f c) (hf c) ⊤ (by rw [sup])
  let desc (c : Cocone (approxDiagram R₀)) : CommRingCat.of A ⟶ c.pt :=
    CommRingCat.ofHom (liftTop c |>.comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom
  refine IsColimit.mk desc ?_ ?_
  · intro c i
    apply CommRingCat.hom_ext
    ext x
    change liftTop c (Subalgebra.topEquiv.symm (x : A)) = f c i x
    have htop : Subalgebra.topEquiv.symm (x : A) =
        Subalgebra.inclusion (show K i ≤ ⊤ from le_top) x :=
      Subtype.ext rfl
    rw [htop]
    exact Subalgebra.iSupLift_inclusion (K := K) (dir := dir) (f := f c) (hf := hf c)
      (T := ⊤) (hT := by rw [sup]) (i := i) (x := x) (h := le_top)
  · intro c m hm
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨i, hx⟩ := hmem x
    let xi : K i := ⟨x, hx⟩
    have h₁ : m.hom x = f c i xi := by
      simpa [approxCocone, approxDiagram, K, f, xi] using
        congrArg (fun k : CommRingCat.Hom _ _ => k.hom xi) (hm i)
    have h₂ : (desc c).hom x = f c i xi := by
      change liftTop c (Subalgebra.topEquiv.symm x) = f c i xi
      exact Subalgebra.iSupLift_of_mem (K := K) (dir := dir) (f := f c) (hf := hf c)
        (T := ⊤) (hT := by rw [sup]) (i := i) (x := Subalgebra.topEquiv.symm x)
        (by simpa using hx)
    exact h₁.trans h₂.symm

/-- The inverse system of spectra of the finite type `ℤ`-subalgebras of `A`. -/
private noncomputable abbrev approxSpectrumSystem (A : Type u) [CommRing A] :=
  (approxDiagram (⊥ : Subalgebra (ULift.{u} ℤ) A)).op ⋙ Scheme.Spec

/-- The cone on the spectra of the finite type `ℤ`-subalgebras of `A` with vertex
`Spec A`. -/
private noncomputable abbrev approxSpectrumCone (A : Type u) [CommRing A] :
    Cone (approxSpectrumSystem A) :=
  Scheme.Spec.mapCone (approxCocone (⊥ : Subalgebra (ULift.{u} ℤ) A)).op

/-- `Spec A` is the limit of the spectra of the finite type `ℤ`-subalgebras of `A`, since
`Spec` turns the colimit of rings into a limit of schemes. -/
private noncomputable def approxSpectrumCone_isLimit (A : Type u) [CommRing A] :
    IsLimit (approxSpectrumCone A) :=
  isLimitOfPreserves Scheme.Spec
    (approxCocone_isColimit (⊥ : Subalgebra (ULift.{u} ℤ) A)
      ((Subalgebra.fg_iff_finiteType _).2 inferInstance)).op

/-- A stage of the system is of finite type over `ℤ`. -/
private theorem approxStage_isFiniteType (A : Type u) [CommRing A]
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    Algebra.FiniteType (ULift.{u} ℤ) i.1 :=
  (Subalgebra.fg_iff_finiteType i.1).mp i.2.2

/-- The spectrum of a stage of the system lies in the site: it is the spectrum of a ring of
finite type over `ℤ`, whose spectrum is the terminal scheme. -/
private theorem approxStage_size_lt (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    (A : Type u) [CommRing A] (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    (Spec (.of i.1)).size < B.cutoff := by
  let eInt : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  have hBase : (Spec (.of (ULift.{u} ℤ))).size < B.cutoff := by
    rw [Scheme.size_congr eInt]
    exact hZ
  let : Algebra.FiniteType (ULift.{u} ℤ) (↥i.1) := approxStage_isFiniteType A i
  exact Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hBase
    (Cardinal.mk_le_of_algebra_finiteType (ULift.{u} ℤ) (↥i.1))

/-! ### The system over the terminal scheme and its restriction to the site over `S` -/

/-- A stage of the system, as an object of the big fppf site over the terminal scheme. -/
private noncomputable def approxStageObj (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    BigFppfOver B (⊤_ Scheme.{u}) hZ := by
  let V := Spec (.of i.1)
  let hV := approxStage_size_lt B hZ A i
  let Vobj : B.Schemes := ⟨V, hV⟩
  let qV : Vobj ⟶ B.obj hZ := B.inclusion.preimage (terminalIsTerminal.from V)
  exact Over.mk qV

/-- A transition morphism of the system, as a morphism of the site over the terminal
scheme. -/
private noncomputable def approxStageMap (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    {i j : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)}
    (g : Spec (.of j.1) ⟶ Spec (.of i.1)) :
    approxStageObj B hZ A j ⟶ approxStageObj B hZ A i := by
  let Wj := (approxStageObj B hZ A j).left
  let Wi := (approxStageObj B hZ A i).left
  have g' : B.inclusion.obj Wj ⟶ B.inclusion.obj Wi := g
  exact Over.homMk (B.inclusion.preimage g')
    (B.inclusion.map_injective (terminalIsTerminal.hom_ext _ _))

/-- The inverse system of stages, in the big fppf site over the terminal scheme. -/
private noncomputable def approxStageDiagram (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A] :
    (ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A))ᵒᵖ ⥤
      BigFppfOver B (⊤_ Scheme.{u}) hZ where
  obj i := approxStageObj B hZ A i.unop
  map := fun {i j} f => approxStageMap B hZ A ((approxSpectrumSystem A).map f)
  map_id := by
    intro i
    apply Over.OverMorphism.ext
    let V := (approxStageObj B hZ A i.unop).left
    let g : B.inclusion.obj V ⟶ B.inclusion.obj V := (approxSpectrumSystem A).map (𝟙 i)
    change B.inclusion.preimage g = 𝟙 V
    have hg : g = 𝟙 _ := (approxSpectrumSystem A).map_id i
    rw [hg, B.inclusion.preimage_id]
  map_comp := by
    intro i j k f g
    apply Over.OverMorphism.ext
    let V := (approxStageObj B hZ A i.unop).left
    let W := (approxStageObj B hZ A j.unop).left
    let Y := (approxStageObj B hZ A k.unop).left
    let p : B.inclusion.obj V ⟶ B.inclusion.obj W := (approxSpectrumSystem A).map f
    let q : B.inclusion.obj W ⟶ B.inclusion.obj Y := (approxSpectrumSystem A).map g
    let r : B.inclusion.obj V ⟶ B.inclusion.obj Y := (approxSpectrumSystem A).map (f ≫ g)
    change B.inclusion.preimage r = B.inclusion.preimage p ≫ B.inclusion.preimage q
    have hr : r = p ≫ q := (approxSpectrumSystem A).map_comp f g
    rw [hr, B.inclusion.preimage_comp]

/-- Restriction of the functor of points from the site over the terminal scheme to the site
over `S`. -/
private noncomputable def approxRestrictionFunctor (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) :
    BigFppfOver B (⊤_ Scheme.{u}) hZ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := by
  let gBase : B.obj hS ⟶ B.obj hZ := B.inclusion.preimage (terminalIsTerminal.from S)
  exact yoneda ⋙ OverShriek.relocalizeRestrict gBase

/-- The inverse system of stages, as algebraic spaces over `S`. -/
private noncomputable abbrev approxSystemOverS (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A] :=
  approxStageDiagram B hZ A ⋙ approxRestrictionFunctor B S hS hZ

/-- A stage of the system, restricted to the site over `S`, is an algebraic space. -/
private theorem approxStageOverS_isAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    IsAlgebraicSpace B S hS
      ((approxRestrictionFunctor B S hS hZ).obj (approxStageObj B hZ A i)) := by
  let gBase : B.obj hS ⟶ B.obj hZ := B.inclusion.preimage (terminalIsTerminal.from S)
  exact AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict B S (⊤_ Scheme.{u}) hS hZ gBase
    (yoneda.obj (approxStageObj B hZ A i))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ (approxStageObj B hZ A i))

/-- A stage `X ⨯ Spec Aᵢ` of the product system is an algebraic space. -/
private theorem approxProductStage_isAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    IsAlgebraicSpace B S hS (X ⨯ (approxSystemOverS B S hS hZ A).obj (op i)) :=
  isAlgebraicSpace_prod B S hS hX (approxStageOverS_isAlgebraicSpace B S hS hZ A i)

/-- `Spec A` itself, as an object of the big fppf site over the terminal scheme. -/
private noncomputable def approxLimitObj (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : (Spec (.of A)).size < B.cutoff) : BigFppfOver B (⊤_ Scheme.{u}) hZ := by
  let V : B.Schemes := ⟨Spec (.of A), hA⟩
  let q : V ⟶ B.obj hZ := B.inclusion.preimage (terminalIsTerminal.from (Spec (.of A)))
  exact Over.mk q

/-- The inclusion of a big fppf site into schemes is full, and the chosen preimage of a
morphism of schemes between objects of the site is that morphism. -/
private theorem bigFppfInclusion_preimage_hom (B : BigFppfSite.{u}) {V W : B.Schemes}
    (f : B.inclusion.obj V ⟶ B.inclusion.obj W) : (B.inclusion.preimage f).hom = f := by
  simpa [AlgebraicGeometry.BigFppfSite.inclusion, AlgebraicGeometry.schemeBelowInclusion,
    ObjectProperty.ι_map] using B.inclusion.map_preimage f

/-- The cone on the system of stages in the site over the terminal scheme, with vertex
`Spec A`. -/
private noncomputable def approxLimitCone (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : (Spec (.of A)).size < B.cutoff) : Cone (approxStageDiagram B hZ A) where
  pt := approxLimitObj B hZ A hA
  π :=
    { app := fun i =>
        let V := (approxLimitObj B hZ A hA).left
        let W := (approxStageObj B hZ A i.unop).left
        let g : B.inclusion.obj V ⟶ B.inclusion.obj W := (approxSpectrumCone A).π.app i
        Over.homMk (B.inclusion.preimage g)
          (B.inclusion.map_injective (terminalIsTerminal.hom_ext _ _))
      naturality := by
        intro i j f
        apply Over.OverMorphism.ext
        simp only [Over.comp_left]
        let V := (approxLimitObj B hZ A hA).left
        let Wi := (approxStageObj B hZ A i.unop).left
        let Wj := (approxStageObj B hZ A j.unop).left
        let gi : B.inclusion.obj V ⟶ B.inclusion.obj Wi := (approxSpectrumCone A).π.app i
        let gj : B.inclusion.obj V ⟶ B.inclusion.obj Wj := (approxSpectrumCone A).π.app j
        let hij : B.inclusion.obj Wi ⟶ B.inclusion.obj Wj := (approxSpectrumSystem A).map f
        change B.inclusion.preimage gj =
          B.inclusion.preimage gi ≫ B.inclusion.preimage hij
        rw [← B.inclusion.preimage_comp]
        exact congrArg B.inclusion.preimage ((approxSpectrumCone A).w f).symm }

/-- `Spec A` is the limit of the stages in the site over the terminal scheme: the forgetful
functor to schemes is fully faithful, so the limit statement is the one for schemes. -/
private noncomputable def approxLimitCone_isLimit (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : (Spec (.of A)).size < B.cutoff) : IsLimit (approxLimitCone B hZ A hA) := by
  let F := Over.forget (B.obj hZ) ⋙ B.inclusion
  have hmap {i j : (ApproxIndex A ⊥)ᵒᵖ} (f : i ⟶ j) :
      F.map ((approxStageDiagram B hZ A).map f) = (approxSpectrumSystem A).map f := by
    let Vi := (approxStageObj B hZ A i.unop).left
    let Vj := (approxStageObj B hZ A j.unop).left
    let g : B.inclusion.obj Vi ⟶ B.inclusion.obj Vj := (approxSpectrumSystem A).map f
    dsimp [F, approxStageDiagram, approxStageMap, approxStageObj, approxSpectrumSystem, Vi, Vj]
    change B.inclusion.map (B.inclusion.preimage g) = g
    exact B.inclusion.map_preimage g
  let hlim := approxSpectrumCone_isLimit A
  let transport (s : Cone (approxStageDiagram B hZ A)) : Cone (approxSpectrumSystem A) :=
    { pt := F.obj s.pt
      π :=
        { app := fun i => F.map (s.π.app i)
          naturality := by
            intro i j f
            rw [← hmap f]
            simp only [Functor.const_obj_map]
            exact (congrArg F.map (s.w f)).symm.trans (F.map_comp _ _) } }
  have hπ (i : (ApproxIndex A ⊥)ᵒᵖ) :
      F.map ((approxLimitCone B hZ A hA).π.app i) = (approxSpectrumCone A).π.app i := by
    change ((approxLimitCone B hZ A hA).π.app i).left.hom = _
    dsimp [approxLimitCone]
    exact bigFppfInclusion_preimage_hom B _
  let lift (s : Cone (approxStageDiagram B hZ A)) : s.pt ⟶ (approxLimitCone B hZ A hA).pt := by
    let g := hlim.lift (transport s)
    have g' : B.inclusion.obj s.pt.left ⟶ B.inclusion.obj (approxLimitObj B hZ A hA).left := by
      dsimp [transport, F, approxLimitObj, AlgebraicGeometry.BigFppfSite.inclusion,
        AlgebraicGeometry.schemeBelowInclusion] at g ⊢
      exact g
    exact Over.homMk (B.inclusion.preimage g')
      (B.inclusion.map_injective (terminalIsTerminal.hom_ext _ _))
  have hLift (s : Cone (approxStageDiagram B hZ A)) :
      F.map (lift s) = hlim.lift (transport s) := by
    dsimp [lift]
    let g' : B.inclusion.obj s.pt.left ⟶ B.inclusion.obj (approxLimitObj B hZ A hA).left := by
      dsimp [F, transport, approxLimitObj, AlgebraicGeometry.BigFppfSite.inclusion,
        AlgebraicGeometry.schemeBelowInclusion]
      exact hlim.lift (transport s)
    change (B.inclusion.preimage g').hom = hlim.lift (transport s)
    rw [bigFppfInclusion_preimage_hom]
    rfl
  refine IsLimit.mk lift ?_ ?_
  · intro s i
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change F.map (lift s) ≫ F.map ((approxLimitCone B hZ A hA).π.app i) = F.map (s.π.app i)
    rw [hLift, hπ]
    exact hlim.fac (transport s) i
  · intro s m hm
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    have hm' : F.map m = hlim.lift (transport s) := by
      apply hlim.hom_ext
      intro i
      have hi := congrArg F.map (hm i)
      have hfac := hlim.fac (transport s) i
      have hi' := hi.trans hfac.symm
      rw [F.map_comp] at hi'
      rw [hπ] at hi'
      exact hi'
    change F.map m = F.map (lift s)
    rw [hLift]
    exact hm'

/-- The cone on the restricted system of stages, with vertex the restricted functor of points
of `Spec A`. -/
private noncomputable def approxRestrictionCone (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : (Spec (.of A)).size < B.cutoff) : Cone (approxSystemOverS B S hS hZ A) :=
  (approxRestrictionFunctor B S hS hZ).mapCone (approxLimitCone B hZ A hA)

/-- Restriction to the site over `S` is a composite of a Yoneda embedding and a right
adjoint, so it preserves the limit of the stages. -/
private noncomputable def approxRestrictionCone_isLimit (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : (Spec (.of A)).size < B.cutoff) : IsLimit (approxRestrictionCone B S hS hZ A hA) := by
  let F := approxRestrictionFunctor B S hS hZ
  haveI : PreservesLimitsOfShape (ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A))ᵒᵖ F := by
    dsimp [F, approxRestrictionFunctor]
    infer_instance
  exact isLimitOfPreserves F (approxLimitCone_isLimit B hZ A hA)

/-! ### Products and graphs -/

/-- A representable property stable under base change is inherited by the product of a
morphism with the identity: that product is a base change of the morphism. -/
private theorem presheaf_prodMap_id (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ Z)
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (prod.map (𝟙 X) f) := by
  have sq : IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd := by
    apply (IsPullback.of_prod_fst_with_id f X).of_iso'
      (prod.braiding X Y) (Iso.refl _) (prod.braiding X Z) (Iso.refl _)
    all_goals ext <;> simp
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf

/-- The graph of `f : Y ⟶ X` in the product, as a base change of the diagonal of `X`. -/
@[sga "3 VIIB 1.6.1" "Cartesian square"]
private theorem isPullback_graph {C : Type*} [Category C] [HasBinaryProducts C] {X Y : C}
    (f : Y ⟶ X) : IsPullback f (prod.lift f (𝟙 Y)) (diag X) (prod.map (𝟙 X) f) where
  w := by ext <;> simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have h₁ := congrArg (fun k ↦ k ≫ (prod.fst : X ⨯ X ⟶ X)) s.condition
    have h₂ := congrArg (fun k ↦ k ≫ (prod.snd : X ⨯ X ⟶ X)) s.condition
    simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id,
      prod.map_fst, prod.map_snd] at h₁ h₂
    refine ⟨s.snd ≫ prod.snd, ?_, ?_, ?_⟩
    · change (s.snd ≫ prod.snd) ≫ f = s.fst
      exact (Category.assoc _ _ _).trans h₂.symm
    · change (s.snd ≫ prod.snd) ≫ prod.lift f (𝟙 Y) = s.snd
      apply prod.hom_ext
      · rw [Category.assoc, prod.lift_fst, Category.assoc]
        exact h₂.symm.trans h₁
      · rw [Category.assoc, prod.lift_snd, Category.comp_id]
    · intro m hm₁ hm₂
      change m ≫ prod.lift f (𝟙 Y) = s.snd at hm₂
      have h : m ≫ (prod.lift f (𝟙 Y) ≫ prod.snd) = s.snd ≫ prod.snd := by
        rw [← Category.assoc, hm₂]
      exact (Category.comp_id m).symm.trans
        ((congrArg (m ≫ ·) (prod.lift_snd f (𝟙 Y))).symm.trans h))⟩

/-- **The graph of a morphism into a locally separated algebraic space is an immersion.**
For `f : Y ⟶ X` with `X` locally separated over `S`, the graph `Y ⟶ X ⨯ Y` of `f` is an
immersion, being a base change of the diagonal of `X`.  This is Stacks 03KO, part (2), in the
form the embedding argument uses it: the diagonal of `X` is the relative diagonal of the
morphism from `X` to a terminal presheaf, and the graph in the product is the graph over that
terminal presheaf. -/
private theorem isImmersion_prod_lift_id (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X)
    (hX : IsLocallySeparatedOver B S hS X) :
    IsImmersion B S hS (prod.lift f (𝟙 Y)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_graph f) hX

/-! ### Comparison of restricted functors of points -/

/-- Restricting the functor of points of `V` along a change of base scheme gives the functor
of points of the base change of `V`, by the adjunction between `Over.map` and
`Over.pullback`. -/
private noncomputable def restrictionYonedaIso {C : Type*} [Category.{u} C] [HasPullbacks C]
    {S Z : C} (g : S ⟶ Z) (V : Over Z) :
    (Over.map g).op ⋙ yoneda.obj V ≅ yoneda.obj ((Over.pullback g).obj V) :=
  NatIso.ofComponents
    (fun T ↦ ((Over.mapPullbackAdj g).homEquiv T.unop V).toIso)
    (by
      intro T T' a
      ext q
      exact (Over.mapPullbackAdj g).homEquiv_naturality_left a.unop q)

/-- A morphism of sites which is an immersion of schemes induces an immersion of the
corresponding restricted functors of points. -/
private theorem immersion_restrictionYoneda (B : BigFppfSite.{u}) (S Z : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains Z) (g : B.obj hS ⟶ B.obj hZ)
    (U : BigFppfOver B S hS) (V : BigFppfOver B Z hZ) (q : (Over.map g).obj U ⟶ V)
    (hq : _root_.AlgebraicGeometry.IsImmersion (B.inclusion.map q.left)) :
    IsImmersion B S hS
      (yonedaEquiv.symm q : yoneda.obj U ⟶ (Over.map g).op ⋙ yoneda.obj V) := by
  let e := restrictionYonedaIso g V
  let a := (Over.mapPullbackAdj g).homEquiv U V q
  have ha : a.left ≫ ((Over.mapPullbackAdj g).counit.app V).left = q.left := by
    have h := (Over.mapPullbackAdj g).homEquiv_counit U V a
    rw [Equiv.symm_apply_apply] at h
    exact congrArg Over.Hom.left h.symm
  have ham : _root_.AlgebraicGeometry.IsImmersion (B.inclusion.map a.left) := by
    have hc : _root_.AlgebraicGeometry.IsImmersion
        (B.inclusion.map a.left ≫ B.inclusion.map
          ((Over.mapPullbackAdj g).counit.app V).left) := by
      rw [← B.inclusion.map_comp, ha]
      exact hq
    exact _root_.AlgebraicGeometry.IsImmersion.of_comp _
      (B.inclusion.map ((Over.mapPullbackAdj g).counit.app V).left)
  let P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange := schemeProperty_baseChange B S hS _
  have hp : P.presheaf (yoneda.map a) := P.relative_map ham
  have heq : (yonedaEquiv.symm q : yoneda.obj U ⟶ _) ≫ e.hom = yoneda.map a := by
    apply yonedaEquiv.injective
    change (Over.mapPullbackAdj g).homEquiv U V ((Over.map g).map (𝟙 U) ≫ q) = a
    simp [a]
  rw [← heq] at hp
  exact (MorphismProperty.cancel_right_of_respectsIso P.presheaf _ e.hom).mp hp

/-- When a scheme `W` over `S` is a base change of an object `V` of the site over `Z`, the
restricted functor of points of `V` is the functor of points of `W`. -/
private noncomputable def restrictionYonedaIsoOfIsPullback (B : BigFppfSite.{u})
    (S Z : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains Z) (g : B.obj hS ⟶ B.obj hZ)
    (V : BigFppfOver B Z hZ) (W : Over S) (p : W.left ⟶ B.inclusion.obj V.left)
    (sq : IsPullback p W.hom (B.inclusion.map V.hom) (B.inclusion.map g)) :
    (Over.map g).op ⋙ yoneda.obj V ≅ (Over.post B.inclusion).op ⋙ yoneda.obj W := by
  let e (T : BigFppfOver B S hS) :
      ((Over.map g).obj T ⟶ V) ≃ ((Over.post B.inclusion).obj T ⟶ W) :=
    { toFun a := Over.homMk
        (sq.lift (B.inclusion.map (a.left : T.left ⟶ V.left)) (B.inclusion.map T.hom)
          (by
            have h : (a.left : T.left ⟶ V.left) ≫ V.hom = T.hom ≫ g := a.w
            have h2 := congrArg B.inclusion.map h
            rw [Functor.map_comp, Functor.map_comp] at h2
            exact h2))
        (sq.lift_snd _ _ _)
      invFun a := Over.homMk
        (B.inclusion.preimage
          ((a.left : B.inclusion.obj T.left ⟶ W.left) ≫ p)) (by
        apply B.inclusion.map_injective
        rw [Functor.map_comp, Functor.map_preimage]
        change ((a.left : B.inclusion.obj T.left ⟶ W.left) ≫ p) ≫ B.inclusion.map V.hom
          = B.inclusion.map (T.hom ≫ g)
        rw [Category.assoc, sq.w, ← Category.assoc, a.w, Functor.map_comp]
        rfl)
      left_inv a := Over.OverMorphism.ext <| B.inclusion.map_injective <|
        (B.inclusion.map_preimage _).trans (sq.lift_fst _ _ _)
      right_inv a := by
        apply Over.OverMorphism.ext
        refine sq.hom_ext ?_ ?_
        · exact (sq.lift_fst _ _ _).trans (B.inclusion.map_preimage _)
        · exact (sq.lift_snd _ _ _).trans a.w.symm }
  refine NatIso.ofComponents (fun T ↦ (e T.unop).toIso) ?_
  intro T T' a
  ext q
  apply Over.OverMorphism.ext
  change (e T'.unop ((Over.map g).map a.unop ≫ q)).left =
    B.inclusion.map a.unop.left ≫ (e T.unop q).left
  dsimp only [e, Equiv.coe_fn_mk, Over.homMk_left]
  refine sq.hom_ext ?_ ?_
  · exact (sq.lift_fst _ _ _).trans
      ((B.inclusion.map_comp a.unop.left q.left).trans
        ((congrArg (B.inclusion.map a.unop.left ≫ ·) (sq.lift_fst _ _ _)).symm.trans
          (Category.assoc _ _ _).symm))
  · exact (sq.lift_snd _ _ _).trans
      ((congrArg B.inclusion.map a.unop.w).symm.trans
        ((B.inclusion.map_comp _ _).trans
          ((congrArg (B.inclusion.map a.unop.left ≫ ·) (sq.lift_snd _ _ _)).symm.trans
            (Category.assoc _ _ _).symm)))

/-! ### A finite type algebra is a closed subscheme of affine space -/

/-- **The spectrum of an algebra of finite type is a closed subscheme of affine space.**  A
finite generating set gives a surjection from a polynomial ring in finitely many variables,
and the spectrum of a surjection is a closed immersion. -/
private theorem exists_isClosedImmersion_affineSpace {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] :
    ∃ (n : ℕ) (j : Spec (.of A) ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of R))),
      _root_.AlgebraicGeometry.IsClosedImmersion j := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  let n := Fintype.card s
  let e : s ≃ Fin n := Fintype.equivFin s
  let φ : MvPolynomial (ULift.{u} (Fin n)) R →ₐ[R] A :=
    MvPolynomial.aeval fun i => (e.symm i.down).1
  have hrange_eq :
      Set.range (fun i : ULift.{u} (Fin n) => (e.symm i.down).1) = (s : Set A) := by
    ext a
    exact ⟨by rintro ⟨i, rfl⟩; exact (e.symm i.down).2, fun ha => ⟨ULift.up (e ⟨a, ha⟩), by simp⟩⟩
  have hrange :
      Algebra.adjoin R (Set.range fun i : ULift.{u} (Fin n) => (e.symm i.down).1) = ⊤ := by
    rw [hrange_eq, hs]
  have hsurj : Function.Surjective φ := by
    rw [Algebra.adjoin_range_eq_range_aeval] at hrange
    exact (AlgHom.range_eq_top φ).mp hrange
  let p : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) R) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom φ.toRingHom
  let eSpec := AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of R)
  have hp : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map p) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective p hsurj
  exact ⟨n, Spec.map p ≫ eSpec.inv, inferInstance⟩

/-- **A stage of the system immerses into affine space over `S`.**  The stage is `Spec Aᵢ`
with `Aᵢ` of finite type over `ℤ`, hence a closed subscheme of affine `n`-space over the
terminal scheme; restricting to the site over `S` and base changing gives a closed immersion
into the restricted functor of points of affine `n`-space over `S`. -/
private theorem exists_isImmersion_approxStage (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    ∃ (n : ℕ) (b : (approxSystemOverS B S hS hZ A).obj (op i) ⟶
      Stacks.Groupoids.points (Over.post B.inclusion)
        (Over.mk (AffineSpace.over (ULift.{u} (Fin n)) S).hom)),
      IsImmersion B S hS b := by
  let : Algebra.FiniteType (ULift.{u} ℤ) i.1 := approxStage_isFiniteType A i
  obtain ⟨n, j, hj⟩ := exists_isClosedImmersion_affineSpace (R := ULift.{u} ℤ) (A := i.1)
  let N := ULift.{u} (Fin n)
  let eZ : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let eA : AffineSpace N (Spec (.of (ULift.{u} ℤ))) ≅ AffineSpace N (⊤_ Scheme.{u}) :=
    (AffineSpace.functor.obj (op N)).mapIso eZ
  have hW : B.Contains (AffineSpace N (⊤_ Scheme.{u})) := by
    change (AffineSpace N (⊤_ Scheme.{u})).size < B.cutoff
    rw [← Scheme.size_congr eA, Scheme.size_congr (AffineSpace.SpecIso N (.of (ULift.{u} ℤ)))]
    exact polynomialSpectrum_size_lt B (ULift.{u} ℤ) n (by rwa [Scheme.size_congr eZ])
  let V := approxStageObj B hZ A i
  let W : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    Over.mk (ObjectProperty.homMk (X := B.obj hW) (Y := B.obj hZ)
      (AffineSpace.over N (⊤_ Scheme.{u})).hom)
  let qleft : V.left ⟶ W.left := B.inclusion.preimage (j ≫ eA.hom)
  let q : V ⟶ W := Over.homMk qleft (B.inclusion.map_injective (terminal.hom_ext _ _))
  let P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  have hq : P q := by
    change _root_.AlgebraicGeometry.IsImmersion (B.inclusion.map qleft)
    rw [show B.inclusion.map qleft = j ≫ eA.hom from B.inclusion.map_preimage _]
    exact _root_.AlgebraicGeometry.IsImmersion.comp j eA.hom
  let : P.IsStableUnderBaseChange := schemeProperty_baseChange B (⊤_ Scheme.{u}) hZ
    (@_root_.AlgebraicGeometry.IsImmersion.{u})
  have hq' : P.presheaf (yoneda.map q) := P.relative_map hq
  let g : B.obj hS ⟶ B.obj hZ := B.inclusion.preimage (terminal.from S)
  let R := OverShriek.relocalizeRestrict g
  have hr := presheaf_restrict B (⊤_ Scheme.{u}) S hZ hS g
    (@_root_.AlgebraicGeometry.IsImmersion.{u}) (yoneda.map q) hq'
  let WS : Over S := Over.mk (AffineSpace.over N S).hom
  have sq : IsPullback (AffineSpace.map N (terminal.from S)) WS.hom
      (B.inclusion.map W.hom) (B.inclusion.map g) := by
    dsimp only [g]
    rw [B.inclusion.map_preimage]
    exact AffineSpace.isPullback_map (terminal.from S)
  let e := restrictionYonedaIsoOfIsPullback B S (⊤_ Scheme.{u}) hS hZ g W WS _ sq
  exact ⟨n, R.map (yoneda.map q) ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom _ hr⟩

/-! ### Stacks 088L -/

/-- The transition morphisms `X ⨯ Spec Aⱼ ⟶ X ⨯ Spec Aᵢ` of the product system are affine,
being products with the identity of the affine transition morphisms of the system of
spectra. -/
private theorem approxProduct_transition_isAffineHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    {i j : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)} (h : i ≤ j) :
    IsAffineHom B S hS
      (prod.map (𝟙 X) ((approxSystemOverS B S hS hZ A).map (homOfLE h).op)) := by
  let P : MorphismProperty Scheme.{u} := @_root_.AlgebraicGeometry.IsAffineHom
  let q := (approxStageDiagram B hZ A).map (homOfLE h).op
  let : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((approxStageDiagram B hZ A).obj (op j))) := by
    change IsAffine (Spec (.of j.1))
    infer_instance
  let : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((approxStageDiagram B hZ A).obj (op i))) := by
    change IsAffine (Spec (.of i.1))
    infer_instance
  have hq : (P.inverseImage (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)) q := by
    change _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map q)
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have hq' := (P.inverseImage
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).relative_map (F := yoneda) hq
  have hr := presheaf_restrict B (⊤_ Scheme.{u}) S hZ hS
    (B.inclusion.preimage (terminal.from S)) P (yoneda.map q) hq'
  have hp := presheaf_prodMap_id B S hS P X _ hr
  apply ((isAffineHom_tfae_of_isAlgebraicSpace B S hS _
    (approxProductStage_isAlgebraicSpace B S hS hZ A X hX j)
    (approxProductStage_isAlgebraicSpace B S hS hZ A X hX i)).out 1 2).mp
  exact ⟨hp.1, hp⟩

/-- The graph of `f` followed by the product with the identity of the immersion of an affine `U`
into the limit of the stages is an immersion `U ⟶ X ⨯ Spec A`. -/
private theorem exists_isImmersion_prod_lift (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : yoneda.obj U ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hls : IsAbsolutelyLocallySeparated B S hS hZ X)
    {A : Type u} [CommRing A] (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of A)) :
    ∃ (hA : (Spec (.of A)).size < B.cutoff)
      (j : yoneda.obj U ⟶ (prodCone X (approxRestrictionCone B S hS hZ A hA)).pt),
      j ≫ prod.fst = f ∧ IsImmersion B S hS j := by
  have hA : (Spec (.of A)).size < B.cutoff := by
    rw [← Scheme.size_congr eU]
    exact U.left.property
  let V := approxLimitObj B hZ A hA
  let g : B.obj hS ⟶ B.obj hZ := B.inclusion.preimage (terminal.from S)
  let eUhom : B.inclusion.obj U.left ⟶ B.inclusion.obj V.left := eU.hom
  let qleft : U.left ⟶ V.left := B.inclusion.preimage eUhom
  let q : (Over.map g).obj U ⟶ V :=
    Over.homMk qleft (B.inclusion.map_injective (terminal.hom_ext _ _))
  let r : yoneda.obj U ⟶ (approxRestrictionCone B S hS hZ A hA).pt := yonedaEquiv.symm q
  have hr : IsImmersion B S hS r := by
    apply immersion_restrictionYoneda B S (⊤_ Scheme.{u}) hS hZ g U V q
    change _root_.AlgebraicGeometry.IsImmersion (B.inclusion.map qleft)
    rw [show B.inclusion.map qleft = eUhom from B.inclusion.map_preimage eUhom]
    have : IsIso eUhom := inferInstanceAs (IsIso eU.hom)
    infer_instance
  refine ⟨hA, prod.lift f r, prod.lift_fst _ _, ?_⟩
  have h₁ := isImmersion_prod_lift_id B S hS f
    (isLocallySeparatedOver_of_isAbsolutelyLocallySeparated B S hS hZ hX hls)
  have h₂ := presheaf_prodMap_id B S hS (@_root_.AlgebraicGeometry.IsImmersion.{u}) X r hr
  have hp := isImmersion_comp B S hS _ _ h₁ h₂
  rwa [prod_lift_id_comp_prod_map f r] at hp

/-- Once `U ⟶ X ⨯ Spec A` is an immersion at some stage `X ⨯ Spec Aᵢ`, composing with the
immersion of `Spec Aᵢ` into affine space gives the immersion into `𝔸ⁿ_X` over `X`. -/
private theorem exists_isImmersion_affineSpaceOver_of_stage (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u)
    [CommRing A] (hA : (Spec (.of A)).size < B.cutoff) (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : Y ⟶ X) (j : Y ⟶ (prodCone X (approxRestrictionCone B S hS hZ A hA)).pt)
    (hjf : j ≫ prod.fst = f) (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A))
    (hi : IsImmersion B S hS (j ≫ (prodCone X (approxRestrictionCone B S hS hZ A hA)).π.app
      (op i))) :
    ∃ (n : ℕ) (j : Y ⟶ affineSpaceOver B S hS X n),
      j ≫ prod.fst = f ∧ IsImmersion B S hS j := by
  obtain ⟨n, b, hbi⟩ := exists_isImmersion_approxStage B S hS hZ A i
  refine ⟨n, (j ≫ (prodCone X (approxRestrictionCone B S hS hZ A hA)).π.app (op i)) ≫
    prod.map (𝟙 X) b, ?_, ?_⟩
  · rw [Category.assoc, prod_map_id_comp_fst, Category.assoc]
    exact (congrArg (j ≫ ·) (prodCone_π_comp_fst X _ (op i))).trans hjf
  · exact isImmersion_comp B S hS _ _ hi
      (presheaf_prodMap_id B S hS (@_root_.AlgebraicGeometry.IsImmersion.{u}) X b hbi)

/-- **Stacks 088L.**  Let `f : U ⟶ X` be a morphism of algebraic spaces over `S` with `U` an
affine scheme, `f` locally of finite type and `X` locally separated.  Then `U` admits an
immersion into affine `n`-space over `X`, over `X`.

The hypothesis `hcard` bounds the ring of sections of `U` by the cofinality of the site's
cutoff; it is not part of Stacks 088L, but is the condition under which the directed limit
used in the proof is an algebraic space in this development, inherited from Stacks 07SF and
Stacks 0828.  See `exists_isImmersion_affineSpaceOver_of_isRegular` for the form in which it
disappears, and the implementation notes of this file for why it cannot be removed outright.

Quasi-separatedness of `X`, which Stacks 088L also assumes, is not needed: this development's
Stacks 0828, part (2) does not assume it of the stages. -/
@[stacks 088L "with the cutoff-cofinality side condition on the sections of `U` that the \
directed limit in the proof requires; quasi-separatedness of `X` is not needed"]
theorem exists_isImmersion_affineSpaceOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : yoneda.obj U ⟶ X)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hls : IsAbsolutelyLocallySeparated B S hS hZ X)
    (hcard : #Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) < B.cutoff.ord.cof) :
    ∃ (n : ℕ) (j : yoneda.obj U ⟶ affineSpaceOver B S hS X n),
      j ≫ prod.fst = f ∧ IsImmersion B S hS j := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let : IsAffine (T.obj U) := hU
  let A : Type u := Γ(T.obj U, ⊤)
  obtain ⟨hA, j, hjf, hj⟩ :=
    exists_isImmersion_prod_lift B S hS hZ U X f hX hls (A := A) (T.obj U).isoSpec
  let E := approxSystemOverS B S hS hZ A
  let D := prodDiagram X E
  let cR := approxRestrictionCone B S hS hZ A hA
  let c := prodCone X cR
  have hb : (⊥ : Subalgebra (ULift.{u} ℤ) A).FG := (Subalgebra.fg_iff_finiteType _).2 inferInstance
  let : Nonempty (ApproxIndex A ⊥) := ⟨⟨⊥, le_rfl, hb⟩⟩
  let : IsDirected (ApproxIndex A ⊥) (· ≤ ·) := approxIndex_isDirected ⊥
  have hSize : #(ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) < B.cutoff.ord.cof :=
    (mk_approxIndex_le A ⊥).trans_lt (max_lt hcard B.aleph0_lt_cutoff_cof)
  let i₀ : ApproxIndex A ⊥ := ⟨⊥, le_rfl, hb⟩
  let t : D ⟶ (Functor.const (ApproxIndex A ⊥)ᵒᵖ).obj X := prodDiagramFst X E
  have hcomm : c.π ≫ t = (Functor.const _).map (prod.fst : c.pt ⟶ X) :=
    prodCone_π_comp_prodDiagramFst X cR
  have hqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_obj B S hS (Scheme.compactSpace_of_isAffine _)
  have he := eventually_isImmersion_comp_limitπ_of_small B S hS hSize X hX D
    (approxProductStage_isAlgebraicSpace B S hS hZ A X hX) t c
    (prodCone_isLimit_of_directed X (approxRestrictionCone_isLimit B S hS hZ A hA) i₀)
    prod.fst hcomm
    (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hqc j
    (fun _ _ h ↦ approxProduct_transition_isAffineHom B S hS hZ A X hX h)
    (hjf ▸ hft) hj
  obtain ⟨i, hi⟩ := he.exists
  exact exists_isImmersion_affineSpaceOver_of_stage B S hS hZ A hA X _ f j hjf i hi

/-- **Stacks 088L** over a big fppf site whose size cutoff is a regular cardinal: an affine
scheme locally of finite type over a locally separated algebraic space admits an immersion
into affine `n`-space over that space.

Regularity of the cutoff discharges the cardinality side condition of
`exists_isImmersion_affineSpaceOver` for every `U`: the sections of an affine object of the
site are bounded by its size, which is below the cutoff, which is its own cofinality. -/
@[stacks 088L "verbatim, over a big fppf site whose size cutoff is a regular cardinal"]
theorem exists_isImmersion_affineSpaceOver_of_isRegular (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (hreg : B.cutoff.IsRegular)
    (U : BigFppfOver B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : yoneda.obj U ⟶ X)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hls : IsAbsolutelyLocallySeparated B S hS hZ X) :
    ∃ (n : ℕ) (j : yoneda.obj U ⟶ affineSpaceOver B S hS X n),
      j ≫ prod.fst = f ∧ IsImmersion B S hS j := by
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  refine exists_isImmersion_affineSpaceOver B S hS hZ U X f hU hX hft hls ?_
  refine (Scheme.mk_sections_le_size ((BigFppfOver.toScheme B S hS).obj U)
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩).trans_lt ?_
  exact lt_of_lt_of_le U.left.property hreg.2

/-- A stage `X ⨯ Spec Aᵢ` of the product system is quasi-separated when `X` is: the stage
`Spec Aᵢ`, an affine scheme over the terminal scheme, is quasi-separated over it, hence its
restriction is quasi-separated over `S`, so the projection `X ⨯ Spec Aᵢ ⟶ X`, a base change of
the structure morphism of that restriction, is quasi-separated (Stacks 04ZI, part (6), and
Stacks 04ZH, part (2)). -/
private theorem approxProductStage_isAbsolutelyQuasiSeparated (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u)
    [CommRing A] (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (i : ApproxIndex A (⊥ : Subalgebra (ULift.{u} ℤ) A)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (X ⨯ (approxSystemOverS B S hS hZ A).obj (op i)) := by
  let gBase : B.obj hS ⟶ B.obj hZ := B.inclusion.preimage (terminalIsTerminal.from S)
  let V := approxStageObj B hZ A i
  have hVsep : Scheme.IsSeparated ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) := by
    change Scheme.IsSeparated (Spec (.of i.1))
    infer_instance
  have hVqs : IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (yoneda.obj V) :=
    isQuasiSeparatedOver_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ _
      (isSeparatedOver_yoneda_obj B (⊤_ Scheme.{u}) hZ V hVsep)
  have hEqs : IsQuasiSeparatedOver B S hS ((approxSystemOverS B S hS hZ A).obj (op i)) :=
    isQuasiSeparatedOver_relocalizeRestrict B S hS (⊤_ Scheme.{u}) hZ gBase _ hVqs
  have hterm := isQuasiSeparated_of_isQuasiSeparatedOver B S hS hEqs
    (terminal.from ((approxSystemOverS B S hS hZ A).obj (op i)))
  have hfst : IsQuasiSeparated B S hS
      (prod.fst : X ⨯ (approxSystemOverS B S hS hZ A).obj (op i) ⟶ X) :=
    isQuasiSeparated_of_isPullback B S hS
      (IsPullback.of_hasBinaryProduct' X ((approxSystemOverS B S hS hZ A).obj (op i))).flip hterm
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (approxProductStage_isAlgebraicSpace B S hS hZ A X hX i) hqs hfst

/-- **Stacks 088L.**  Let `f : U ⟶ X` be a morphism of algebraic spaces over `S` with `U` an
affine scheme, `f` locally of finite type, and `X` quasi-separated and locally separated.
Then there is an immersion `U ⟶ 𝔸ⁿ_X` over `X`.

Writing `U = Spec A` with `A` the filtered union of its finite type `ℤ`-subalgebras `Aᵢ`, the
graph `U ⟶ X ⨯ U` is an immersion because `X` is locally separated (Stacks 03KO), and
`X ⨯ U` is the directed limit of the stages `X ⨯ Spec Aᵢ`, which have affine transition
morphisms and are quasi-separated because `X` is.  Stacks 0828, part (2), which places no bound
on the index set, then makes `U ⟶ X ⨯ Spec Aᵢ` an immersion for some `i`, and `Spec Aᵢ` is a
closed subscheme of affine space over `ℤ`. -/
@[stacks 088L]
theorem exists_isImmersion_affineSpaceOver_of_isAbsolutelyQuasiSeparated (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : yoneda.obj U ⟶ X)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hls : IsAbsolutelyLocallySeparated B S hS B.contains_terminal X) :
    ∃ (n : ℕ) (j : yoneda.obj U ⟶ affineSpaceOver B S hS X n),
      j ≫ prod.fst = f ∧ IsImmersion B S hS j := by
  classical
  let hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let T := BigFppfOver.toScheme B S hS
  let : IsAffine (T.obj U) := hU
  let A : Type u := Γ(T.obj U, ⊤)
  obtain ⟨hA, j, hjf, hj⟩ :=
    exists_isImmersion_prod_lift B S hS hZ U X f hX hls (A := A) (T.obj U).isoSpec
  let E := approxSystemOverS B S hS hZ A
  let D := prodDiagram X E
  let cR := approxRestrictionCone B S hS hZ A hA
  let c := prodCone X cR
  have hb : (⊥ : Subalgebra (ULift.{u} ℤ) A).FG := (Subalgebra.fg_iff_finiteType _).2 inferInstance
  let : Nonempty (ApproxIndex A ⊥) := ⟨⟨⊥, le_rfl, hb⟩⟩
  let : IsDirected (ApproxIndex A ⊥) (· ≤ ·) := approxIndex_isDirected ⊥
  let i₀ : ApproxIndex A ⊥ := ⟨⊥, le_rfl, hb⟩
  let t : D ⟶ (Functor.const (ApproxIndex A ⊥)ᵒᵖ).obj X := prodDiagramFst X E
  have hcomm : c.π ≫ t = (Functor.const _).map (prod.fst : c.pt ⟶ X) :=
    prodCone_π_comp_prodDiagramFst X cR
  have hqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_obj B S hS (Scheme.compactSpace_of_isAffine _)
  have he := eventually_isImmersion_comp_limitπ B S hS X hX D
    (approxProductStage_isAlgebraicSpace B S hS hZ A X hX) t c
    (prodCone_isLimit_of_directed X (approxRestrictionCone_isLimit B S hS hZ A hA) i₀)
    prod.fst hcomm
    (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hqc j
    (fun _ _ h ↦ approxProduct_transition_isAffineHom B S hS hZ A X hX h)
    (approxProductStage_isAbsolutelyQuasiSeparated B S hS hZ A X hX hqs)
    (hjf ▸ hft) hj
  obtain ⟨i, hi⟩ := he.exists
  exact exists_isImmersion_affineSpaceOver_of_stage B S hS hZ A hA X _ f j hjf i hi

end AlgebraicGeometry.Space

end
