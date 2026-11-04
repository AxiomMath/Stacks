module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteEtaleCovers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The ringed site `(C, Λ)` of schemes locally of finite type over `S`

Let `S` be a scheme and `Λ` a ring. Stacks 0DC6 considers the full subcategory `C` of the big
étale site `(Sch/S)_ét` consisting of the schemes locally of finite type over `S`, with the étale
topology, ringed by the constant sheaf `Λ`. This file sets up that ringed site in the
single-universe shape `AlgebraicGeometry.RingedSite.{u + 1, u + 1, u + 1}` that the conditions of
Stacks 0DC1 (`Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily`) are stated for, and
records its coverings.

## Main definitions

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.Lifted`: the category `C` with its morphism
  types lifted to the universe of its objects (`CategoryTheory.ULiftHom`).
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.liftedTopology`: the étale topology on it,
  transported along the equivalence `C ≌ Lifted S`.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.ringedSite`: the ringed site `(C, Λ)`, whose
  structure sheaf is the constant sheaf with value `Λ`.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.IsQuasiCompactEtaleCovering`: the families
  `{V_i ⟶ V}` of étale morphisms that are jointly surjective and have quasi-compact members, the
  system `Cov_V` of the source.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.quasiCompactEtaleCoverings`: these families
  form a cofinal system of coverings of `V`.

## Implementation notes

The objects of `C` are schemes, in `Type (u + 1)`, while its morphisms are in `Type u`; the
conditions of Stacks 0DC1 are stated for a ringed site whose objects and morphisms share one
universe. `CategoryTheory.ULiftHom` keeps the objects and lifts each morphism type, which is an
equivalence of categories `ULiftHom.equiv`, and the topology is transported along it; nothing
about the site changes. The constant sheaf is that of `ULift Λ`, which is `Λ` in the universe of
the sheaf's sections.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0DC1](https://stacks.math.columbia.edu/tag/0DC1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable (S : Scheme.{u})

/-- The schemes locally of finite type over `S`, with morphism types lifted to `Type (u + 1)`. -/
abbrev Lifted : Type (u + 1) := ULiftHom.{u + 1} (LocallyFiniteTypeEtale S)

/-- The equivalence between the site and its lifted copy. -/
abbrev liftedEquiv : LocallyFiniteTypeEtale S ≌ Lifted S := ULiftHom.equiv

/-- The étale topology on the lifted site, transported along `liftedEquiv`. -/
abbrev liftedTopology : GrothendieckTopology (Lifted S) :=
  (liftedEquiv S).inverse.inducedTopology (topology S)

/-- The underlying scheme of an object of the lifted site. -/
abbrev liftedForget : Lifted S ⥤ Scheme.{u} := (liftedEquiv S).inverse ⋙ forget S

variable {S}

/-- A sieve of the lifted site is covering if and only if its image is a covering sieve of the
site. -/
lemma mem_liftedTopology_iff {V : Lifted S} (R : Sieve V) :
    R ∈ liftedTopology S V ↔
      R.functorPushforward (liftedEquiv S).inverse ∈ topology S ((liftedEquiv S).inverse.obj V) :=
  Functor.mem_inducedTopology_iff_of_isCoverDense _ _ R

/-- **A sieve of the lifted site is covering if and only if every point of the underlying scheme
lies in the image of an étale morphism belonging to it.** -/
theorem mem_liftedTopology_iff_forall {V : Lifted S} (R : Sieve V) :
    R ∈ liftedTopology S V ↔ ∀ x : (liftedForget S).obj V, ∃ (Z : Lifted S) (f : Z ⟶ V),
      Etale ((liftedForget S).map f) ∧ x ∈ Set.range ((liftedForget S).map f).base ∧
        R.arrows f := by
  rw [mem_liftedTopology_iff, mem_topology_iff_hasEtalePointCover]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨Z, f, het, hx, ⟨Z', g, a, hg, hfac⟩⟩ := h x
    subst hfac
    exact ⟨_, (liftedEquiv S).functor.map a ≫ g, het, hx, R.downward_closed hg _⟩
  · obtain ⟨Z, f, het, hx, hf⟩ := h x
    exact ⟨_, (liftedEquiv S).inverse.map f, het, hx, ⟨Z, f, 𝟙 _, hf, by simp⟩⟩

/-- A family of morphisms of the lifted site is a member of `Cov_V`: every member is étale and
quasi-compact, and the family is jointly surjective. -/
def IsQuasiCompactEtaleCovering {V : Lifted S} (𝒰 : PreZeroHypercover.{u + 1} V) : Prop :=
  (∀ i, Etale ((liftedForget S).map (𝒰.f i))) ∧
    (∀ x : (liftedForget S).obj V, ∃ i, x ∈ Set.range ((liftedForget S).map (𝒰.f i)).base) ∧
      ∀ i, IsQuasiCompact ((liftedEquiv S).inverse.obj (𝒰.X i))

/-- A member of `Cov_V` is a covering. -/
lemma IsQuasiCompactEtaleCovering.mem {V : Lifted S} {𝒰 : PreZeroHypercover.{u + 1} V}
    (h : IsQuasiCompactEtaleCovering 𝒰) : 𝒰.sieve₀ ∈ liftedTopology S V := by
  rw [mem_liftedTopology_iff_forall]
  intro x
  obtain ⟨i, hi⟩ := h.2.1 x
  exact ⟨_, 𝒰.f i, h.1 i, hi, 𝒰.sieve₀_f i⟩

/-- The canonical affine open cover of an object of the lifted site. -/
def affineHypercover (V : Lifted S) : PreZeroHypercover.{u + 1} V where
  I₀ := ULift.{u + 1} ((liftedEquiv S).inverse.obj V).obj.left.affineCover.I₀
  X i := (liftedEquiv S).functor.obj (affineObj ((liftedEquiv S).inverse.obj V) i.down)
  f i := (liftedEquiv S).functor.map (affineMap ((liftedEquiv S).inverse.obj V) i.down)

/-- The canonical affine open cover is a member of `Cov_V`. -/
lemma isQuasiCompactEtaleCovering_affineHypercover (V : Lifted S) :
    IsQuasiCompactEtaleCovering (affineHypercover V) := by
  refine ⟨fun i ↦ ?_, fun x ↦ ?_, fun i ↦ isQuasiCompact_affineObj _ i.down⟩
  · show Etale (((liftedEquiv S).inverse.obj V).obj.left.affineCover.f i.down)
    infer_instance
  · exact ⟨⟨((liftedEquiv S).inverse.obj V).obj.left.affineCover.idx x⟩,
      ((liftedEquiv S).inverse.obj V).obj.left.affineCover.covers x⟩

/-- A morphism through a member of a family factors through a member. -/
private lemma exists_comp_eq_of_ofArrows {V : Lifted S} (𝒰 : PreZeroHypercover.{u + 1} V)
    {Y Z : Lifted S} {b : Y ⟶ V} (hb : Presieve.ofArrows 𝒰.X 𝒰.f b) (a : Z ⟶ Y) :
    ∃ (i : 𝒰.I₀) (c : Z ⟶ 𝒰.X i), c ≫ 𝒰.f i = a ≫ b := by
  rcases hb with ⟨i⟩
  exact ⟨i, a, rfl⟩

/-- **`Cov_V` is cofinal**: every covering of an object of the lifted site is refined by an
étale covering whose members are quasi-compact. -/
lemma exists_isQuasiCompactEtaleCovering_hom {V : Lifted S} (𝒰 : PreZeroHypercover.{u + 1} V)
    (h𝒰 : 𝒰.sieve₀ ∈ liftedTopology S V) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} V, IsQuasiCompactEtaleCovering 𝒱 ∧ Nonempty (𝒱.Hom 𝒰) := by
  rw [mem_liftedTopology_iff_forall] at h𝒰
  choose Z f het hx hf using h𝒰
  choose Y a b hb hab using hf
  choose i c hc using fun x ↦ exists_comp_eq_of_ofArrows 𝒰 (hb x) (a x)
  choose z hz using hx
  let T : (liftedForget S).obj V → LocallyFiniteTypeEtale S := fun x ↦
    (liftedEquiv S).inverse.obj (Z x)
  let A : ∀ x, (T x).obj.left.affineCover.I₀ := fun x ↦ (T x).obj.left.affineCover.idx (z x)
  let g : ∀ x, (liftedEquiv S).functor.obj (affineObj (T x) (A x)) ⟶ Z x :=
    fun x ↦ (liftedEquiv S).functor.map (affineMap (T x) (A x))
  let 𝒱 : PreZeroHypercover.{u + 1} V :=
    { I₀ := ULift.{u + 1} ((liftedForget S).obj V)
      X x := (liftedEquiv S).functor.obj (affineObj (T x.down) (A x.down))
      f x := g x.down ≫ f x.down }
  refine ⟨𝒱, ⟨fun x ↦ ?_, fun x ↦ ⟨⟨x⟩, ?_⟩, fun x ↦ isQuasiCompact_affineObj _ _⟩,
    ⟨{ s₀ x := i x.down
       h₀ x := g x.down ≫ c x.down
       w₀ x := by
         show (g x.down ≫ c x.down) ≫ 𝒰.f (i x.down) = g x.down ≫ f x.down
         rw [Category.assoc, hc, hab] }⟩⟩
  · show Etale ((T x.down).obj.left.affineCover.f (A x.down) ≫ (liftedForget S).map (f x.down))
    have := het x.down
    infer_instance
  · obtain ⟨w, hw⟩ := (T x).obj.left.affineCover.covers (z x)
    refine ⟨w, ?_⟩
    show ((liftedForget S).map (f x)).base
      (((T x).obj.left.affineCover.f (A x)).base w) = x
    rw [hw, hz]

variable (S) in
/-- **The system `Cov_V`** of Stacks 0DC6: the étale coverings `{V_i ⟶ V}` with every `V_i`
quasi-compact, as a cofinal system of coverings of `V`. -/
def quasiCompactEtaleCoverings (V : Lifted S) :
    Stacks.Cohomology.CofinalCoveringSystem (liftedTopology S) V where
  cov := {𝒰 | IsQuasiCompactEtaleCovering 𝒰}
  isCover _ h := h.mem
  cofinal 𝒰 h := exists_isQuasiCompactEtaleCovering_hom 𝒰 h

variable (S) in
/-- **The ringed site `(C, Λ)` of Stacks 0DC6**: the schemes locally of finite type over `S`
with the étale topology, ringed by the constant sheaf `Λ`. -/
abbrev ringedSite (Λ : Type u) [CommRing Λ] : RingedSite.{u + 1, u + 1, u + 1} where
  C := Lifted S
  J := liftedTopology S
  O := (constantSheaf (liftedTopology S) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} Λ))

/-- The structure map `Λ ⟶ Λ(Z)` of the constant sheaf. -/
def constantMap (Λ : Type u) [CommRing Λ] (Z : Lifted S) :
    CommRingCat.of (ULift.{u + 1} Λ) ⟶ (ringedSite S Λ).O.obj.obj (Opposite.op Z) :=
  (toSheafify (liftedTopology S)
    ((Functor.const _).obj (CommRingCat.of (ULift.{u + 1} Λ)))).app (Opposite.op Z)

/-- **The order of a finite ring `Λ` vanishes in every ring of sections of the constant sheaf
`Λ`.** -/
lemma natCast_card_eq_zero (Λ : Type u) [CommRing Λ] [Finite Λ] (Z : Lifted S) :
    ((Nat.card Λ : ℕ) : (ringedSite S Λ).O.obj.obj (Opposite.op Z)) = 0 := by
  have : ((Nat.card Λ : ℕ) : ULift.{u + 1} Λ) = 0 := by
    apply (ULift.ringEquiv (R := Λ)).injective
    rw [map_natCast, map_zero]
    have := Fintype.ofFinite Λ
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero Λ
  rw [← map_natCast (constantMap Λ Z).hom, this, map_zero]

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
