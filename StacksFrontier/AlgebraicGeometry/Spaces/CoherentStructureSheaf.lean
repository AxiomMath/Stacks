module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The structure sheaf of a locally Noetherian algebraic space is coherent

Let `F` be an algebraic space over a scheme `S` which is locally Noetherian, in the sense of
Stacks 03E6 for the étale-local scheme property `AlgebraicGeometry.IsLocallyNoetherian`.  Its
structure sheaf is then a coherent `𝒪_F`-module.  This is the structure-sheaf assertion of
Stacks 07UB.

Quasi-coherence and finite type of the structure sheaf hold on any ringed site at all and are
`SheafOfModules.isQuasicoherentOnSite_unit` and `PresheafOfModules.isFiniteType_unit`.  What the
locally Noetherian hypothesis buys is the remaining clause of
`SheafOfModules.IsCoherentOnSite`: the relations among a finite family of sections of `𝒪_F` over
an étale chart form a module of finite type on the slice site at that chart.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteType_relations_unit`: on any ringed site whose objects
  are covered by objects with Noetherian ring of sections and mutually flat restriction maps,
  the relations among a finite family of sections of the structure sheaf are of finite type on
  the slice site.
* `AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`: every étale chart of a
  locally Noetherian algebraic space is covered by Noetherian affine étale charts.
* `AlgebraicGeometry.Space.isCoherent_structureSheaf`: **the structure-sheaf assertion of
  Stacks 07UB**, as an instance.

## Implementation notes

The covering family of the slice site at a chart `U` witnessing finite type is the family of
*all* objects of `Over U` whose underlying scheme is affine with Noetherian ring of global
sections.  That this family covers the slice is
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`, which is where the locally
Noetherian hypothesis enters, in two steps and in the only form in which it is available.

Local Noetherianity is *not* known in this library to be local for the étale precoverage —
`CategoryTheory.ObjectProperty.IsLocal (fun X => IsLocallyNoetherian X)
Scheme.etalePrecoverage` is not available, since it contains descent of Noetherianity along a
surjective étale morphism — so an arbitrary étale chart of `F` cannot be asserted to be locally
Noetherian, and only the atlas supplied by `AlgebraicGeometry.Space.HasEtaleLocalProperty` is.
The two steps therefore are: every chart `W` is covered by the single chart `W ×_F U₀`, where
`U₀` is that atlas, and `W ×_F U₀` *is* locally Noetherian because it is étale over `U₀`
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`); and a chart over `W ×_F U₀` is
in turn covered by affine charts, by cover density of the affine étale charts (Stacks 04JS),
each of which is locally Noetherian for the same reason and hence, being affine, has Noetherian
ring of global sections.  Only the first step needs the hypothesis.

Generation on a Noetherian object `V` of the site is finite generation of the kernel of
`𝒪(V) ^ n → 𝒪(V)`, available because `𝒪(V)` is Noetherian; propagating it to an object over `V`
is flat base change of that kernel.  For the small étale site of an algebraic space flatness
holds because a morphism of étale charts is étale on schemes
(`AlgebraicGeometry.Space.etale_toScheme_toOver_map`), hence flat, and because the charts may
be taken affine.

Both halves of that argument are the `M := 𝒪(V)` case of a statement about an arbitrary module
proved in `StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules`, a module upstream of this one,
and are used from there rather than restated: finite generation of the relations is
`IsNoetherianRing.exists_fin_generating_relations`, and flat base change of them is
`Module.Flat.exists_coeffs_of_sum_tmul_eq_zero`.  The latter is stated for a flat algebra and a
vanishing tensor expression, so the flat restriction map `𝒪(V) → 𝒪(A)` of the hypothesis `hflat`
is turned into an algebra by `algebraize` and the vanishing of the relation is transported
across `TensorProduct.rid`; that is the only bridging the reuse costs.

The ring of sections of `Stacks.SheafOfModules.Tensor.ringSheaf X.O` is commutative — the
structure sheaf of a ringed site takes values in `CommRingCat` and only the sheaf of rings over
which modules are taken forgets that — but not syntactically so;
`Stacks.SheafOfModules.Tensor.ringSheafSectionCommRing` records the instance.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u v w

/-! ### The relations presheaf of the structure sheaf of a ringed site, sectionwise -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  {U : C} {n : ℕ} (s : Fin n → (SheafOfModules.unit R).val.obj (op U))

/-- Restriction in the presheaf of relations among sections of the structure sheaf is
componentwise restriction of the coefficients. -/
theorem relations_unit_restrict_val {V W : Over U} (h : W ⟶ V)
    (y : (PresheafOfModules.relations (SheafOfModules.unit R).val s).obj (op V)) (i : Fin n) :
    (((PresheafOfModules.relations (SheafOfModules.unit R).val s).restrictₛₗ h.op) y).val i
      = R.obj.map h.left.op (y.val i) := rfl

/-- A finite sum of relations is computed componentwise. -/
theorem relations_unit_sum_val {V : Over U} {k : ℕ} (t : Finset (Fin k))
    (c : Fin k → R.obj.obj (op V.left))
    (y : Fin k → (PresheafOfModules.relations (SheafOfModules.unit R).val s).obj (op V))
    (i : Fin n) :
    ((∑ j ∈ t, c j • y j :
        (PresheafOfModules.relations (SheafOfModules.unit R).val s).obj (op V)).val i)
      = ∑ j ∈ t, c j * (y j).val i := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl

/-- A tuple of coefficients is a relation among the restricted sections of the structure sheaf
exactly when the corresponding linear combination vanishes. -/
theorem mem_relations_unit_iff {V : Over U} (y : Fin n → R.obj.obj (op V.left)) :
    y ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op V.left))
        (fun i ↦ (SheafOfModules.unit R).val.restrictₛₗ V.hom.op (s i))) ↔
      ∑ i, y i * R.obj.map V.hom.op (s i) = 0 := by
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  rfl

end SheafOfModules

namespace AlgebraicGeometry

/-- Restriction along a composite in a presheaf of rings is the composite of the two
restrictions. -/
theorem presheaf_ringCat_map_comp_apply {D : Type*} [Category* D] (P : Dᵒᵖ ⥤ RingCat.{w})
    {X Y Z : D} (α : X ⟶ Y) (β : Y ⟶ Z) (x : P.obj (op Z)) :
    P.map (α ≫ β).op x = P.map α.op (P.map β.op x) := by
  rw [show (α ≫ β).op = β.op ≫ α.op from rfl, P.map_comp]
  rfl

namespace RingedSite

/-- Generation of the relations among a finite family of sections of the structure sheaf of a
ringed site, on a `Good` object `V` of a slice site: the Noetherian hypothesis at `V` gives
finitely many generating relations over `V`, and flat base change carries them to the `Good`
objects covering any object over `V`. -/
theorem exists_generators_relations_unit (X : RingedSite.{u, v, w}) (Good : X.C → Prop)
    (hcov : ∀ W : X.C, ∃ Sv : Sieve W, Sv ∈ X.J W ∧
      ∀ ⦃Y : X.C⦄ (h : Y ⟶ W), Sv h →
        ∃ (A : X.C) (l : Y ⟶ A) (m : A ⟶ W), Good A ∧ h = l ≫ m)
    (hnoeth : ∀ A : X.C, Good A → IsNoetherianRing ↥((ringSheaf X.O).obj.obj (op A)))
    (hflat : ∀ {A A' : X.C} (h : A' ⟶ A), Good A → Good A' →
      RingHom.Flat ((ringSheaf X.O).obj.map h.op).hom)
    {U : X.C} {n : ℕ} (s : Fin n → (SheafOfModules.unit (ringSheaf X.O)).val.obj (op U))
    (V : Over U) (hV : Good V.left) :
    ∃ (k : ℕ) (σ : Fin k →
        (PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val s).obj (op V)),
      PresheafOfModules.Generates (X.J.over U)
        (PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val s) σ := by
  classical
  have hVn : IsNoetherianRing ↥((ringSheaf X.O).obj.obj (op V.left)) := hnoeth _ hV
  obtain ⟨k, g, hg0, hgspan⟩ := IsNoetherianRing.exists_fin_generating_relations
    (A := ↥((ringSheaf X.O).obj.obj (op V.left)))
    (M := ↥((ringSheaf X.O).obj.obj (op V.left)))
    (fun i => (ringSheaf X.O).obj.map V.hom.op (s i))
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin k →
      (PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val s).obj (op V),
      ∀ j i, (σ j).val i = g j i :=
    ⟨fun j => ⟨g j, (SheafOfModules.mem_relations_unit_iff (ringSheaf X.O) s (g j)).2 (hg0 j)⟩,
      fun _ _ => rfl⟩
  refine ⟨k, σ, ?_⟩
  intro W f t
  obtain ⟨Sv, hSv, hfac⟩ := hcov W.left
  refine ⟨(Sieve.overEquiv W).symm Sv, X.J.overEquiv_symm_mem_over W Sv hSv, ?_⟩
  intro Z q hq
  rw [Sieve.overEquiv_symm_iff] at hq
  obtain ⟨A, l, m, hA, hleft⟩ := hfac q.left hq
  -- the `Good` object `A`, as an object of the slice over `U`
  let A' : Over U := Over.mk (m ≫ W.hom)
  let mA : A' ⟶ W := Over.homMk m
  let lA : Z ⟶ A' := Over.homMk l (by
    show l ≫ m ≫ W.hom = Z.hom
    rw [← Category.assoc, ← hleft]
    exact Over.w q)
  have hA' : Good A'.left := hA
  have hq2 : q = lA ≫ mA := Over.OverMorphism.ext hleft
  have hleft' : q.left = lA.left ≫ mA.left := hleft
  -- restricting `t` to `A` gives a relation over `A`
  have hrel : ∑ i, (ringSheaf X.O).obj.map mA.left.op (t.val i) *
      (ringSheaf X.O).obj.map (mA ≫ f).left.op
        ((ringSheaf X.O).obj.map V.hom.op (s i)) = 0 := by
    have ht := (SheafOfModules.mem_relations_unit_iff (ringSheaf X.O) s (V := A')
      (fun i => (ringSheaf X.O).obj.map mA.left.op (t.val i))).1
        (((PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val s).restrictₛₗ
          mA.op) t).2
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ht
    refine congrArg (fun z => (ringSheaf X.O).obj.map mA.left.op (t.val i) * z) ?_
    exact (presheaf_ringCat_map_comp_apply (ringSheaf X.O).obj (mA ≫ f).left V.hom
        (s i)).symm.trans
      (congrArg (fun α : A'.left ⟶ U => (ringSheaf X.O).obj.map α.op (s i)) (Over.w (mA ≫ f)))
  -- flat base change of the generating relations, through the equational criterion for the
  -- vanishing of a tensor expression
  have hφ : RingHom.Flat ((ringSheaf X.O).obj.map (mA ≫ f).left.op).hom :=
    hflat (mA ≫ f).left hV hA'
  algebraize [((ringSheaf X.O).obj.map (mA ≫ f).left.op).hom]
  have hten : ∑ i, (ringSheaf X.O).obj.map mA.left.op (t.val i)
      ⊗ₜ[↥((ringSheaf X.O).obj.obj (op V.left))] (ringSheaf X.O).obj.map V.hom.op (s i) = 0 := by
    refine (TensorProduct.rid _ _).injective ?_
    rw [map_sum, map_zero]
    simpa only [TensorProduct.rid_tmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      mul_comm] using hrel
  obtain ⟨c, hc⟩ : ∃ c : Fin k → ↥((ringSheaf X.O).obj.obj (op A'.left)), ∀ i,
      (ringSheaf X.O).obj.map mA.left.op (t.val i) =
        ∑ j, c j * (ringSheaf X.O).obj.map (mA ≫ f).left.op (g j i) :=
    Module.Flat.exists_coeffs_of_sum_tmul_eq_zero
      (fun i => (ringSheaf X.O).obj.map V.hom.op (s i)) g hgspan
      (fun i => (ringSheaf X.O).obj.map mA.left.op (t.val i)) hten
  refine ⟨fun j => (ringSheaf X.O).obj.map lA.left.op (c j), ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  have hσq : ∀ j, (((PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val
      s).restrictₛₗ (q ≫ f).op) (σ j)).val i = (ringSheaf X.O).obj.map (q ≫ f).left.op (g j i) :=
    fun j =>
      (SheafOfModules.relations_unit_restrict_val (ringSheaf X.O) s (q ≫ f) (σ j) i).trans
        (congrArg _ (hσ j i))
  refine ((SheafOfModules.relations_unit_sum_val (ringSheaf X.O) s _ _ _ i).trans
    (Finset.sum_congr rfl fun j _ => congrArg _ (hσq j))).trans
    (Eq.trans ?_ (SheafOfModules.relations_unit_restrict_val (ringSheaf X.O) s q t i).symm)
  have hop : (q ≫ f).left = lA.left ≫ (mA ≫ f).left := by
    rw [hq2]
    exact Category.assoc _ _ _
  rw [hop, hleft', presheaf_ringCat_map_comp_apply (ringSheaf X.O).obj lA.left mA.left]
  simp only [presheaf_ringCat_map_comp_apply (ringSheaf X.O).obj lA.left (mA ≫ f).left]
  rw [hc i, map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm

/-- **The relations clause of coherence for the structure sheaf of a ringed site.**  Suppose
that every object of the site is covered by morphisms factoring through objects with the
property `Good`, that the ring of sections at a `Good` object is Noetherian, and that
restriction between `Good` objects is flat.  Then the relations among a finite family of
sections of the structure sheaf over any object `U` are of finite type on the slice site at
`U`.

The covering family is all of the objects of the slice whose underlying object of the site is
`Good`.  That it covers the slice is
`CategoryTheory.GrothendieckTopology.coversTop_over_subtype`, which mentions no sheaf of
modules; generation on such an object is
`AlgebraicGeometry.RingedSite.exists_generators_relations_unit`. -/
theorem isFiniteType_relations_unit (X : RingedSite.{u, v, w}) (Good : X.C → Prop)
    (hcov : ∀ W : X.C, ∃ Sv : Sieve W, Sv ∈ X.J W ∧
      ∀ ⦃Y : X.C⦄ (h : Y ⟶ W), Sv h →
        ∃ (A : X.C) (l : Y ⟶ A) (m : A ⟶ W), Good A ∧ h = l ≫ m)
    (hnoeth : ∀ A : X.C, Good A → IsNoetherianRing ↥((ringSheaf X.O).obj.obj (op A)))
    (hflat : ∀ {A A' : X.C} (h : A' ⟶ A), Good A → Good A' →
      RingHom.Flat ((ringSheaf X.O).obj.map h.op).hom)
    (U : X.C) (n : ℕ) (s : Fin n → (SheafOfModules.unit (ringSheaf X.O)).val.obj (op U)) :
    PresheafOfModules.IsFiniteType (X.J.over U)
      (PresheafOfModules.relations (SheafOfModules.unit (ringSheaf X.O)).val s) :=
  ⟨{V : Over U // Good V.left}, Subtype.val, X.J.coversTop_over_subtype Good U hcov,
    fun Vs => exists_generators_relations_unit X Good hcov hnoeth hflat s Vs.1 Vs.2⟩

end RingedSite

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Noetherian affine charts cover -/

/-- Local Noetherianity of the scheme underlying an étale chart passes to any chart over it: a
morphism of étale charts is étale on schemes, hence locally of finite type. -/
theorem isLocallyNoetherian_of_chart_hom {A W : SmallEtale B S hS F} (f : A ⟶ W)
    (hW : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W))) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj A)) := by
  have he := etale_toScheme_toOver_map B S hS F f
  have := hW
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f))

/-- A one-element family of étale charts whose morphism is surjective on points generates a
covering sieve of the small étale site. -/
theorem sieve_generate_singleton_chart_mem_topology {P W : SmallEtale B S hS F} (c : P ⟶ W)
    (hcs : Surjective ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map c))) :
    Sieve.generate (Presieve.singleton c) ∈ SmallEtale.topology B S hS F W := by
  have hpre : Presieve.singleton c ∈ SmallEtale.precoverage B S hS F W := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact B.singleton_mem_etalePrecoverage _ hcs (etale_toScheme_toOver_map B S hS F c)
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- Every étale chart of a locally Noetherian algebraic space carries a covering sieve each of
whose members factors through an étale chart whose underlying scheme is affine with Noetherian
ring of global sections.

The chart is first covered by its fibre product with the atlas supplied by local Noetherianity,
which is locally Noetherian because it is étale over that atlas; a chart over the fibre product
is then covered by affine charts, by cover density of the affine étale charts, and each of those
is locally Noetherian for the same reason. -/
theorem exists_covering_through_noetherianAffine (hF : IsAlgebraicSpace B S hS F)
    (hLN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (W : SmallEtale B S hS F) :
    ∃ Sv : Sieve W, Sv ∈ SmallEtale.topology B S hS F W ∧
      ∀ ⦃Y : SmallEtale B S hS F⦄ (h : Y ⟶ W), Sv h →
        ∃ (A : SmallEtale B S hS F) (l : Y ⟶ A) (m : A ⟶ W),
          (IsAffine ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj A)) ∧
            IsNoetherianRing (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj A))))) ∧ h = l ≫ m := by
  obtain ⟨U₀, a, haₛ, haₑ, hN⟩ := hLN
  let T := BigFppfOver.toScheme B S hS
  let L := SmallEtale.toOver B S hS F
  let G := AffineEtale.inclusion B S hS F
  have hdense : G.IsCoverDense (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense'
  let Sv : Sieve W :=
    { arrows := fun Y h => ∃ (A : SmallEtale B S hS F) (l : Y ⟶ A) (m : A ⟶ W),
        (IsAffine (T.obj (L.obj A)) ∧
          IsNoetherianRing (Scheme.Γ.obj (op (T.obj (L.obj A))))) ∧ h = l ≫ m
      downward_closed := by
        rintro Y Z h ⟨A, l, m, hA, rfl⟩ g
        exact ⟨A, g ≫ l, m, hA, by simp⟩ }
  refine ⟨Sv, ?_, fun Y h hh => hh⟩
  -- the fibre product of `W` with the atlas, as an étale chart over `W`
  let hrep := W.property.rep
  let p := hrep.fst a
  let q := hrep.snd a
  have hpull := hrep.isPullback a
  let r : hrep.pullback a ⟶ W.obj.left := yoneda.preimage p
  have hpb : IsPullback (yoneda.map q) (yoneda.map r) a W.obj.hom :=
    yoneda.map_preimage p ▸ hpull.flip
  have hrSurjective : Surjective (T.map r) := haₛ.property W.obj.hom (yoneda.map q) r hpb
  have hrEtale : Etale (T.map r) := haₑ.property _ _ r hpb
  have hqEtale : Etale (T.map q) := W.property.property a p q hpull
  have hPN : IsLocallyNoetherian (T.obj (hrep.pullback a)) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map q)
  let Pc : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map r ≫ W.obj.hom),
      etale_comp_of_scheme B S hS r W.obj.hom hrEtale W.property⟩
  let c : Pc ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk r rfl)
  have hPcN : IsLocallyNoetherian (T.obj (L.obj Pc)) := hPN
  have hcs : Surjective (T.map (L.map c)) := hrSurjective
  refine (SmallEtale.topology B S hS F).transitive
    (sieve_generate_singleton_chart_mem_topology B S hS F c hcs) Sv ?_
  rintro Z f ⟨Y', g₁, g₂, hg₂, rfl⟩
  obtain ⟨⟩ := hg₂
  have hZN : IsLocallyNoetherian (T.obj (L.obj Z)) :=
    isLocallyNoetherian_of_chart_hom B S hS F g₁ hPcN
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (G.is_cover_of_isCoverDense (SmallEtale.topology B S hS F) Z)
  rintro Y k ⟨⟨A₀, lift, map, fac⟩⟩
  have hAaff : IsAffine (T.obj (L.obj (G.obj A₀))) := AffineEtale.isAffine_toScheme B S hS F A₀
  have hAN : IsLocallyNoetherian (T.obj (L.obj (G.obj A₀))) :=
    isLocallyNoetherian_of_chart_hom B S hS F map hZN
  refine ⟨G.obj A₀, lift, map ≫ (g₁ ≫ c), ⟨hAaff, ?_⟩, ?_⟩
  · exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (T.obj (L.obj (G.obj A₀)))⟩
  · simp [← fac]

/-! ### Coherence of the structure sheaf -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- Restriction of sections of the structure sheaf along a morphism of étale charts between
affine charts is a flat ring homomorphism: the morphism of schemes is étale, hence flat, and
flatness of a morphism of affine schemes is flatness of the induced homomorphism of rings of
global sections. -/
theorem flat_ringSheaf_map {V W : (smallEtaleRingedSite B S hS F hF).C} (h : W ⟶ V)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W))) :
    RingHom.Flat
      ((ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map h.op).hom := by
  have he := etale_toScheme_toOver_map B S hS F h
  have := hV
  have := hW
  have hfl : Flat ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h)) :=
    inferInstance
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)
    (f := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h))).1 hfl

/-- **Stacks 07UB, the structure sheaf.**  The structure sheaf of a locally Noetherian
algebraic space is a coherent `𝒪_F`-module.

Quasi-coherence is `SheafOfModules.isQuasicoherentOnSite_unit` and finite type is
`PresheafOfModules.isFiniteType_unit`, neither of which needs the hypothesis; the relations
clause is `AlgebraicGeometry.RingedSite.isFiniteType_relations_unit`, applied to the covering
by Noetherian affine charts of
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`. -/
@[stacks 07UB "structure sheaf"]
instance isCoherent_structureSheaf
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] :
    IsCoherent B S hS F hF
      (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
  isCoherent_structureSheaf_of_relations B S hS F hF
    (RingedSite.isFiniteType_relations_unit (smallEtaleRingedSite B S hS F hF)
      (fun A => IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj A)) ∧
        IsNoetherianRing (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj A)))))
      (exists_covering_through_noetherianAffine B S hS F hF Fact.out)
      (fun _ hA => hA.2) (fun h hA hA' => flat_ringSheaf_map B S hS F hF h hA.1 hA'.1))

end Space

end AlgebraicGeometry

end
