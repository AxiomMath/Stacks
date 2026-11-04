module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.SetTheory.Cardinal.Rat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanFractionalSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSectionProjections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SparseEmbeddingSystem
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# A representable morphism to a McQuillan space with non-McQuillan source

There is a representable morphism `f : X ⟶ Y` of affine formal algebraic spaces with `Y` McQuillan
and `X` not McQuillan.

The example is built from the system of rings of
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanFractionalSystem`, applied to the inverse
system of free vector spaces on the injections `s ↪ ℕ` with infinite complement, `s` running over
the countable subsets of an uncountable set. The target is `Y = colim Spec(Aᵢ)`, whose stage rings
are the quotients `Aᵢ = P/𝔍ᵢ` of one ring `P`, so that the section projections of this
presentation are surjective and `Y` is McQuillan. The source is `X = colim Spec(Rᵢ)` with
`Rᵢ = Aᵢ ⊕ Mᵢ`; since `Rⱼ = Rᵢ ⊗_{Aᵢ} Aⱼ`, the morphism `X ⟶ Y` induced by `Aᵢ → Rᵢ` has cartesian
stage squares and is representable, with affine represented base changes. The stage rings `Rᵢ`
surject compatibly onto the vector spaces of the system, whose inverse limit vanishes, so no
section projection of the presentation of `X` is surjective and `X` is not McQuillan.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_representable_hasSomeSurjectivePresentation_not`: there
  is a representable morphism of affine formal algebraic spaces with McQuillan target and
  non-McQuillan source.

## Implementation notes

The source sketches a construction of the system `Φ = (Λ, Jᵢ, (Mᵢ) → (Vᵢ))` by iterating a step
which adjoins square-zero variables;
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemCokernel` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemEnlargement` show that this iteration
cannot be run. The system used here has the shape the source asks for — ideals `Jᵢ`
decreasing along the index and nil modulo one another, modules `Mᵢ` with `Mⱼ = Mᵢ/JⱼMᵢ` and
compatible surjections `Mᵢ → Vᵢ` — but its ideals are idempotent rather than square-zero, which
is what lets the kernels of the transition maps be divided inside themselves.

"Representable" is read as representable by schemes, the convention of the source; the
morphism is moreover affine over every test object.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

open Stacks.FractionalSystem

/-! ### The inverse system of sparse embeddings as a system with surjective maps -/

/-- The countable subsets of `α` are directed under inclusion. -/
instance (α : Type u) : IsDirected (CountableSubset α) (· ≤ ·) :=
  ⟨fun s t => ⟨⟨s.val ∪ t.val, s.property.union t.property⟩, Set.subset_union_left,
    Set.subset_union_right⟩⟩

/-- The injections with infinite complement, as an inverse system with surjective maps. -/
def sparseSystem (α : Type u) : SurjSystem (CountableSubset α) where
  obj s := SparseEmbedding s
  map h := sparseRestrict h
  map_refl _ _ := rfl
  map_map _ _ _ := rfl
  surjective_map h := sparseRestrict_surjective h

/-! ### Diagrams of affine stages from inverse systems of algebras -/

section StageDiagram

variable (B : BigFppfSite.{u}) (K : Type u) [CommRing K]
  (hS : B.Contains (Spec (CommRingCat.of K)))
  {J : Type u} [Preorder J] (F : Jᵒᵖ ⥤ CommRingCat.{u})
  (str : (Functor.const Jᵒᵖ).obj (CommRingCat.of K) ⟶ F)
  (hcont : ∀ j, B.Contains (Spec (F.obj (op j))))

/-- The structure morphism `Spec(F j) ⟶ Spec(K)` of a stage. -/
def stageStructureMap (j : J) : Spec (F.obj (op j)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (str.app (op j))

/-- For `j ≤ k`, the transition morphism `Spec(F j) ⟶ Spec(F k)` commutes with the structure
morphisms to `Spec(K)`. -/
theorem stageStructureMap_naturality {j k : J} (h : j ≤ k) :
    Spec.map (F.map (homOfLE h).op) ≫ stageStructureMap K F str k =
      stageStructureMap K F str j := by
  simp only [stageStructureMap, ← Spec.map_comp, ← str.naturality (homOfLE h).op]
  simp

/-- The stage over `j` of the diagram of spectra of an inverse system of `K`-algebras. -/
def stageObject (j : J) : BigAffineFppf B (Spec (CommRingCat.of K)) hS :=
  ⟨Over.mk (show B.obj (hcont j) ⟶ B.obj hS from
    ObjectProperty.homMk (stageStructureMap K F str j)),
    inferInstanceAs (IsAffine (Spec (F.obj (op j))))⟩

/-- The directed diagram of spectra of an inverse system of `K`-algebras, indexed by the universe
lift of the index preorder. -/
def stageDiagram : ULift.{u + 1} J ⥤ BigAffineFppf B (Spec (CommRingCat.of K)) hS where
  obj j := stageObject B K hS F str hcont j.down
  map {j k} f := by
    have h : j ≤ k := leOfHom f
    exact ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk (Spec.map (F.map (homOfLE (show j.down ≤ k.down from h)).op))) (by
      apply ObjectProperty.hom_ext
      exact stageStructureMap_naturality K F str (show j.down ≤ k.down from h)))
  map_id j := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (F.map (𝟙 _)) = 𝟙 _
    rw [F.map_id, Spec.map_id]
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (F.map _) = Spec.map (F.map _) ≫ Spec.map (F.map _)
    rw [← Spec.map_comp, ← F.map_comp]
    rfl

/-- The underlying morphism of schemes of a transition morphism of `stageDiagram` is `Spec` of the
corresponding transition map of `F`. -/
theorem toScheme_stageDiagram_map {j k : ULift.{u + 1} J} (h : j ≤ k) :
    (BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((stageDiagram B K hS F str hcont).map (homOfLE h)) =
      Spec.map (F.map (homOfLE (show j.down ≤ k.down from h)).op) :=
  rfl

variable {F str hcont}
variable {F' : Jᵒᵖ ⥤ CommRingCat.{u}} {str' : (Functor.const Jᵒᵖ).obj (CommRingCat.of K) ⟶ F'}
  {hcont' : ∀ j, B.Contains (Spec (F'.obj (op j)))} (ψ : F ⟶ F') (hψ : str ≫ ψ = str')

include hψ

/-- The morphism `Spec(F' j) ⟶ Spec(F j)` induced by `ψ` commutes with the structure morphisms to
`Spec(K)`. -/
theorem stageStructureMap_comp (j : J) :
    Spec.map (ψ.app (op j)) ≫ stageStructureMap K F str j = stageStructureMap K F' str' j := by
  simp only [stageStructureMap, ← Spec.map_comp, ← hψ]
  rfl

/-- The morphism of diagrams of spectra induced by a morphism of inverse systems of algebras. -/
def stageDiagramMap : stageDiagram B K hS F' str' hcont' ⟶ stageDiagram B K hS F str hcont where
  app j := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (Spec.map (ψ.app (op j.down))))
    (by
      apply ObjectProperty.hom_ext
      exact stageStructureMap_comp K ψ hψ j.down))
  naturality {j k} f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (F'.map _) ≫ Spec.map (ψ.app _) = Spec.map (ψ.app _) ≫ Spec.map (F.map _)
    rw [← Spec.map_comp, ← Spec.map_comp, ψ.naturality]

/-- The underlying morphism of schemes of a component of `stageDiagramMap` is `Spec` of the
corresponding component of `ψ`. -/
theorem toScheme_stageDiagramMap_app (j : ULift.{u + 1} J) :
    (BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((stageDiagramMap B K hS ψ hψ (hcont := hcont) (hcont' := hcont')).app j) =
      Spec.map (ψ.app (op j.down)) :=
  rfl

end StageDiagram

/-! ### The rings of the example -/

section Example

variable (α : Type u) (K : Type u) [Field K]

/-- The structure maps `K → Aᵢ`. -/
def strA : (Functor.const (CountableSubset α)ᵒᵖ).obj (CommRingCat.of K) ⟶
    Afun (I := CountableSubset α) K where
  app s := CommRingCat.ofHom (algebraMap K (A K s.unop))
  naturality s t f := by
    refine CommRingCat.hom_ext (RingHom.ext fun k => ?_)
    change algebraMap K (A K t.unop) k = Amap K (leOfHom f.unop) (algebraMap K (A K s.unop) k)
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Amap_mk]

/-- The structure maps `K → Rᵢ`. -/
def strR : (Functor.const (CountableSubset α)ᵒᵖ).obj (CommRingCat.of K) ⟶
    Rfun (sparseSystem α) K :=
  strA α K ≫ inlNat (sparseSystem α) K

/-! ### Cardinality bounds -/

/-- The cardinal bounding the ground field and the uncountable set. -/
def bound0 : Cardinal.{u} := max Cardinal.aleph0 (max (Cardinal.mk K) (Cardinal.mk α))

/-- The bound for the index set and the stage sets. -/
def bound1 : Cardinal.{u} := 2 ^ bound0 α K

/-- The bound for the exponents and the vector spaces. -/
def bound2 : Cardinal.{u} := 2 ^ bound1 α K

/-- The bound for the rings of the example. -/
def bound3 : Cardinal.{u} := 2 ^ bound2 α K

omit [Field K] in
/-- `ℵ₀ ≤ bound0 α K`. -/
theorem aleph0_le_bound0 : Cardinal.aleph0 ≤ bound0 α K := le_max_left _ _

omit [Field K] in
/-- `bound0 α K ≤ bound1 α K`. -/
theorem bound0_le_bound1 : bound0 α K ≤ bound1 α K := (Cardinal.cantor _).le

omit [Field K] in
/-- `bound1 α K ≤ bound2 α K`. -/
theorem bound1_le_bound2 : bound1 α K ≤ bound2 α K := (Cardinal.cantor _).le

omit [Field K] in
/-- `bound2 α K ≤ bound3 α K`. -/
theorem bound2_le_bound3 : bound2 α K ≤ bound3 α K := (Cardinal.cantor _).le

omit [Field K] in
/-- `ℵ₀ ≤ bound1 α K`. -/
theorem aleph0_le_bound1 : Cardinal.aleph0 ≤ bound1 α K :=
  (aleph0_le_bound0 α K).trans (bound0_le_bound1 α K)

omit [Field K] in
/-- `ℵ₀ ≤ bound2 α K`. -/
theorem aleph0_le_bound2 : Cardinal.aleph0 ≤ bound2 α K :=
  (aleph0_le_bound1 α K).trans (bound1_le_bound2 α K)

omit [Field K] in
/-- `ℵ₀ ≤ bound3 α K`. -/
theorem aleph0_le_bound3 : Cardinal.aleph0 ≤ bound3 α K :=
  (aleph0_le_bound2 α K).trans (bound2_le_bound3 α K)

omit [Field K] in
/-- The cardinality of `K` is at most `bound0 α K`. -/
theorem mk_K_le : Cardinal.mk K ≤ bound0 α K := (le_max_left _ _).trans (le_max_right _ _)

omit [Field K] in
/-- The cardinality of `α` is at most `bound0 α K`. -/
theorem mk_α_le : Cardinal.mk α ≤ bound0 α K := (le_max_right _ _).trans (le_max_right _ _)

/-- The cardinality of `X →₀ Y` is at most `#Y ^ #X`. -/
theorem mk_finsupp_le_power {X Y : Type u} [Zero Y] :
    Cardinal.mk (X →₀ Y) ≤ Cardinal.mk Y ^ Cardinal.mk X := by
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id] using
    Cardinal.mk_le_of_injective (f := fun v : X →₀ Y => (v : X → Y)) DFunLike.coe_injective

omit [Field K] in
/-- The set of countable subsets of `α` has cardinality at most `bound1 α K`. -/
theorem mk_countableSubset_le : Cardinal.mk (CountableSubset α) ≤ bound1 α K :=
  (Cardinal.mk_subtype_le _).trans
    (Cardinal.mk_set.trans_le (Cardinal.power_le_power_left two_ne_zero (mk_α_le α K)))

omit [Field K] in
/-- For a countable `Q`, the finitely supported functions from the countable subsets of `α` to `Q`
form a set of cardinality at most `bound2 α K`. -/
theorem mk_countable_finsupp_le {Q : Type} [Zero Q] [Countable Q] :
    Cardinal.mk (CountableSubset α →₀ Q) ≤ bound2 α K := by
  have h := Cardinal.mk_le_of_injective (f := fun v : CountableSubset α →₀ Q =>
    (v : CountableSubset α → Q)) DFunLike.coe_injective
  rw [Cardinal.mk_arrow, Cardinal.lift_uzero] at h
  exact h.trans (Cardinal.power_le_two_power (aleph0_le_bound1 α K)
    ((Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans (aleph0_le_bound1 α K))
    (mk_countableSubset_le α K))

/-- The ring `P` has cardinality at most `bound3 α K`. -/
theorem mk_P_le : Cardinal.mk (P K (CountableSubset α)) ≤ bound3 α K :=
  (Cardinal.mk_le_of_injective (AddMonoidAlgebra.coeff_injective (R := K)
    (M := G (CountableSubset α)))).trans (mk_finsupp_le_power.trans
    (Cardinal.power_le_two_power (aleph0_le_bound2 α K)
      ((mk_K_le α K).trans ((bound0_le_bound1 α K).trans (bound1_le_bound2 α K)))
      (mk_countable_finsupp_le α K)))

/-- Each ring `Aₛ` has cardinality at most `bound3 α K`. -/
theorem mk_A_le (s : CountableSubset α) : Cardinal.mk (A K s) ≤ bound3 α K :=
  (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_P_le α K)

omit [Field K] in
/-- The injections `s ↪ ℕ` with infinite complement form a set of cardinality at most `bound1 α K`.
-/
theorem mk_sparseEmbedding_le (s : CountableSubset α) :
    Cardinal.mk (SparseEmbedding s) ≤ bound1 α K := by
  have h := Cardinal.mk_le_of_injective
    (f := fun e : SparseEmbedding s => (e.val : s.val → ℕ))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero] at h
  exact h.trans (Cardinal.power_le_two_power (aleph0_le_bound0 α K) (aleph0_le_bound0 α K)
    ((Cardinal.mk_subtype_le _).trans (mk_α_le α K)))

/-- Each vector space `Vₛ` has cardinality at most `bound2 α K`. -/
theorem mk_V_le (s : CountableSubset α) :
    Cardinal.mk (V (sparseSystem α) K s) ≤ bound2 α K :=
  mk_finsupp_le_power.trans (Cardinal.power_le_two_power (aleph0_le_bound1 α K)
    ((mk_K_le α K).trans (bound0_le_bound1 α K)) (mk_sparseEmbedding_le α K s))

/-- Each module `Mₛ` has cardinality at most `bound3 α K`. -/
theorem mk_M_le (s : CountableSubset α) :
    Cardinal.mk (M (sparseSystem α) K s) ≤ bound3 α K :=
  (Cardinal.mk_subtype_le _).trans (mk_finsupp_le_power.trans
    (Cardinal.power_le_two_power (aleph0_le_bound2 α K) (mk_V_le α K s)
      (mk_countable_finsupp_le α K)))

/-- Each ring `Rₛ = Aₛ ⊕ Mₛ` has cardinality at most `bound3 α K`. -/
theorem mk_R_le (s : CountableSubset α) :
    Cardinal.mk (R (sparseSystem α) K s) ≤ bound3 α K := by
  change Cardinal.mk (A K s × M (sparseSystem α) K s) ≤ _
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (mul_le_mul' (mk_A_le α K s) (mk_M_le α K s)).trans_eq
    (Cardinal.mul_eq_self (aleph0_le_bound3 α K))

omit [Field K] in
/-- If `bound0 α K < κ` for a strong limit cardinal `κ`, then `bound3 α K < κ`. -/
theorem bound3_lt {κ : Cardinal.{u}} (hlim : κ.IsStrongPrelimit)
    (hb : bound0 α K < κ) : bound3 α K < κ :=
  hlim (hlim (hlim hb))

end Example

/-! ### The example -/

section Assembly

/-- The universe lift of the countable subsets of `α` is nonempty. -/
instance (α : Type u) : Nonempty (ULift.{u + 1} (CountableSubset α)) :=
  ⟨ULift.up ⟨∅, Set.countable_empty⟩⟩

/-- The universe lift of the countable subsets of `α` is directed under inclusion. -/
instance (α : Type u) : IsDirected (ULift.{u + 1} (CountableSubset α)) (· ≤ ·) :=
  ⟨fun i j => ⟨ULift.up ⟨i.down.val ∪ j.down.val, i.down.property.union j.down.property⟩,
    Set.subset_union_left, Set.subset_union_right⟩⟩

variable (α : Type u) (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hb : bound0 α K < B.cutoff)

/-- The spectrum of a ring of cardinality at most `bound3 α K` has size at most `bound3 α K`. -/
private theorem size_spec_le (α K : Type u) {R : Type u} [CommRing R]
    (hR : Cardinal.mk R ≤ bound3 α K) :
    (Spec (CommRingCat.of R)).size ≤ bound3 α K := by
  rw [Scheme.size_Spec]
  exact max_le (aleph0_le_bound3 α K) hR

include hb in
/-- Each spectrum `Spec(Aₛ)` lies in the big site `B`. -/
theorem contains_A (s : CountableSubset α) :
    B.Contains (Spec ((Afun (I := CountableSubset α) K).obj (op s))) := by
  exact (size_spec_le α K (mk_A_le α K s)).trans_lt
    (bound3_lt α K B.cutoff_isStrongPrelimit hb)

include hb in
/-- Each spectrum `Spec(Rₛ)` lies in the big site `B`. -/
theorem contains_R (s : CountableSubset α) :
    B.Contains (Spec ((Rfun (sparseSystem α) K).obj (op s))) := by
  exact (size_spec_le α K (mk_R_le α K s)).trans_lt
    (bound3_lt α K B.cutoff_isStrongPrelimit hb)

variable (hS : B.Contains (Spec (CommRingCat.of K)))

/-- The presentation of the target: the spectra of the rings `Aᵢ`. -/
abbrev diagramY : ULift.{u + 1} (CountableSubset α) ⥤
    BigAffineFppf B (Spec (CommRingCat.of K)) hS :=
  stageDiagram B K hS (Afun K) (strA α K) (contains_A α K B hb)

/-- The presentation of the source: the spectra of the rings `Rᵢ`. -/
abbrev diagramX : ULift.{u + 1} (CountableSubset α) ⥤
    BigAffineFppf B (Spec (CommRingCat.of K)) hS :=
  stageDiagram B K hS (Rfun (sparseSystem α) K) (strR α K) (contains_R α K B hb)

/-- The morphism of presentations induced by the structure maps `Aᵢ → Rᵢ`. -/
abbrev diagramMap : diagramX α K B hb hS ⟶ diagramY α K B hb hS :=
  stageDiagramMap B K hS (inlNat (sparseSystem α) K) rfl

/-- The transition morphisms of `diagramY` are thickenings. -/
theorem diagramY_isThickening ⦃i j : ULift.{u + 1} (CountableSubset α)⦄ (g : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramY α K B hb hS).map g)) := by
  have h : i.down ≤ j.down := (leOfHom g : i ≤ j)
  change Stacks.Thickenings.IsThickening (Scheme.Spec.map (CommRingCat.ofHom (Amap K h)).op)
  exact CartesianColimit.specMap_isThickening_of_nilKernel _ (surjective_Amap K h)
    (fun x hx => isNilpotent_of_mem_ker_Amap K h hx)

/-- The transition morphisms of `diagramX` are thickenings. -/
theorem diagramX_isThickening ⦃i j : ULift.{u + 1} (CountableSubset α)⦄ (g : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramX α K B hb hS).map g)) := by
  have h : i.down ≤ j.down := (leOfHom g : i ≤ j)
  change Stacks.Thickenings.IsThickening
    (Scheme.Spec.map (CommRingCat.ofHom (Rmap (sparseSystem α) K h)).op)
  exact CartesianColimit.specMap_isThickening_of_nilKernel _ (surjective_Rmap _ K h)
    (fun x hx => isNilpotent_of_mem_ker_Rmap _ K h hx)

/-- **The stage squares are pushouts**: `Rⱼ = Rᵢ ⊗_{Aᵢ} Aⱼ` for `j ≤ i`. -/
theorem isPushout_stage {i j : (CountableSubset α)ᵒᵖ} (f : i ⟶ j) :
    IsPushout ((Afun K).map f) ((inlNat (sparseSystem α) K).app i)
      ((inlNat (sparseSystem α) K).app j) ((Rfun (sparseSystem α) K).map f) :=
  CartesianColimit.isPushout_of_surjective_of_ker_eq _ _ _ _
    ((inlNat (sparseSystem α) K).naturality f)
    (surjective_Amap K (leOfHom f.unop)) (surjective_Rmap _ K (leOfHom f.unop))
    (ker_Rmap _ K (leOfHom f.unop))

/-- The stage squares of `diagramMap` are pullbacks of schemes:
`Spec(Rⱼ) = Spec(Rᵢ) ×_{Spec(Aᵢ)} Spec(Aⱼ)`. -/
theorem diagram_isPullback ⦃i j : ULift.{u + 1} (CountableSubset α)⦄ (g : i ⟶ j) :
    IsPullback
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramMap α K B hb hS).app i))
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramX α K B hb hS).map g))
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramY α K B hb hS).map g))
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((diagramMap α K B hb hS).app j)) :=
  ((isPushout_stage α K (homOfLE (show i.down ≤ j.down from (leOfHom g : i ≤ j))).op).op.map
    Scheme.Spec).flip

/-- The target `Y = colim Spec(Aᵢ)`. -/
abbrev targetY : FppfSheaf B (Spec (CommRingCat.of K)) hS :=
  colimit (diagramY α K B hb hS ⋙ BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS))

/-- The source `X = colim Spec(Rᵢ)`. -/
abbrev sourceX : FppfSheaf B (Spec (CommRingCat.of K)) hS :=
  colimit (diagramX α K B hb hS ⋙ BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS))

include hb in
/-- If the rings of an inverse system of `K`-algebras indexed by the countable subsets of `α`
have cardinality at most `bound3 α K`, the coproduct of the stages of `stageDiagram` lies in the
big site `B`. -/
theorem coproduct_contains {F : (CountableSubset α)ᵒᵖ ⥤ CommRingCat.{u}}
    (str : (Functor.const (CountableSubset α)ᵒᵖ).obj (CommRingCat.of K) ⟶ F)
    (hcont : ∀ s, B.Contains (Spec (F.obj (op s))))
    (hF : ∀ s, Cardinal.mk (F.obj (op s)) ≤ bound3 α K) :
    B.Contains (∐ fun i : ULift.{u + 1} (CountableSubset α) =>
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hS).obj
        ((BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS).obj
          ((stageDiagram B K hS F str hcont).obj i))) := by
  let Y' : CountableSubset α → Scheme.{u} := fun s => Spec (F.obj (op s))
  let e : (∐ fun i : ULift.{u + 1} (CountableSubset α) =>
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hS).obj
        ((BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS).obj
          ((stageDiagram B K hS F str hcont).obj i))) ≅ ∐ Y' :=
    Sigma.reindex (Equiv.ulift : ULift.{u + 1} (CountableSubset α) ≃ CountableSubset α) Y'
  rw [BigFppfSite.Contains]
  refine (Scheme.size_congr e).trans_lt ((schemeSize_coproduct_le Y' (bound3 α K)
    (aleph0_le_bound3 α K) ((mk_countableSubset_le α K).trans
      ((bound1_le_bound2 α K).trans (bound2_le_bound3 α K))) fun s => ?_).trans_lt
    (bound3_lt α K B.cutoff_isStrongPrelimit hb))
  exact size_spec_le α K (hF s)

include hb in
/-- If the rings of an inverse system of `K`-algebras indexed by the countable subsets of `α`
have cardinality at most `bound3 α K` and the transition morphisms of `stageDiagram` are
thickenings, the colimit of the stages is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_of_stageDiagram {F : (CountableSubset α)ᵒᵖ ⥤ CommRingCat.{u}}
    (str : (Functor.const (CountableSubset α)ᵒᵖ).obj (CommRingCat.of K) ⟶ F)
    (hcont : ∀ s, B.Contains (Spec (F.obj (op s))))
    (hF : ∀ s, Cardinal.mk (F.obj (op s)) ≤ bound3 α K)
    (hD : ∀ ⦃i j : ULift.{u + 1} (CountableSubset α)⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((stageDiagram B K hS F str hcont).map g))) :
    IsAffineFormalAlgebraicSpace B (Spec (CommRingCat.of K)) hS
      (colimit (stageDiagram B K hS F str hcont ⋙
        BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS))) := by
  refine ⟨?_, ULift.{u + 1} (CountableSubset α), inferInstance, inferInstance, inferInstance,
    stageDiagram B K hS F str hcont, hD, ⟨Iso.refl _⟩⟩
  exact satisfiesSetTheoreticCondition_of_colimit B (Spec (CommRingCat.of K)) hS _ hD _
    ⟨Iso.refl _⟩ (exists_represented_coproduct B (Spec (CommRingCat.of K)) hS _
      (coproduct_contains α K B hb hS str hcont hF))

/-- The target `targetY` is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_targetY :
    IsAffineFormalAlgebraicSpace B (Spec (CommRingCat.of K)) hS (targetY α K B hb hS) :=
  isAffineFormalAlgebraicSpace_of_stageDiagram α K B hb hS (strA α K) (contains_A α K B hb)
    (mk_A_le α K) (diagramY_isThickening α K B hb hS)

/-- The source `sourceX` is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_sourceX :
    IsAffineFormalAlgebraicSpace B (Spec (CommRingCat.of K)) hS (sourceX α K B hb hS) :=
  isAffineFormalAlgebraicSpace_of_stageDiagram α K B hb hS (strR α K) (contains_R α K B hb)
    (mk_R_le α K) (diagramX_isThickening α K B hb hS)

end Assembly

/-! ### The target is McQuillan, the source is not -/

section Criteria

variable (α : Type u) (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hb : bound0 α K < B.cutoff) (hS : B.Contains (Spec (CommRingCat.of K)))

/-- The section projections of the presentation `diagramY` are surjective. -/
theorem hasSurjectiveSectionProjections_diagramY :
    HasSurjectiveSectionProjections B (Spec (CommRingCat.of K)) hS (diagramY α K B hb hS) := by
  refine hasSurjectiveSectionProjections_of_surjective_family B (Spec (CommRingCat.of K)) hS
    (Λ := P K (CountableSubset α))
    (fun j x => (Scheme.ΓSpecIso (CommRingCat.of (A K j.unop.down))).inv.hom
      (Ideal.Quotient.mk _ x)) ?_ ?_
  · intro j k g x
    have h : k.unop.down ≤ j.unop.down := (leOfHom g.unop : k.unop ≤ j.unop)
    have hn := congrArg (fun φ => φ.hom (Ideal.Quotient.mk (ideal K j.unop.down) x))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Amap K h)))
    change (Spec.map (CommRingCat.ofHom (Amap K h))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (A K j.unop.down))).inv.hom (Ideal.Quotient.mk _ x)) =
      (Scheme.ΓSpecIso (CommRingCat.of (A K k.unop.down))).inv.hom (Ideal.Quotient.mk _ x)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, Amap_mk] at hn
    exact hn.symm
  · intro j
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (A K j.unop.down))).inv).2.comp
      Ideal.Quotient.mk_surjective

/-- The target `targetY` is McQuillan. -/
theorem hasSomeSurjectivePresentation_targetY :
    HasSomeSurjectivePresentation B (Spec (CommRingCat.of K)) hS (targetY α K B hb hS) :=
  ⟨isAffineFormalAlgebraicSpace_targetY α K B hb hS, ULift.{u + 1} (CountableSubset α),
    inferInstance, inferInstance, inferInstance, diagramY α K B hb hS,
    diagramY_isThickening α K B hb hS, ⟨Iso.refl _⟩,
    hasSurjectiveSectionProjections_diagramY α K B hb hS⟩

/-- The inverse system of the vector spaces `Vᵢ`, reindexed by the universe lift. -/
abbrev vectorSystem : (ULift.{u + 1} (CountableSubset α))ᵒᵖ ⥤ Type u where
  obj j := V (sparseSystem α) K j.unop.down
  map {j k} g := ↾fun v => q (sparseSystem α) K (leOfHom g.unop : k.unop ≤ j.unop) v
  map_id j := by
    apply TypeCat.homEquiv.injective
    funext v
    exact q_refl _ K j.unop.down v
  map_comp f g := by
    apply TypeCat.homEquiv.injective
    funext v
    exact (q_q _ K _ _ v).symm

/-- The transition maps of `vectorSystem` are the maps `q` of the inverse system of vector spaces.
-/
theorem vectorSystem_map_apply {j k : (ULift.{u + 1} (CountableSubset α))ᵒᵖ} (g : j ⟶ k)
    (v : V (sparseSystem α) K j.unop.down) :
    (vectorSystem α K).map g v = q (sparseSystem α) K (leOfHom g.unop : k.unop ≤ j.unop) v :=
  rfl

/-- The compatible surjections from the section rings of the source onto the vector spaces. -/
def sectionsToVectors :
    sectionDiagram B (Spec (CommRingCat.of K)) hS (diagramX α K B hb hS) ⋙ forget CommRingCat.{u}
      ⟶ vectorSystem α K where
  app j := ↾fun x => proj (sparseSystem α) K j.unop.down
    ((Scheme.ΓSpecIso (CommRingCat.of (R (sparseSystem α) K j.unop.down))).hom.hom x)
  naturality {j k} g := by
    apply TypeCat.homEquiv.injective
    funext x
    have h : k.unop.down ≤ j.unop.down := (leOfHom g.unop : k.unop ≤ j.unop)
    have hn := congrArg (fun φ => φ.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Rmap (sparseSystem α) K h)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, CommRingCat.hom_ofHom] at hn
    exact (congrArg (proj (sparseSystem α) K k.unop.down) hn).trans (proj_Rmap _ K h _)

/-- Each component of `sectionsToVectors` is surjective. -/
theorem surjective_sectionsToVectors (j : (ULift.{u + 1} (CountableSubset α))ᵒᵖ) :
    Function.Surjective ((sectionsToVectors α K B hb hS).app j) := by
  change Function.Surjective (fun x => proj (sparseSystem α) K j.unop.down
    ((Scheme.ΓSpecIso (CommRingCat.of (R (sparseSystem α) K j.unop.down))).hom.hom x))
  exact (surjective_proj _ K j.unop.down).comp (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (R (sparseSystem α) K j.unop.down))).hom).2

/-- For uncountable `α`, the inverse limit of `vectorSystem` is trivial. -/
theorem subsingleton_sections_vectorSystem [Uncountable α] :
    Subsingleton (vectorSystem α K).sections := by
  have hzero : ∀ x : (vectorSystem α K).sections, ∀ j,
      (x.1 j : V (sparseSystem α) K j.unop.down) = 0 := fun x j =>
    finsupp_sparseEmbedding_eq_zero (α := α) (M := K)
      (fun s => (x.1 (op (ULift.up s)) : V (sparseSystem α) K s)) (fun s t h => by
        have := x.2 (homOfLE (show (ULift.up s : ULift.{u + 1} (CountableSubset α)) ≤
          ULift.up t from h)).op
        rwa [vectorSystem_map_apply] at this) j.unop.down
  exact ⟨fun x y => Subtype.ext (funext fun j => (hzero x j).trans (hzero y j).symm)⟩

/-- Each vector space of `vectorSystem` is nontrivial. -/
theorem not_subsingleton_vectorSystem (j : (ULift.{u + 1} (CountableSubset α))ᵒᵖ) :
    ¬ Subsingleton ((vectorSystem α K).obj j) := by
  intro h
  obtain ⟨e⟩ := sparseEmbedding_nonempty j.unop.down
  exact one_ne_zero (Finsupp.single_eq_zero.mp
    (h.elim (Finsupp.single e (1 : K) : V (sparseSystem α) K j.unop.down) 0))

/-- For uncountable `α`, the source `sourceX` is not McQuillan. -/
theorem not_hasSomeSurjectivePresentation_sourceX [Uncountable α] :
    ¬ HasSomeSurjectivePresentation B (Spec (CommRingCat.of K)) hS (sourceX α K B hb hS) := by
  let i₀ : ULift.{u + 1} (CountableSubset α) := ULift.up ⟨∅, Set.countable_empty⟩
  exact not_hasSomeSurjectivePresentation_of_presentation B (Spec (CommRingCat.of K)) hS _
    (ULift.{u + 1} (CountableSubset α)) (diagramX α K B hb hS)
    (diagramX_isThickening α K B hb hS) (Iso.refl _)
    (not_hasSurjectiveSectionProjections_of_natTrans B (Spec (CommRingCat.of K)) hS
      (sectionsToVectors α K B hb hS) (surjective_sectionsToVectors α K B hb hS) (i₀ := i₀)
      (Functor.not_surjective_sections_eval_of_subsingleton_sections
        (subsingleton_sections_vectorSystem α K) (not_subsingleton_vectorSystem α K (op i₀))))

/-- The morphism `X ⟶ Y` induced by the structure maps `Aᵢ → Rᵢ`. -/
abbrev morphism : sourceX α K B hb hS ⟶ targetY α K B hb hS :=
  colim.map (CartesianColimit.sheafMap B (Spec (CommRingCat.of K)) hS _ _ (diagramMap α K B hb hS))

/-- Every represented base change of `morphism` along a scheme is an affine morphism of schemes. -/
theorem relative_isAffineHom_morphism :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS))
      (morphism α K B hb hS) := by
  have h := CartesianColimit.relative_isAffineHom_colimMap
    (diagramY_isThickening α K B hb hS) (diagram_isPullback α K B hb hS)
    (targetY α K B hb hS) (isAffineFormalAlgebraicSpace_targetY α K B hb hS) (Iso.refl _)
    (bound3_lt α K B.cutoff_isStrongPrelimit hb) (fun i => size_spec_le α K (mk_R_le α K i.down))
  have he : colim.map (CartesianColimit.sheafMap B (Spec (CommRingCat.of K)) hS _ _
      (diagramMap α K B hb hS)) ≫ (Iso.refl (targetY α K B hb hS)).inv =
      morphism α K B hb hS := Category.comp_id _
  rwa [he] at h

end Criteria

/-- There exists a representable morphism `f : X ⟶ Y` of affine formal algebraic spaces with `Y`
McQuillan, but `X` not McQuillan. The morphism is representable by schemes, and every represented
base change of it is moreover an affine morphism of schemes. -/
@[stacks 0CBE]
theorem exists_representable_hasSomeSurjectivePresentation_not :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (inS : B.Contains S) (X Y : FppfSheaf B S inS)
      (f : X ⟶ Y),
      IsAffineFormalAlgebraicSpace B S inS X ∧ IsAffineFormalAlgebraicSpace B S inS Y ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S inS)).relativelyRepresentable f ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S inS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S inS)) f ∧
      HasSomeSurjectivePresentation B S inS Y ∧ ¬ HasSomeSurjectivePresentation B S inS X := by
  classical
  obtain ⟨B, _⟩ := AlgebraicGeometry.exists_common_bigFppfSite.{u, 0}
    (fun e : PEmpty.{1} => (e.elim : BigFppfSite.{u}))
  let K := ULift.{u} ℚ
  let α := ULift.{u} (Set ℕ)
  have hcard : Cardinal.mk α = 2 ^ Cardinal.aleph0.{u} := by
    simp [α, Cardinal.mk_uLift, Cardinal.mk_set]
  have hαunc : Uncountable α := by
    rw [← Cardinal.aleph0_lt_mk_iff, hcard]
    exact Cardinal.cantor _
  have hK : Cardinal.mk K < B.cutoff :=
    (Cardinal.mk_le_aleph0 (α := K)).trans_lt B.aleph0_lt_cutoff
  have hα : Cardinal.mk α < B.cutoff := by
    rw [hcard]
    exact B.cutoff_isStrongPrelimit B.aleph0_lt_cutoff
  have hS : B.Contains (Spec (CommRingCat.of K)) := by
    rw [BigFppfSite.Contains, Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff hK
  have hb : bound0 α K < B.cutoff := max_lt B.aleph0_lt_cutoff (max_lt hK hα)
  have hrel := relative_isAffineHom_morphism α K B hb hS
  exact ⟨B, Spec (CommRingCat.of K), hS, sourceX α K B hb hS, targetY α K B hb hS,
    morphism α K B hb hS, isAffineFormalAlgebraicSpace_sourceX α K B hb hS,
    isAffineFormalAlgebraicSpace_targetY α K B hb hS, hrel.rep, hrel,
    hasSomeSurjectivePresentation_targetY α K B hb hS,
    not_hasSomeSurjectivePresentation_sourceX α K B hb hS⟩

end AlgebraicGeometry.FormalSpace

end
