module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.Unramified
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The graph relation of an abstract group acting on a scheme

An abstract group `G` acting on a scheme `U` over `S` by automorphisms of `S`-schemes has a
*graph relation*: its scheme of arrows is the disjoint union of one copy of `U` for each
element of `G`, the source map is the identity on each copy and the target map is the action
of the indexing element. The source and target maps are étale because each copy of `U` maps
isomorphically, and the relation is an equivalence relation on points over every
algebraically closed field as soon as no nonidentity element fixes a point together with its
residue field. Its sheaf quotient on a big fppf site is the quotient of `U` by `G`.

## Main definitions

* `AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields` is the condition that a
  nonidentity group element fixing a point act nontrivially on its residue field.
* `AlgebraicGeometry.Space.actionRelationScheme`, together with
  `AlgebraicGeometry.Space.actionRelationSource` and
  `AlgebraicGeometry.Space.actionRelationTarget`, is the graph relation of the action, and
  `AlgebraicGeometry.Space.actionRelation` packages it as a pre-relation.
* `AlgebraicGeometry.Space.actionQuotient` is its quotient sheaf on a big fppf site, and
  `AlgebraicGeometry.Space.siteActionRelationScheme` realises the relation inside that site.

## Main results

* `AlgebraicGeometry.Space.actionRelation_isEtaleEquivalenceRelation`: the graph relation of
  an action with residue-field-faithful stabilizers is an étale equivalence relation.
* `AlgebraicGeometry.Space.contains_actionRelationScheme`: the scheme of arrows of such a
  relation satisfies the size cutoff of a big fppf site containing `U`, so the relation lives
  in that site.

## Implementation notes

The action is a homomorphism into the automorphism group of `U` in the slice category over
`S`. The fixed-point condition compares the induced map on the residue field at a fixed point
with the canonical identification coming from the equality of the two points. An indexed
coproduct of schemes needs its index type to be small relative to the universe of schemes,
which is required of `G` throughout.

That the relation scheme again satisfies the size cutoff is a cardinality estimate: a group
element is determined by its effect on a single chosen field-valued point, and the set of
field-valued points of `U` is bounded by `2 ^ U.size`, which the cutoff dominates because it
is a strong prelimit. When `U` is empty the relation scheme is empty too, and the estimate is
replaced by the countable bound for empty schemes.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]

/-- The action of a group on a scheme over `S` *acts nontrivially on fixed residue fields*
when every nonidentity element fixing a point acts nontrivially on the residue field at that
point. -/
@[stacks 02Z3 "acts freely: the condition (*) of 02Z2 on the action"]
def ActsNontriviallyOnFixedResidueFields (a : G →* Aut U) : Prop :=
  ∀ (g : G) (x : U.left) (hx : (a g).asIso.hom.left x = x),
    g ≠ 1 → (a g).asIso.hom.left.residueFieldMap x ≠
      (U.left.residueFieldCongr hx).hom

/-- The scheme of arrows of the graph relation of a group action: the disjoint union of one
copy of `U` for each group element. -/
@[stacks 02Z2 "relation object"]
abbrev actionRelationScheme : Over S := ∐ fun _ : G ↦ U

/-- The target map of the graph relation of a group action, sending the point `x` of the
copy indexed by `g` to `g x`. -/
def actionRelationTarget (a : G →* Aut U) : actionRelationScheme U G ⟶ U :=
  Sigma.desc (fun g : G ↦ (a g).asIso.hom)

/-- The source map of the graph relation of a group action, the identity on every copy
of `U`. -/
def actionRelationSource : actionRelationScheme U G ⟶ U :=
  Sigma.desc (fun _ : G ↦ 𝟙 U)

/-- The graph relation of a group action, as a pre-relation on `U`. -/
@[stacks 02Z2 "relation"]
def actionRelation (a : G →* Aut U) :
    PreRelation (actionRelationScheme U G) U :=
  prod.lift (actionRelationTarget U G a) (actionRelationSource U G)

/-- The underlying scheme of the relation scheme of a group action is the disjoint union of
the underlying schemes of the copies of `U`. -/
def actionRelationUnderlyingIso :
    (actionRelationScheme U G).left ≅ ∐ fun _ : G ↦ U.left :=
  preservesColimitIso (Over.forget S) (Discrete.functor fun _ : G ↦ U)

omit [Group G] in
/-- The inverse of `actionRelationUnderlyingIso` sends the coprojection of the copy of
`U.left` indexed by `g` to the underlying morphism of the coprojection of the copy of `U`
indexed by `g`. -/
@[simp]
theorem actionRelationUnderlyingIso_inv_ι (g : G) :
    Sigma.ι (fun _ : G ↦ U.left) g ≫ (actionRelationUnderlyingIso U G).inv =
      (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) :=
  ι_preservesColimitIso_inv (Over.forget S) (Discrete.functor fun _ : G ↦ U) ⟨g⟩

private theorem actionRelation_source_eq (a : G →* Aut U) :
    (actionRelation U G a).source = actionRelationSource U G := by
  simp [actionRelation, PreRelation.source]

private theorem actionRelation_target_eq (a : G →* Aut U) :
    (actionRelation U G a).target = actionRelationTarget U G a := by
  simp [actionRelation, PreRelation.target]

omit [Group G] in
/-- A morphism out of the relation scheme is étale if its restriction to each copy of `U` is. -/
private theorem etale_of_forget_ι_comp (f : actionRelationScheme U G ⟶ U)
    (hf : ∀ g : G, Etale ((Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) ≫ f.left)) :
    Etale f.left := by
  let : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  let e := actionRelationUnderlyingIso U G
  have hsum : Etale (e.inv ≫ f.left) := by
    have h : e.inv ≫ f.left = Sigma.desc fun g : G ↦
        (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) ≫ f.left := by
      apply Sigma.hom_ext
      intro g
      rw [← Category.assoc, actionRelationUnderlyingIso_inv_ι, Sigma.ι_desc]
    rw [h]
    exact IsZariskiLocalAtSource.sigmaDesc hf
  have h : Etale ((e.hom ≫ e.inv) ≫ f.left) := Etale.etale_comp e.hom (e.inv ≫ f.left)
  simpa [Category.assoc] using h

private theorem actionRelationSource_etale (a : G →* Aut U) :
    Etale (actionRelation U G a).source.left :=
  (actionRelation_source_eq U G a).symm ▸ etale_of_forget_ι_comp U G _ fun g ↦ by
    change Etale ((Over.forget S).map _ ≫ (Over.forget S).map _)
    rw [← (Over.forget S).map_comp]
    simpa [actionRelationSource] using inferInstanceAs (Etale (𝟙 U.left))

private theorem actionRelationTarget_etale (a : G →* Aut U) :
    Etale (actionRelation U G a).target.left :=
  (actionRelation_target_eq U G a).symm ▸ etale_of_forget_ι_comp U G _ fun g ↦ by
    change Etale ((Over.forget S).map _ ≫ (Over.forget S).map _)
    rw [← (Over.forget S).map_comp]
    have : IsIso ((a g).asIso.hom.left) := ((Over.forget S).mapIso (a g).asIso).isIso_hom
    simpa [actionRelationTarget] using inferInstanceAs (Etale (a g).asIso.hom.left)

private def actionRelationIdentity : U ⟶ actionRelationScheme U G :=
  Sigma.ι (fun _ : G ↦ U) 1

private theorem actionRelationIdentity_source :
    actionRelationIdentity U G ≫ actionRelationSource U G = 𝟙 U := by
  simp [actionRelationIdentity, actionRelationSource]

private theorem actionRelationIdentity_target (a : G →* Aut U) :
    actionRelationIdentity U G ≫ actionRelationTarget U G a = 𝟙 U := by
  simp only [actionRelationIdentity, actionRelationTarget, Sigma.ι_desc]
  rw [map_one]
  rfl

private def actionRelationInverse (a : G →* Aut U) :
    actionRelationScheme U G ⟶ actionRelationScheme U G :=
  Sigma.desc fun g : G ↦ (a g).asIso.hom ≫ Sigma.ι (fun _ : G ↦ U) g⁻¹

private theorem actionRelationInverse_target (a : G →* Aut U) :
    actionRelationInverse U G a ≫ actionRelationTarget U G a =
      actionRelationSource U G := by
  apply Sigma.hom_ext
  intro g
  calc
    _ = ((a g).asIso.hom ≫ Sigma.ι (fun _ : G ↦ U) g⁻¹) ≫
        actionRelationTarget U G a := by
          rw [← Category.assoc, actionRelationInverse, Sigma.ι_desc]
    _ = (a g).asIso.hom ≫ ((a g⁻¹).asIso.hom) := by
          rw [Category.assoc, actionRelationTarget, Sigma.ι_desc]
    _ = 𝟙 U := by
          rw [a.map_inv g, Aut.inv_asIso]
          exact Iso.hom_inv_id _
    _ = Sigma.ι (fun _ : G ↦ U) g ≫ actionRelationSource U G := by
          simp [actionRelationSource]

private theorem actionRelationInverse_source (a : G →* Aut U) :
    actionRelationInverse U G a ≫ actionRelationSource U G =
      actionRelationTarget U G a := by
  apply Sigma.hom_ext
  intro g
  calc
    _ = ((a g).asIso.hom ≫ Sigma.ι (fun _ : G ↦ U) g⁻¹) ≫
        actionRelationSource U G := by
          rw [← Category.assoc, actionRelationInverse, Sigma.ι_desc]
    _ = (a g).asIso.hom := by
          simp [actionRelationSource]
    _ = Sigma.ι (fun _ : G ↦ U) g ≫ actionRelationTarget U G a := by
          rw [actionRelationTarget, Sigma.ι_desc]

private theorem actionRelationComposition_exists (a : G →* Aut U) :
    ∃ c : pullback (actionRelationSource U G) (actionRelationTarget U G a) ⟶
        actionRelationScheme U G,
      c ≫ actionRelationTarget U G a =
        pullback.fst (actionRelationSource U G) (actionRelationTarget U G a) ≫
          actionRelationTarget U G a ∧
      c ≫ actionRelationSource U G =
        pullback.snd (actionRelationSource U G) (actionRelationTarget U G a) ≫
          actionRelationSource U G := by
  let F : G → Over S := fun _ ↦ U
  let f : G → (U ⟶ U) := fun _ ↦ 𝟙 U
  let g : G → (U ⟶ U) := fun i ↦ (a i).asIso.hom
  have hf (i : G) : Sigma.ι F i ≫ actionRelationSource U G = f i := by
    simp [F, f, actionRelationSource]
  have hg (i : G) : Sigma.ι F i ≫ actionRelationTarget U G a = g i := by
    simp [F, g, actionRelationTarget]
  let P := pullback (actionRelationSource U G) (actionRelationTarget U G a)
  let m (p : G × G) : pullback (f p.1) (g p.2) ⟶ P :=
    pullback.map (f p.1) (g p.2) (actionRelationSource U G)
      (actionRelationTarget U G a) (Sigma.ι F p.1) (Sigma.ι F p.2) (𝟙 U)
      (by simpa [Category.id_comp] using (hf p.1).symm)
      (by simpa [Category.id_comp] using (hg p.2).symm)
  let d : Cofan (fun p : G × G ↦ pullback (f p.1) (g p.2)) :=
    Cofan.mk P m
  have hd : IsColimit d := Classical.choice <|
    (isUniversalColimit_sigmaCofanOver F).nonempty_isColimit_prod_of_pullbackCone
      (isUniversalColimit_sigmaCofanOver F) f g (actionRelationSource U G)
      (actionRelationTarget U G a)
      (fun i j ↦ pullback.cone (f i) (g j))
      (fun i j ↦ pullback.isLimit (f i) (g j))
      (pullback.cone (actionRelationSource U G) (actionRelationTarget U G a))
      (pullback.isLimit (actionRelationSource U G) (actionRelationTarget U G a))
      (d := d) (Iso.refl P) hf hg
      (by
        intro i j
        simpa [Cofan.inj, d, m, pullback.map] using
          (pullback.lift_fst (pullback.fst (f i) (g j) ≫ Sigma.ι F i)
            (pullback.snd (f i) (g j) ≫ Sigma.ι F j) _))
      (by
        intro i j
        simpa [Cofan.inj, d, m, pullback.map] using
          (pullback.lift_snd (pullback.fst (f i) (g j) ≫ Sigma.ι F i)
            (pullback.snd (f i) (g j) ≫ Sigma.ι F j) _))
  have hmFst (i j : G) :
      m (i, j) ≫ pullback.fst (actionRelationSource U G)
          (actionRelationTarget U G a) =
        pullback.fst (f i) (g j) ≫ Sigma.ι F i := by
    simpa [m, pullback.map] using
      (pullback.lift_fst (pullback.fst (f i) (g j) ≫ Sigma.ι F i)
        (pullback.snd (f i) (g j) ≫ Sigma.ι F j) _)
  have hmSnd (i j : G) :
      m (i, j) ≫ pullback.snd (actionRelationSource U G)
          (actionRelationTarget U G a) =
        pullback.snd (f i) (g j) ≫ Sigma.ι F j := by
    simpa [m, pullback.map] using
      (pullback.lift_snd (pullback.fst (f i) (g j) ≫ Sigma.ι F i)
        (pullback.snd (f i) (g j) ≫ Sigma.ι F j) _)
  let c : P ⟶ actionRelationScheme U G :=
    Cofan.IsColimit.desc hd fun p ↦
      pullback.snd (f p.1) (g p.2) ≫ Sigma.ι F (p.1 * p.2)
  refine ⟨c, ?_, ?_⟩
  · apply Cofan.IsColimit.hom_ext hd
    rintro ⟨i, j⟩
    show (d.inj (i, j) ≫ c) ≫ actionRelationTarget U G a =
      (d.inj (i, j) ≫ pullback.fst (actionRelationSource U G)
        (actionRelationTarget U G a)) ≫ actionRelationTarget U G a
    rw [Cofan.IsColimit.fac hd]
    show (pullback.snd (f i) (g j) ≫ Sigma.ι F (i * j)) ≫
        actionRelationTarget U G a =
      (m (i, j) ≫ pullback.fst (actionRelationSource U G)
          (actionRelationTarget U G a)) ≫ actionRelationTarget U G a
    have hmul : (a (i * j)).asIso.hom = (a j).asIso.hom ≫ (a i).asIso.hom := by
      rw [a.map_mul i j, Aut.mul_asIso]
      rfl
    calc
      (pullback.snd (f i) (g j) ≫ Sigma.ι F (i * j)) ≫
          actionRelationTarget U G a =
        pullback.snd (f i) (g j) ≫ (a (i * j)).asIso.hom := by
          rw [Category.assoc, actionRelationTarget, Sigma.ι_desc]
      _ = pullback.snd (f i) (g j) ≫ ((a j).asIso.hom ≫ (a i).asIso.hom) := by rw [hmul]
      _ = pullback.fst (f i) (g j) ≫ (a i).asIso.hom := by
          have hbase : pullback.fst (f i) (g j) =
              pullback.snd (f i) (g j) ≫ (a j).asIso.hom := by
            simpa [f, g] using
              (pullback.condition : pullback.fst (f i) (g j) ≫ f i =
                pullback.snd (f i) (g j) ≫ g j)
          rw [← Category.assoc, ← hbase]
      _ = (m (i, j) ≫ pullback.fst (actionRelationSource U G)
          (actionRelationTarget U G a)) ≫ actionRelationTarget U G a := by
          rw [hmFst, Category.assoc, actionRelationTarget, Sigma.ι_desc]
  · apply Cofan.IsColimit.hom_ext hd
    rintro ⟨i, j⟩
    show (d.inj (i, j) ≫ c) ≫ actionRelationSource U G =
      (d.inj (i, j) ≫ pullback.snd (actionRelationSource U G)
        (actionRelationTarget U G a)) ≫ actionRelationSource U G
    rw [Cofan.IsColimit.fac hd]
    show (pullback.snd (f i) (g j) ≫ Sigma.ι F (i * j)) ≫
        actionRelationSource U G =
      (m (i, j) ≫ pullback.snd (actionRelationSource U G)
          (actionRelationTarget U G a)) ≫ actionRelationSource U G
    rw [hmSnd]
    show pullback.snd (f i) (g j) ≫
        (Sigma.ι F (i * j) ≫ Sigma.desc (fun _ : G ↦ 𝟙 U)) =
      pullback.snd (f i) (g j) ≫
        (Sigma.ι F j ≫ Sigma.desc (fun _ : G ↦ 𝟙 U))
    rw [Sigma.ι_desc, Sigma.ι_desc]

omit [Group G] in
private theorem actionRelationFieldPoint_factors {k : Type u} [Field k]
    (z : Spec (.of k) ⟶ (actionRelationScheme U G).left) :
    ∃ g : G, ∃ z' : Spec (.of k) ⟶ U.left,
      z ≫ (actionRelationUnderlyingIso U G).hom =
        z' ≫ Sigma.ι (fun _ : G ↦ U.left) g := by
  let z'' := z ≫ (actionRelationUnderlyingIso U G).hom
  let q := z'' (default : Spec (.of k))
  obtain ⟨g, x, hx⟩ := (AlgebraicGeometry.sigmaOpenCover (fun _ : G ↦ U.left)).exists_eq q
  have hrange : Set.range z'' ⊆ Set.range (Sigma.ι (fun _ : G ↦ U.left) g) := by
    rintro y ⟨t, rfl⟩
    obtain rfl : t = (default : Spec (.of k)) := Subsingleton.elim _ _
    exact ⟨x, hx⟩
  let z' := IsOpenImmersion.lift (Sigma.ι (fun _ : G ↦ U.left) g) z'' hrange
  exact ⟨g, z', (IsOpenImmersion.lift_fac _ _ _).symm⟩

private def actionRelationUnderlyingInclusion (g : G) :
    U.left ⟶ (actionRelationScheme U G).left :=
  (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g)

omit [Group G] in
private theorem actionRelationUnderlyingInclusion_source (g : G) :
    actionRelationUnderlyingInclusion U G g ≫ (actionRelationSource U G).left =
      𝟙 U.left := by
  show (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) ≫
      (Over.forget S).map (actionRelationSource U G) = 𝟙 U.left
  rw [← (Over.forget S).map_comp]
  exact congrArg Over.Hom.left (Sigma.ι_desc (fun _ : G ↦ 𝟙 U) g)

private theorem actionRelationUnderlyingInclusion_target (a : G →* Aut U) (g : G) :
    actionRelationUnderlyingInclusion U G g ≫ (actionRelationTarget U G a).left =
      (a g).asIso.hom.left := by
  show (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) ≫
      (Over.forget S).map (actionRelationTarget U G a) = _
  rw [← (Over.forget S).map_comp]
  exact congrArg Over.Hom.left (Sigma.ι_desc (fun g : G ↦ (a g).asIso.hom) g)

omit [Small.{u} G] in
private theorem actionRelation_fixedPoint_forces_identity (a : G →* Aut U)
    (ha : ActsNontriviallyOnFixedResidueFields U G a)
    {k : Type u} [Field k] (z : Spec (.of k) ⟶ U.left) (g : G)
    (hfix : z ≫ (a g).asIso.hom.left = z) : g = 1 := by
  let E := Scheme.SpecToEquivOfField k U.left
  let x := z (IsLocalRing.closedPoint k)
  obtain ⟨hx, hres⟩ := Scheme.SpecToEquivOfField_eq_iff.mp (congrArg E hfix)
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_mk, Scheme.Hom.comp_base,
    TopCat.hom_comp, ContinuousMap.coe_comp,
    Scheme.descResidueField_stalkClosedPointTo_comp, E] at hx hres
  have hres' : (a g).asIso.hom.left.residueFieldMap x =
      (U.left.residueFieldCongr hx).hom := by
    let lam := (E z).2
    let : Mono lam := ConcreteCategory.mono_of_injective lam (RingHom.injective lam.hom)
    have hcomp : (a g).asIso.hom.left.residueFieldMap x ≫ lam =
        (U.left.residueFieldCongr hx).hom ≫ lam := hres
    exact (cancel_mono lam).mp hcomp
  by_contra hne
  exact ha g x hx hne hres'

omit [Small.{u} G] in
private theorem actionRelation_eq_of_comp_eq (a : G →* Aut U)
    (ha : ActsNontriviallyOnFixedResidueFields U G a)
    {k : Type u} [Field k] (z : Spec (.of k) ⟶ U.left) {g h : G}
    (hgh : z ≫ (a g).asIso.hom.left = z ≫ (a h).asIso.hom.left) : g = h := by
  have hmul : (a (h⁻¹ * g)).asIso.hom.left = (a g).asIso.hom.left ≫ (a h⁻¹).asIso.hom.left := by
    rw [a.map_mul, Aut.mul_asIso]
    rfl
  have hcancelOver : (a h).asIso.hom ≫ (a h⁻¹).asIso.hom = 𝟙 U := by
    rw [a.map_inv h, Aut.inv_asIso]
    exact Iso.hom_inv_id _
  have hcancel : (a h).asIso.hom.left ≫ (a h⁻¹).asIso.hom.left = 𝟙 U.left :=
    congrArg Over.Hom.left hcancelOver
  have hd := actionRelation_fixedPoint_forces_identity U G a ha z (h⁻¹ * g) (by
    rw [hmul, ← Category.assoc, hgh, Category.assoc, hcancel, Category.comp_id])
  exact (inv_mul_eq_one.mp hd).symm

private theorem actionRelationFieldPoint_injective (a : G →* Aut U)
    (ha : ActsNontriviallyOnFixedResidueFields U G a)
    {k : Type u} [Field k] [IsAlgClosed k]
    (p : Spec (.of k) ⟶ S)
    (r s : Over.mk p ⟶ actionRelationScheme U G)
    (h : r ≫ actionRelation U G a = s ≫ actionRelation U G a) : r = s := by
  have hfac (t : Over.mk p ⟶ actionRelationScheme U G) :
      ∃ g : G, ∃ z : Spec (.of k) ⟶ U.left,
        t.left = z ≫ actionRelationUnderlyingInclusion U G g := by
    obtain ⟨g, z, hfac⟩ := actionRelationFieldPoint_factors U G t.left
    refine ⟨g, z, ?_⟩
    calc
      t.left = t.left ≫ (actionRelationUnderlyingIso U G).hom ≫
          (actionRelationUnderlyingIso U G).inv := by simp
      _ = z ≫ Sigma.ι (fun _ : G ↦ U.left) g ≫
          (actionRelationUnderlyingIso U G).inv :=
            congrArg (fun f ↦ f ≫ (actionRelationUnderlyingIso U G).inv) hfac
      _ = z ≫ actionRelationUnderlyingInclusion U G g := by
          rw [actionRelationUnderlyingIso_inv_ι, actionRelationUnderlyingInclusion]
  obtain ⟨g, z, hr⟩ := hfac r
  obtain ⟨hidx, w, hs⟩ := hfac s
  have ht : r ≫ actionRelationTarget U G a = s ≫ actionRelationTarget U G a := by
    simpa [actionRelation, PreRelation.target] using congrArg (fun f ↦ f ≫ prod.fst) h
  have hsrel : r ≫ actionRelationSource U G = s ≫ actionRelationSource U G := by
    simpa [actionRelation, PreRelation.source] using congrArg (fun f ↦ f ≫ prod.snd) h
  have hz : z = w := by
    calc
      z = r.left ≫ (actionRelationSource U G).left := by
        rw [hr, Category.assoc, actionRelationUnderlyingInclusion_source]
        simp
      _ = s.left ≫ (actionRelationSource U G).left := congrArg Over.Hom.left hsrel
      _ = w := by
        rw [hs, Category.assoc, actionRelationUnderlyingInclusion_source]
        simp
  have hact : z ≫ (a g).asIso.hom.left = z ≫ (a hidx).asIso.hom.left := by
    calc
      z ≫ (a g).asIso.hom.left = r.left ≫ (actionRelationTarget U G a).left := by
        rw [hr, Category.assoc, actionRelationUnderlyingInclusion_target]
      _ = s.left ≫ (actionRelationTarget U G a).left := congrArg Over.Hom.left ht
      _ = w ≫ (a hidx).asIso.hom.left := by
        rw [hs, Category.assoc, actionRelationUnderlyingInclusion_target]
      _ = z ≫ (a hidx).asIso.hom.left := by rw [hz]
  have hidx_eq : hidx = g := (actionRelation_eq_of_comp_eq U G a ha z hact).symm
  apply Over.OverMorphism.ext
  rw [hr, hs, hz, hidx_eq]

private theorem actionRelation_rel_equivalence (a : G →* Aut U) (T : Over S) :
    Equivalence ((actionRelation U G a).Rel (T := T)) := by
  have hs := actionRelation_source_eq U G a
  have ht := actionRelation_target_eq U G a
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨x ≫ actionRelationIdentity U G, ?_, ?_⟩
    · rw [Category.assoc, ht, actionRelationIdentity_target U G a, Category.comp_id]
    · rw [Category.assoc, hs, actionRelationIdentity_source U G, Category.comp_id]
  · intro x y hxy
    rcases hxy with ⟨r, hrx, hry⟩
    refine ⟨r ≫ actionRelationInverse U G a, ?_, ?_⟩
    · rw [Category.assoc, ht, actionRelationInverse_target U G a, ← hs, hry]
    · rw [Category.assoc, hs, actionRelationInverse_source U G a, ← ht, hrx]
  · intro x y z hxy hyz
    rcases hxy with ⟨r, hrx, hry⟩
    rcases hyz with ⟨s, hsy, hsz⟩
    have hcond : r ≫ actionRelationSource U G = s ≫ actionRelationTarget U G a := by
      rw [← hs, ← ht]
      exact hry.trans hsy.symm
    obtain ⟨c, hct, hcs⟩ := actionRelationComposition_exists U G a
    refine ⟨pullback.lift r s hcond ≫ c, ?_, ?_⟩
    · rw [ht, Category.assoc, hct, pullback.lift_fst_assoc, ← ht, hrx]
    · rw [hs, Category.assoc, hcs, pullback.lift_snd_assoc, ← hs, hsz]

private theorem actionRelation_comp_exists (a : G →* Aut U) :
    ∃ c : pullback (actionRelation U G a).source (actionRelation U G a).target ⟶
        actionRelationScheme U G,
      c ≫ (actionRelation U G a).target =
        pullback.fst (actionRelation U G a).source (actionRelation U G a).target ≫
          (actionRelation U G a).target ∧
      c ≫ (actionRelation U G a).source =
        pullback.snd (actionRelation U G a).source (actionRelation U G a).target ≫
          (actionRelation U G a).source := by
  have key (s t : actionRelationScheme U G ⟶ U) [HasPullback s t]
      (hs : s = actionRelationSource U G) (ht : t = actionRelationTarget U G a) :
      ∃ c : pullback s t ⟶ actionRelationScheme U G,
        c ≫ t = pullback.fst s t ≫ t ∧ c ≫ s = pullback.snd s t ≫ s := by
    subst hs ht
    exact actionRelationComposition_exists U G a
  exact key _ _ (actionRelation_source_eq U G a) (actionRelation_target_eq U G a)

/-- The graph relation of an action whose stabilizers act faithfully on residue fields is an
étale equivalence relation. -/
@[stacks 02Z2 "étale equivalence relation"]
theorem actionRelation_isEtaleEquivalenceRelation (a : G →* Aut U)
    (ha : ActsNontriviallyOnFixedResidueFields U G a) :
    IsEtaleEquivalenceRelation (actionRelation U G a) := by
  have hs := actionRelation_source_eq U G a
  have ht := actionRelation_target_eq U G a
  let : Etale (actionRelation U G a).source.left := actionRelationSource_etale U G a
  let : Etale (actionRelation U G a).target.left := actionRelationTarget_etale U G a
  have hpoints (k : Type u) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ S) :
      Function.Injective (fun r : Over.mk p ⟶ actionRelationScheme U G ↦
        r ≫ actionRelation U G a) ∧
      Equivalence ((actionRelation U G a).Rel (T := Over.mk p)) :=
    ⟨actionRelationFieldPoint_injective U G a ha p, actionRelation_rel_equivalence U G a _⟩
  have unram (f : actionRelationScheme U G ⟶ U) [Etale f.left] :
      AlgebraicGeometry.Unramified f.left :=
    ⟨fun x ↦ ((etaleAt_iff_smoothAt_and_unramifiedAt f.left x).mp
      ((etale_iff_forall_etaleAt f.left).mp inferInstance x)).2⟩
  let : AlgebraicGeometry.Unramified (actionRelation U G a).source.left := unram _
  let : AlgebraicGeometry.Unramified (actionRelation U G a).target.left := unram _
  obtain ⟨c', hct', hcs'⟩ := actionRelation_comp_exists U G a
  let : IsEquivalenceRelation (actionRelation U G a).target
      (actionRelation U G a).source :=
    isEquivalenceRelation_of_unramified
      (actionRelation U G a) hpoints
      (actionRelationIdentity U G)
      (by rw [ht]; exact actionRelationIdentity_target U G a)
      (by rw [hs]; exact actionRelationIdentity_source U G)
      (actionRelationInverse U G a)
      (by rw [ht, hs]; exact actionRelationInverse_target U G a)
      (by rw [hs, ht]; exact actionRelationInverse_source U G a)
      c' hct' hcs'
  exact ⟨⟩

variable (B : BigFppfSite.{u}) (hS : B.Contains S)
variable (V : BigFppfOver B S hS)

/-- The underlying scheme over `S` of an object of a big fppf site over `S`. -/
abbrev underlyingOver : Over S := (Over.post B.inclusion).obj V

/-- The quotient of a scheme in a big fppf site by a group action: the quotient sheaf of the
graph relation of the action. -/
@[stacks 02Z2 "quotient",
  stacks 02Z3 "the quotient U/G of a scheme by a group action satisfying (*)"]
abbrev actionQuotient (a : G →* Aut (underlyingOver B hS V))
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (actionRelation (underlyingOver B hS V) G a)).obj

section SiteRelation

variable (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)

/-- The relation scheme of a group action, as an object of a big fppf site large enough to
contain it. -/
def siteActionRelationScheme : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (actionRelationScheme (underlyingOver B hS V) G).hom : B.obj hR ⟶ B.obj hS)

/-- The target map of the graph relation of a group action, as a morphism in a big fppf
site. -/
def siteActionRelationTarget (a : G →* Aut (underlyingOver B hS V)) :
    siteActionRelationScheme G B hS V hR ⟶ V :=
  Over.homMk (ObjectProperty.homMk
    (actionRelationTarget (underlyingOver B hS V) G a).left) (by
      apply ObjectProperty.hom_ext
      exact (actionRelationTarget (underlyingOver B hS V) G a).w)

/-- The source map of the graph relation of a group action, as a morphism in a big fppf
site. -/
def siteActionRelationSource :
    siteActionRelationScheme G B hS V hR ⟶ V :=
  Over.homMk (ObjectProperty.homMk
    (actionRelationSource (underlyingOver B hS V) G).left) (by
      apply ObjectProperty.hom_ext
      exact (actionRelationSource (underlyingOver B hS V) G).w)

end SiteRelation

/-! ### The relation scheme stays inside the site -/

private theorem schemeSize_coproduct_le_aleph0_of_isEmpty {I : Type u}
    (Y : I → Scheme.{u}) (hY : ∀ i, IsEmpty (Y i : Type u)) :
    (∐ Y).size ≤ ℵ₀ := by
  refine size_le_aleph0_of_isEmpty (∐ Y) ⟨fun x ↦ ?_⟩
  have hSigma : IsEmpty (Σ i, (Y i : Type u)) := ⟨fun z ↦ (hY z.1).false z.2⟩
  exact hSigma.false ((AlgebraicGeometry.sigmaMk Y).symm x)

private theorem card_residueField_hom_le (X : Scheme.{u}) {k : Type u} [Field k]
    (hk : Cardinal.mk k ≤ X.size) (y : X) :
    Cardinal.mk (X.residueField y ⟶ CommRingCat.of k) ≤ 2 ^ X.size := by
  have hκ := X.aleph0_le_size
  calc
    Cardinal.mk (X.residueField y ⟶ CommRingCat.of k) ≤ Cardinal.mk (X.residueField y → k) := by
      let fwd : (X.residueField y ⟶ CommRingCat.of k) → (X.residueField y → k) := fun f r ↦ f r
      apply Cardinal.mk_le_of_injective (f := fwd)
      intro f g h
      exact CommRingCat.hom_ext (RingHom.ext (fun r ↦ congrFun h r))
    _ = Cardinal.mk k ^ Cardinal.mk (X.residueField y) :=
      (Cardinal.power_def k (X.residueField y)).symm
    _ ≤ X.size ^ X.size := by
      apply le_trans (Cardinal.power_le_power_right hk)
      exact Cardinal.power_le_power_left
        (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ)) (X.residueField_size_le y)
    _ = 2 ^ X.size := Cardinal.power_self_eq hκ

private theorem actionGroup_card_le_power (a : G →* Aut U)
    (ha : ActsNontriviallyOnFixedResidueFields U G a) (hne : Nonempty U.left) :
    Cardinal.mk (Shrink.{u} G) ≤ 2 ^ U.left.size := by
  classical
  let x : U.left := Classical.choice hne
  let k := U.left.residueField x
  let z : Spec (.of k) ⟶ U.left := U.left.fromSpecResidueField x
  let eG : G ≃ Shrink.{u} G := equivShrink.{u} G
  let φ : Shrink.{u} G → (Spec (.of k) ⟶ U.left) :=
    fun g ↦ z ≫ (a (eG.symm g)).asIso.hom.left
  have hφ : Function.Injective φ := fun g h hgh ↦
    eG.symm.injective (actionRelation_eq_of_comp_eq U G a ha z hgh)
  have hGroupMaps : Cardinal.mk (Shrink.{u} G) ≤
      Cardinal.mk (Σ y : U.left, U.left.residueField y ⟶ CommRingCat.of k) := by
    calc
      Cardinal.mk (Shrink.{u} G) ≤ Cardinal.mk (Spec (.of k) ⟶ U.left) :=
        Cardinal.mk_le_of_injective (f := φ) hφ
      _ = Cardinal.mk (Σ y : U.left, U.left.residueField y ⟶ CommRingCat.of k) :=
        Cardinal.mk_congr (Scheme.SpecToEquivOfField k U.left)
  let κ : Cardinal.{u} := U.left.size
  have hκ : Cardinal.aleph0 ≤ κ := U.left.aleph0_le_size
  have hk : Cardinal.mk k ≤ κ := U.left.residueField_size_le x
  have hMaps : Cardinal.mk (Σ y : U.left, U.left.residueField y ⟶ CommRingCat.of k) ≤
      2 ^ κ := by
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun y : U.left ↦
          Cardinal.mk (U.left.residueField y ⟶ CommRingCat.of k)) ≤
          Cardinal.mk U.left * ⨆ y : U.left,
            Cardinal.mk (U.left.residueField y ⟶ CommRingCat.of k) :=
        Cardinal.sum_le_mk_mul_iSup _
      _ ≤ (2 ^ κ) * (2 ^ κ) :=
        mul_le_mul (Scheme.mk_le_two_pow_size U.left)
          (ciSup_le' (card_residueField_hom_le U.left hk)) (by positivity) (by positivity)
      _ = 2 ^ κ := Cardinal.mul_eq_self (le_trans hκ (Cardinal.cantor κ).le)
  exact hGroupMaps.trans hMaps

/-- The relation scheme of a group action with residue-field-faithful stabilizers again
satisfies the size cutoff of a big fppf site containing the scheme acted on, so the graph
relation is a relation inside that site. -/
theorem contains_actionRelationScheme (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a) :
    B.Contains (actionRelationScheme (underlyingOver B hS V) G).left := by
  classical
  let W : Over S := underlyingOver B hS V
  let eG : G ≃ Shrink.{u} G := equivShrink.{u} G
  let Y : Shrink.{u} G → Scheme.{u} := fun _ ↦ W.left
  have hcongr := Scheme.size_congr (actionRelationUnderlyingIso W G)
  have hreindex : (∐ fun _ : G ↦ W.left).size = (∐ Y).size :=
    Scheme.size_congr (Sigma.reindex eG Y)
  show (actionRelationScheme W G).left.size < B.cutoff
  rw [hcongr, hreindex]
  by_cases hne : Nonempty W.left
  · let κ : Cardinal.{u} := W.left.size
    have hindex : Cardinal.mk (Shrink.{u} G) ≤ 2 ^ κ :=
      actionGroup_card_le_power W G a ha hne
    have hκ : Cardinal.aleph0 ≤ κ := W.left.aleph0_le_size
    have hpow : κ ≤ 2 ^ κ := by
      rw [← Cardinal.power_self_eq hκ]
      exact Cardinal.self_le_power κ (Cardinal.one_le_aleph0.trans hκ)
    have hcoprod : (∐ Y).size ≤ 2 ^ κ :=
      schemeSize_coproduct_le Y (2 ^ κ) (hκ.trans hpow) hindex (fun _ ↦ hpow)
    have hWsize : W.left.size < B.cutoff := V.left.property
    exact hcoprod.trans_lt (B.cutoff_isStrongPrelimit hWsize)
  · exact (schemeSize_coproduct_le_aleph0_of_isEmpty Y fun _ ↦ ⟨fun x ↦ hne ⟨x⟩⟩).trans_lt
      B.aleph0_lt_cutoff

end AlgebraicGeometry.Space

end
