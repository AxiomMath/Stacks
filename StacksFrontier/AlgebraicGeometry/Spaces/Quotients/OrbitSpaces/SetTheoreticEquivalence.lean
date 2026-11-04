module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace

/-!
# Set-theoretic equivalence relations

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`. A
pre-relation `j : R ⟶ U ×_Z U` is a *set-theoretic pre-equivalence relation* when, for every
algebraically closed field `k` in the site and every `k`-valued point of `Z`, the relation it
induces on the `k`-valued points of `U` over that point is an equivalence relation — where an
arrow is only required to exist after one extension of the field. It is a *set-theoretic
equivalence relation* when it is moreover universally injective.

## Main definitions

* `AlgebraicGeometry.Space.fieldObject` is the object of the big fppf site over `S` given by
  a field in the site together with a morphism of its spectrum to `S`.
* `AlgebraicGeometry.Space.PreRelation.SetTheoreticRel` is the relation on the points of `U`
  over such a point of `Z`, with arrows allowed to appear after a field extension, and
  `AlgebraicGeometry.Space.PreRelation.GeometricRel` is the variant cut out by the arrows
  already present over the given field.
* `AlgebraicGeometry.Space.IsSetTheoreticPreEquivalenceRelation` and
  `AlgebraicGeometry.Space.IsSetTheoreticEquivalenceRelation` are the two conditions of the
  source.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_of_isPreEquivalenceRelation`:
  **Stacks 0492**, part (1), a pre-equivalence relation is a set-theoretic pre-equivalence
  relation; and its two instances
  `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_groupoidPreRelation` for a
  groupoid in algebraic spaces and
  `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_groupoidOfAction` for an
  action of a group algebraic space.
* `AlgebraicGeometry.Space.isSetTheoreticEquivalenceRelation_of_isEquivalenceRelation`:
  **Stacks 0492**, part (2), an equivalence relation is a set-theoretic equivalence
  relation.

## Implementation notes

An extension of the field is a field-valued point of `R` whose spectrum lies in the site
together with a morphism of its object of the site to the given one; the underlying morphism
of field spectra is the field extension. The two points of `U` are taken in the fibre of
`U(k)` over the specified point of `Z(k)`, which is why they are sections of the presheaf
rather than test points.

Both predicates are abbreviations, so clients can use their conjuncts and the
`Equivalence` API directly. Everything is stated for an arbitrary presheaf `Z` as base and
arbitrary objects of `CategoryTheory.Over Z`, matching
`AlgebraicGeometry.Space.PreRelation`; nothing here uses the algebraic-space axioms, which
are imposed by `AlgebraicGeometry.Space.UniversallyInjective` where the source needs them.

Passing from a pre-equivalence relation to a set-theoretic one is a translation between the
two shapes in which the induced relation on points is written: on test points, which is
`AlgebraicGeometry.Space.PreRelation.Rel`, and on sections of the presheaf over an object of
the site, which is `AlgebraicGeometry.Space.PreRelation.SetTheoreticRel`. Reflexivity and
symmetry need the relation only over the given field, so they are that translation and
nothing else. Transitivity has to amalgamate the two extension fields carrying the two
arrows, which is the compositum produced inside the site by
`AlgebraicGeometry.Space.exists_fieldSpec_common`; over it both arrows restrict and the
pre-equivalence property composes them.

For part (2) the universal injectivity is that of a monomorphism: by
`AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` an
internal equivalence relation is a monic pre-equivalence relation, a monomorphism of the
slice is monic on underlying presheaves by `CategoryTheory.Over.mono_left_of_mono`, and a
monic transformation is injective on sections over every object of the site, which is more
than `AlgebraicGeometry.Space.universallyInjective_of_fieldPoints` asks for.

## References

* [Stacks Project, Tag 0490](https://stacks.math.columbia.edu/tag/0490)
* [Stacks Project, Tag 0492](https://stacks.math.columbia.edu/tag/0492)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The object of the big fppf site over `S` determined by a field whose spectrum lies in the
site together with a morphism from that spectrum to `S`. -/
noncomputable abbrev fieldObject (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S) : BigFppfOver B S hS :=
  Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- **Stacks 0490.** Two points of `U` over the same `k`-valued point of `Z` are related when,
after one extension of `k`, an arrow of the pre-relation has them as its source and its
target. -/
abbrev PreRelation.SetTheoreticRel (j : PreRelation R U) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : Z.obj (op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj (op (fieldObject (hS := hS) k hk b)) //
      U.hom.app (op (fieldObject (hS := hS) k hk b)) v = β}) : Prop :=
  ∃ (r : FieldValuedPoint B S hS R.left)
    (f : r.siteObject B S hS R.left ⟶ fieldObject (hS := hS) k hk b),
    (j.source.left.app (op (r.siteObject B S hS R.left)) r.value =
        U.left.map f.op x.1) ∧
      (j.target.left.app (op (r.siteObject B S hS R.left)) r.value =
        U.left.map f.op y.1)

/-- The relation on one fibre of `U(k)` cut out by the arrows of the pre-relation already
present in `R(k)`, with no extension of `k` allowed. -/
abbrev PreRelation.GeometricRel (j : PreRelation R U) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : Z.obj (op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj (op (fieldObject (hS := hS) k hk b)) //
      U.hom.app (op (fieldObject (hS := hS) k hk b)) v = β}) : Prop :=
  ∃ r : R.left.obj (op (fieldObject (hS := hS) k hk b)),
    (j.source.left.app (op (fieldObject (hS := hS) k hk b)) r = x.1) ∧
      (j.target.left.app (op (fieldObject (hS := hS) k hk b)) r = y.1)

/-- **Stacks 0490, part (1).** A pre-relation is a *set-theoretic pre-equivalence relation*
when the relation it induces on the fibres of the points over every algebraically closed
field in the site is an equivalence relation, arrows being allowed to appear only after a
field extension. -/
@[stacks 0490 "part (1): set-theoretic pre-equivalence relation"]
abbrev IsSetTheoreticPreEquivalenceRelation (j : PreRelation R U) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S) (β : Z.obj (op (fieldObject (hS := hS) k hk b))),
    Equivalence (j.SetTheoreticRel k hk b β)

/-- **Stacks 0490, part (2).** A *set-theoretic equivalence relation* is a universally
injective set-theoretic pre-equivalence relation. -/
@[stacks 0490 "part (2): set-theoretic equivalence relation"]
abbrev IsSetTheoreticEquivalenceRelation (j : PreRelation R U) : Prop :=
  UniversallyInjective B S hS j.left ∧ IsSetTheoreticPreEquivalenceRelation j

/-! ### From a pre-equivalence relation to a set-theoretic one -/

/-- Restrict a point of `U` lying over a section of `Z` along a morphism of the site. -/
private abbrev restrictFibre {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {γ : Z.obj (op T)}
    (x : {v : U.left.obj (op T) // U.hom.app (op T) v = γ}) :
    {v : U.left.obj (op T') // U.hom.app (op T') v = Z.map g.op γ} :=
  ⟨U.left.map g.op x.1, by rw [NatTrans.naturality_apply, x.2]⟩

/-- A point of `U` lying over a section of `Z` on an object of the site, read as a test
point of `U` over that object. -/
private abbrev fibreTestPoint {T : BigFppfOver B S hS} {γ : Z.obj (op T)}
    (x : {v : U.left.obj (op T) // U.hom.app (op T) v = γ}) :
    TestPoint T (yonedaEquiv.symm γ) U :=
  ⟨yonedaEquiv.symm x.1, by rw [yonedaEquiv_symm_naturality_right, x.2]⟩

/-- The relation a pre-relation induces on the test points of an object of the site, read on
the points of `U` lying over a section of `Z`: two of them are related exactly when a section
of `R` has them as its target and its source. -/
private theorem rel_fibreTestPoint_iff (j : PreRelation R U) {T : BigFppfOver B S hS}
    {γ : Z.obj (op T)} (x y : {v : U.left.obj (op T) // U.hom.app (op T) v = γ}) :
    j.Rel (yonedaEquiv.symm γ) (fibreTestPoint x) (fibreTestPoint y) ↔
      ∃ ρ : R.left.obj (op T), j.target.left.app (op T) ρ = x.1 ∧
        j.source.left.app (op T) ρ = y.1 := by
  constructor
  · rintro ⟨r, hrt, hrs⟩
    exact ⟨yonedaEquiv r.1, by simpa [yonedaEquiv_comp] using congrArg yonedaEquiv hrt,
      by simpa [yonedaEquiv_comp] using congrArg yonedaEquiv hrs⟩
  · rintro ⟨ρ, hrt, hrs⟩
    have hbase : R.hom.app (op T) ρ = γ := by
      rw [← Over.w j.target]
      show U.hom.app (op T) (j.target.left.app (op T) ρ) = γ
      rw [hrt, x.2]
    refine ⟨⟨yonedaEquiv.symm ρ, ?_⟩, ?_, ?_⟩ <;>
      simp only [yonedaEquiv_symm_naturality_right, hbase, hrt, hrs]

/-- **Stacks 0492, part (1).** A pre-equivalence relation is a set-theoretic pre-equivalence
relation: over every algebraically closed field over the base, the relation its arrows induce
on the points of `U` — arrows being allowed to appear after an extension of the field — is an
equivalence relation. -/
@[stacks 0492 "part (1): a pre-equivalence relation"]
theorem isSetTheoreticPreEquivalenceRelation_of_isPreEquivalenceRelation
    (j : PreRelation R U) (hj : IsPreEquivalenceRelation j) :
    IsSetTheoreticPreEquivalenceRelation j := by
  intro k _ _ hk b β
  refine ⟨?_, ?_, ?_⟩
  · -- Reflexivity: the identity arrow over the given field.
    intro x
    obtain ⟨ρ, hrt, hrs⟩ := (rel_fibreTestPoint_iff j x x).mp
      ((hj (fieldObject (hS := hS) k hk b) (yonedaEquiv.symm β)).refl (fibreTestPoint x))
    refine ⟨⟨k, hk, b, ρ⟩, 𝟙 _, ?_, ?_⟩
    · show j.source.left.app (op (fieldObject (hS := hS) k hk b)) ρ =
        U.left.map (𝟙 (fieldObject (hS := hS) k hk b)).op x.1
      simpa only [op_id, Functor.map_id_apply] using hrs
    · show j.target.left.app (op (fieldObject (hS := hS) k hk b)) ρ =
        U.left.map (𝟙 (fieldObject (hS := hS) k hk b)).op x.1
      simpa only [op_id, Functor.map_id_apply] using hrt
  · -- Symmetry: reverse the arrow over the same extension field.
    intro x y hxy
    obtain ⟨r, f, hs, ht⟩ := hxy
    obtain ⟨ρ, hρt, hρs⟩ :=
      (rel_fibreTestPoint_iff j (restrictFibre f x) (restrictFibre f y)).mp
        ((hj _ _).symm ((rel_fibreTestPoint_iff j (restrictFibre f y)
          (restrictFibre f x)).mpr ⟨r.value, ht, hs⟩))
    exact ⟨⟨r.carrier, r.contained, r.toBase, ρ⟩, f, hρs, hρt⟩
  · -- Transitivity: amalgamate the two extension fields inside the site.
    intro x y z hxy hyz
    obtain ⟨r₁, f₁, hs₁, ht₁⟩ := hxy
    obtain ⟨r₂, f₂, hs₂, ht₂⟩ := hyz
    have hba₁ : f₁.left.hom ≫ b = r₁.toBase := congrArg (fun w ↦ w.hom) (Over.w f₁)
    have hba₂ : f₂.left.hom ≫ b = r₂.toBase := congrArg (fun w ↦ w.hom) (Over.w f₂)
    obtain ⟨Ω, instΩ, hΩ, c₁, c₂, key⟩ :=
      exists_fieldSpec_common B (K := r₁.carrier) (L := r₂.carrier) (M := k)
        r₁.contained r₂.contained f₁.left.hom f₂.left.hom
    have hbase : c₂ ≫ r₂.toBase = c₁ ≫ r₁.toBase := by
      rw [← hba₁, ← hba₂, ← Category.assoc, ← Category.assoc, key]
    let g₁ : (Over.mk (⟨c₁ ≫ r₁.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
        r₁.siteObject B S hS R.left :=
      Over.homMk (⟨c₁⟩ : B.obj hΩ ⟶ B.obj r₁.contained) (by ext; rfl)
    let g₂ : (Over.mk (⟨c₁ ≫ r₁.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
        r₂.siteObject B S hS R.left :=
      Over.homMk (⟨c₂⟩ : B.obj hΩ ⟶ B.obj r₂.contained) (by ext; exact hbase)
    have hg : g₂ ≫ f₂ = g₁ ≫ f₁ := by ext; exact key.symm
    have e₁s : j.source.left.app _ (R.left.map g₁.op r₁.value) =
        U.left.map (g₁ ≫ f₁).op x.1 := by
      rw [NatTrans.naturality_apply, hs₁, ← Functor.map_comp_apply, ← op_comp]
    have e₁t : j.target.left.app _ (R.left.map g₁.op r₁.value) =
        U.left.map (g₁ ≫ f₁).op y.1 := by
      rw [NatTrans.naturality_apply, ht₁, ← Functor.map_comp_apply, ← op_comp]
    have e₂s : j.source.left.app _ (R.left.map g₂.op r₂.value) =
        U.left.map (g₁ ≫ f₁).op y.1 := by
      rw [NatTrans.naturality_apply, hs₂, ← Functor.map_comp_apply, ← op_comp, hg]
    have e₂t : j.target.left.app _ (R.left.map g₂.op r₂.value) =
        U.left.map (g₁ ≫ f₁).op z.1 := by
      rw [NatTrans.naturality_apply, ht₂, ← Functor.map_comp_apply, ← op_comp, hg]
    obtain ⟨ρ, hρt, hρs⟩ :=
      (rel_fibreTestPoint_iff j (restrictFibre (g₁ ≫ f₁) z)
        (restrictFibre (g₁ ≫ f₁) x)).mp
        ((hj _ _).trans
          ((rel_fibreTestPoint_iff j (restrictFibre (g₁ ≫ f₁) z)
            (restrictFibre (g₁ ≫ f₁) y)).mpr ⟨_, e₂t, e₂s⟩)
          ((rel_fibreTestPoint_iff j (restrictFibre (g₁ ≫ f₁) y)
            (restrictFibre (g₁ ≫ f₁) x)).mpr ⟨_, e₁t, e₁s⟩))
    exact ⟨⟨Ω, hΩ, c₁ ≫ r₁.toBase, ρ⟩, g₁ ≫ f₁, hρs, hρt⟩

/-- **Stacks 0492, part (1).** The pre-relation of a groupoid in algebraic spaces is a
set-theoretic pre-equivalence relation. -/
@[stacks 0492 "part (1): a groupoid in algebraic spaces"]
theorem isSetTheoreticPreEquivalenceRelation_groupoidPreRelation
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A) :
    IsSetTheoreticPreEquivalenceRelation (groupoidPreRelation G) :=
  isSetTheoreticPreEquivalenceRelation_of_isPreEquivalenceRelation _
    (groupoidPreRelation_isPreEquivalenceRelation G)

/-- **Stacks 0492, part (1).** The pre-relation of the groupoid of an action of a group
algebraic space on an algebraic space is a set-theoretic pre-equivalence relation. -/
@[stacks 0492 "part (1): an action of a group algebraic space"]
theorem isSetTheoreticPreEquivalenceRelation_groupoidOfAction
    (A : AlgebraicSpaces B S hS) (G W : Over A.obj) [GrpObj G] [ModObj G W]
    (hG : IsAlgebraicSpace B S hS G.left) (hW : IsAlgebraicSpace B S hS W.left) :
    IsSetTheoreticPreEquivalenceRelation
      (groupoidPreRelation (groupoidOfAction A G W hG hW).groupoid) :=
  isSetTheoreticPreEquivalenceRelation_groupoidPreRelation _

/-- **Stacks 0492, part (2).** An equivalence relation is a set-theoretic equivalence
relation: it is a monomorphism, hence universally injective, and a pre-equivalence relation,
hence set-theoretically one. -/
@[stacks 0492 "part (2)"]
theorem isSetTheoreticEquivalenceRelation_of_isEquivalenceRelation (j : PreRelation R U)
    (hj : CategoryTheory.IsEquivalenceRelation j.target j.source) :
    IsSetTheoreticEquivalenceRelation j := by
  obtain ⟨hmono, hpre⟩ := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp hj
  have hleft : Mono j.left := @Over.mono_left_of_mono _ _ _ _ _ j hmono
  refine ⟨universallyInjective_of_fieldPoints B S hS j.left ?_,
    isSetTheoreticPreEquivalenceRelation_of_isPreEquivalenceRelation j hpre⟩
  intro p y hy
  have hval : p.value = y := yonedaEquiv.symm.injective (hleft.right_cancellation _ _ (by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right]
    exact congrArg yonedaEquiv.symm hy))
  exact ⟨p, 𝟙 _, by simp, by simpa using hval.symm⟩

end AlgebraicGeometry.Space

end
