module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionPushPull
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of families of cycles on fibres commutes with base change

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, let `r, e ≥ 0`,
let `α` be a family of `r`-cycles on the fibres of `X/Y`, let `β` be a family of `e`-cycles on
the fibres of `Y/S`, and let `h : S' ⟶ S` be an arbitrary morphism of schemes. Write
`Y' = Y ×_S S'` and `X' = X ×_Y Y'`, let `α'` be the base change of `α` along `Y' ⟶ Y` and let
`β'` be the base change of `β` along `h`. This file proves that `α' ∘ β'` is the base change of
`α ∘ β` along `h`.

## Main definitions

* `Stacks.Chow.compBaseChangeChain` — the canonical comparison of the fibre of `X'/S'` over a
  point `t` of `S'` with the base change of `X ×_Y Y_{h t}` along `κ(t)/κ(h t)`; both are
  `X ×_Y Y'_t`.
* `Stacks.Chow.compBaseChangeFibre` — the canonical comparison, over `Spec κ(t)`, of the base
  change of `X ×_Y Y_{h t}` along `κ(t)/κ(h t)` with the base change of the fibre `X_{h t}`.

## Main results

* `Stacks.Chow.capCoeff_baseChangeFamily_of_residueIso` — base change of a family of cycles
  along a morphism inducing isomorphisms on residue fields is a relabelling of the action.
* `Stacks.Chow.compFamily_baseChangeFamily` — the base change of `α ∘ β` is `α' ∘ β'`.

## Implementation notes

The source's proof computes the fibre of `α' ∘ β'` over a point `s'` of `S'` as
`(Y'_{s'} → Y')^*α' ∩ β'_{s'}`, observes that the first factor is the base change of `α` along
the composite `Y'_{s'} → Y' → Y`, that `β'_{s'}` is the base change of `β_s` along
`κ(s')/κ(s)`, and concludes by Tag 0H68, the compatibility of the action with flat base change,
applied to the base change `Spec κ(s') → Spec κ(s)`.

The formalization follows that route. The composition is unfolded on each fibre into an action
by `Stacks.Chow.compFamily_apply_cap`; the base change of `α` is moved from the route
`Y'_t → Y' → Y` to the route `Y'_t → Y_{h t} → Y` by the two orientations
`Stacks.Chow.baseChangeFamily_baseChangeFamily_of_residueIso` and
`Stacks.Chow.baseChangeFamily_baseChangeFamily` of base change along a composite, the fibre
inclusion `Y_{h t} ⟶ Y` and the comparison `Stacks.Chow.fibreBaseChangeIso` both inducing
isomorphisms on residue fields; `Stacks.Chow.cap_baseChange` is Tag 0H68, and
`Stacks.Chow.baseChangeFamily_apply_flatPullbackWeight` presents the right hand side over the
same residue field base change. The two chains of canonical comparisons of iterated fibre
products are assembled into `Stacks.Chow.compBaseChangeChain` and
`Stacks.Chow.compBaseChangeFibre`, whose compatibility with the projections to `X` and to
`Spec κ(t)` is what makes the two sides agree.

The two families compared live on the canonically isomorphic schemes `(X ×_Y (Y ×_S S'))_t` and
`(X ×_S S')_t`, and the comparison is `Stacks.Chow.fiberCycleRestrict` along the isomorphism
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which is injective on fibrewise cycle
groups, so the stated equality is the equality of the two families.

## References

* [Stacks Project, Tag 0H6K](https://stacks.math.columbia.edu/tag/0H6K)
* [Stacks Project, Tag 0H68](https://stacks.math.columbia.edu/tag/0H68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Equal morphisms of schemes agree on points. -/
private theorem hom_apply_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (x : X) :
    a x = b x := by rw [h]

/-! ### The action against a base change along a morphism with isomorphic residue fields -/

/-- Base changing a family of cycles on fibres along a morphism `ι` which induces isomorphisms
on all residue fields does not change the coefficients of the action: the action of the base
change against a cycle whose coefficients are read off `ι` has the coefficients of the original
action. -/
theorem capCoeff_baseChangeFamily_of_residueIso {X Y Y' : Scheme.{u}} (A : X ⟶ Y)
    [LocallyOfFiniteType A] (ι : Y' ⟶ Y) (hres : ∀ y : Y', IsIso (ι.residueFieldMap y)) (r : ℕ)
    (δ : FamilyOfCycles A r) (γ' : AlgebraicCycle Y' ℤ) (γ : AlgebraicCycle Y ℤ)
    (hγ : ∀ y : Y', γ' y = γ (ι y)) (x : ↥(pullback A ι : Scheme.{u})) :
    capCoeff (pullback.snd A ι) (baseChangeFamily A ι r δ) γ' x =
      capCoeff A δ γ (pullback.fst A ι x) := by
  have hpt : ι (pullback.snd A ι x) = A (pullback.fst A ι x) := by
    simpa only [Scheme.Hom.comp_apply] using
      (hom_apply_congr (pullback.condition (f := A) (g := ι)) x).symm
  rw [baseChangeFamily_eq_baseChangeFamilyOfResidueIso A ι hres r δ]
  unfold capCoeff
  rw [hγ, baseChangeFamilyOfResidueIso_apply A ι hres r δ,
    familyOfCycles_restrictedFiberMap_asFiber A (pullback.snd A ι) (pullback.fst A ι) ι
      pullback.condition δ x, hpt]

/-- The coefficients of the action of the base change along a composite `g' ≫ g` are those of the
action of the iterated base change, read through `pullbackLeftPullbackSndIso`. -/
theorem capCoeff_baseChangeFamily_comp' {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (g' : T' ⟶ T) (r : ℕ) (α : FamilyOfCycles f r)
    (hcomp : ∀ t : T', baseChangeFamily (pullback.snd f g) g' r (baseChangeFamily f g r α) t =
      fiberCycleRestrict (pullback.snd f (g' ≫ g)) (pullback.snd (pullback.snd f g) g')
        (pullbackLeftPullbackSndIso f g g').hom
        (pullbackLeftPullbackSndIso_hom_snd f g g') t r (baseChangeFamily f (g' ≫ g) r α t))
    (β : AlgebraicCycle T' ℤ) (y : ↥(pullback f (g' ≫ g) : Scheme.{u})) :
    capCoeff (pullback.snd f (g' ≫ g)) (baseChangeFamily f (g' ≫ g) r α) β y =
      capCoeff (pullback.snd (pullback.snd f g) g')
        (baseChangeFamily (pullback.snd f g) g' r (baseChangeFamily f g r α)) β
        ((pullbackLeftPullbackSndIso f g g').inv y) := by
  rw [capCoeff_baseChangeFamily_comp f g g' r α hcomp β
    ((pullbackLeftPullbackSndIso f g g').inv y)]
  congr 1
  exact (Scheme.inv_hom_apply _ y).symm

/-! ### The two routes out of a fibre of a base change -/

section BaseChange

variable {X Y S S' : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
  [LocallyOfFiniteType g] (h : S' ⟶ S) (t : S')

omit [LocallyOfFiniteType g] in
/-- The two routes from the fibre of `Y' = Y ×_S S'` over `t` to `Y` agree: going through `Y'`,
and going through the fibre `Y_{h t}` after the identification of `Y'_t` with the residue field
base change of `Y_{h t}`. -/
theorem fiberι_comp_pullbackFst_eq :
    (pullback.snd g h).fiberι t ≫ pullback.fst g h =
      ((fibreBaseChangeIso g h t).hom ≫
          pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g) ≫ g.fiberι (h t) := by
  rw [fibreBaseChangeIso_hom_fst,
    restrictedFiberMap_fiberι g (pullback.snd g h) (pullback.fst g h) h pullback.condition t]

/-- The composite comparison from the fibre over `t` of `X' = X ×_Y Y' ⟶ S'` to the base change
along `κ(t)/κ(h t)` of `X ×_Y Y_{h t}`: the canonical comparisons of the iterated fibre products
presenting both as `X ×_Y Y'_t`. -/
def compBaseChangeChain :
    (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiber t ⟶
      (pullback (pullback.snd f (g.fiberι (h t)))
        (pullback.fst (g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g) : Scheme.{u}) :=
  (compFiberIso (pullback.snd f (pullback.fst g h)) (pullback.snd g h) t).inv ≫
    (pullbackLeftPullbackSndIso f (pullback.fst g h) ((pullback.snd g h).fiberι t)).hom ≫
      (pullback.congrHom (rfl : f = f) (fiberι_comp_pullbackFst_eq g h t)).hom ≫
        (pullbackLeftPullbackSndIso f (g.fiberι (h t))
            ((fibreBaseChangeIso g h t).hom ≫
              pullback.fst (g.fiberToSpecResidueField (h t))
                (residueFieldBaseChangeSituation h t).g)).inv ≫
          (pullbackLeftPullbackSndIso (pullback.snd f (g.fiberι (h t)))
              (pullback.fst (g.fiberToSpecResidueField (h t))
                (residueFieldBaseChangeSituation h t).g)
              (fibreBaseChangeIso g h t).hom).inv ≫
            pullback.fst
              (pullback.snd (pullback.snd f (g.fiberι (h t)))
                (pullback.fst (g.fiberToSpecResidueField (h t))
                  (residueFieldBaseChangeSituation h t).g))
              (fibreBaseChangeIso g h t).hom

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The comparison is compatible with the projections to `X`. -/
@[reassoc]
theorem compBaseChangeChain_comp_fst :
    compBaseChangeChain f g h t ≫
        pullback.fst (pullback.snd f (g.fiberι (h t)))
            (pullback.fst (g.fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g) ≫
          pullback.fst f (g.fiberι (h t)) =
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiberι t ≫
        pullback.fst f (pullback.fst g h) := by
  have h0 : (compFiberIso (pullback.snd f (pullback.fst g h)) (pullback.snd g h) t).inv ≫
      pullback.fst (pullback.snd f (pullback.fst g h)) ((pullback.snd g h).fiberι t) =
        (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiberι t :=
    pullbackRightPullbackFstIso_inv_fst (pullback.snd g h) (S'.fromSpecResidueField t)
      (pullback.snd f (pullback.fst g h))
  rw [compBaseChangeChain]
  simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullbackCongrHom_hom_fst,
    pullbackLeftPullbackSndIso_hom_fst, reassoc_of% h0]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The comparison lies over `Spec κ(t)`. -/
@[reassoc]
theorem compBaseChangeChain_comp_snd :
    compBaseChangeChain f g h t ≫
        pullback.snd (pullback.snd f (g.fiberι (h t)))
            (pullback.fst (g.fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g) ≫
          pullback.snd (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g =
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiberToSpecResidueField t := by
  have h0 : (compFiberIso (pullback.snd f (pullback.fst g h)) (pullback.snd g h) t).inv ≫
      pullback.snd (pullback.snd f (pullback.fst g h)) ((pullback.snd g h).fiberι t) ≫
        (pullback.snd g h).fiberToSpecResidueField t =
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiberToSpecResidueField t :=
    pullbackRightPullbackFstIso_inv_snd_snd (pullback.snd g h) (S'.fromSpecResidueField t)
      (pullback.snd f (pullback.fst g h))
  have key : (compFiberIso (pullback.snd f (pullback.fst g h)) (pullback.snd g h) t).inv ≫
      pullback.snd (pullback.snd f (pullback.fst g h)) ((pullback.snd g h).fiberι t) ≫
        (fibreBaseChangeIso g h t).hom ≫
          pullback.snd (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g =
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiberToSpecResidueField t := by
    rw [fibreBaseChangeIso_hom_snd]
    exact h0
  rw [compBaseChangeChain]
  simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd_assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd_assoc, pullbackCongrHom_hom_snd_assoc,
    pullbackLeftPullbackSndIso_hom_snd_assoc]
  exact key

/-! ### The comparison of the two presentations of `X ×_S Spec κ(t)` -/

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The canonical isomorphism `X ×_Y Y_s ≅ X_s` is compatible with the inclusions into `X`. -/
@[reassoc]
theorem compFiberIso_hom_fiberι (s : S) :
    (compFiberIso f g s).hom ≫ (f ≫ g).fiberι s = pullback.fst f (g.fiberι s) :=
  pullbackRightPullbackFstIso_hom_fst g (S.fromSpecResidueField s) f

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The canonical isomorphism `X ×_Y Y_s ≅ X_s` lies over `Spec κ(s)`. -/
@[reassoc]
theorem compFiberIso_hom_fiberToSpecResidueField (s : S) :
    (compFiberIso f g s).hom ≫ (f ≫ g).fiberToSpecResidueField s =
      pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s :=
  pullbackRightPullbackFstIso_hom_snd g (S.fromSpecResidueField s) f

/-- The comparison, over `Spec κ(t)`, of the base change along `κ(t)/κ(h t)` of `X ×_Y Y_{h t}`
with the base change along `κ(t)/κ(h t)` of the fibre `X_{h t}`. -/
def compBaseChangeFibre :
    (pullback (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g : Scheme.{u}) ⟶
      (pullback ((f ≫ g).fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g : Scheme.{u}) :=
  pullback.map _ _ _ _ (compFiberIso f g (h t)).hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, compFiberIso_hom_fiberToSpecResidueField]) (by simp)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The comparison of the two base changes is compatible with the projections to the fibres. -/
@[reassoc]
theorem compBaseChangeFibre_comp_fst :
    compBaseChangeFibre f g h t ≫
        pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g =
      pullback.fst (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g ≫ (compFiberIso f g (h t)).hom := by
  dsimp only [compBaseChangeFibre, pullback.map]
  rw [pullback.lift_fst]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The comparison of the two base changes lies over `Spec κ(t)`. -/
@[reassoc]
theorem compBaseChangeFibre_comp_snd :
    compBaseChangeFibre f g h t ≫
        pullback.snd ((f ≫ g).fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g =
      pullback.snd (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g := by
  dsimp only [compBaseChangeFibre, pullback.map]
  rw [pullback.lift_snd, Category.comp_id]

/-- The comparison of the two base changes is an isomorphism. -/
instance : IsIso (compBaseChangeFibre f g h t) := by
  unfold compBaseChangeFibre
  infer_instance

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The two comparisons agree: the fibre over `t` of `X'/S'` reaches the base change of the
fibre `X_{h t}` along `κ(t)/κ(h t)` the same way through `X ×_Y Y_{h t}` as through
`X ×_S S'`. -/
theorem compBaseChangeChain_comp_compBaseChangeFibre :
    compBaseChangeChain f g h t ≫
        (pullbackRightPullbackFstIso (g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g
          (pullback.snd f (g.fiberι (h t)))).hom ≫ compBaseChangeFibre f g h t =
      fiberRestrict (pullback.snd (f ≫ g) h)
          (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
          (pullbackRightPullbackFstIso g h f).hom
          (pullbackRightPullbackFstIso_hom_snd g h f) t ≫
        (fibreBaseChangeIso (f ≫ g) h t).hom := by
  have d1 : compBaseChangeChain f g h t ≫
        (pullbackRightPullbackFstIso (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g
            (pullback.snd f (g.fiberι (h t)))).hom ≫ compBaseChangeFibre f g h t ≫
          pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g ≫ (f ≫ g).fiberι (h t) =
      fiberRestrict (pullback.snd (f ≫ g) h)
            (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
            (pullbackRightPullbackFstIso g h f).hom
            (pullbackRightPullbackFstIso_hom_snd g h f) t ≫
          (fibreBaseChangeIso (f ≫ g) h t).hom ≫
            pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g ≫ (f ≫ g).fiberι (h t) := by
    rw [compBaseChangeFibre_comp_fst_assoc, compFiberIso_hom_fiberι,
      pullbackRightPullbackFstIso_hom_fst_assoc, compBaseChangeChain_comp_fst,
      fibreBaseChangeIso_hom_fst_assoc,
      restrictedFiberMap_fiberι (f ≫ g) (pullback.snd (f ≫ g) h) (pullback.fst (f ≫ g) h) h
        pullback.condition t,
      fiberRestrict_fiberι_assoc, pullbackRightPullbackFstIso_hom_fst]
  have d2 : compBaseChangeChain f g h t ≫
        (pullbackRightPullbackFstIso (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g
            (pullback.snd f (g.fiberι (h t)))).hom ≫ compBaseChangeFibre f g h t ≫
          pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g ≫
            (f ≫ g).fiberToSpecResidueField (h t) =
      fiberRestrict (pullback.snd (f ≫ g) h)
            (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
            (pullbackRightPullbackFstIso g h f).hom
            (pullbackRightPullbackFstIso_hom_snd g h f) t ≫
          (fibreBaseChangeIso (f ≫ g) h t).hom ≫
            pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
                (residueFieldBaseChangeSituation h t).g ≫
              (f ≫ g).fiberToSpecResidueField (h t) := by
    rw [compBaseChangeFibre_comp_fst_assoc, compFiberIso_hom_fiberToSpecResidueField,
      pullback.condition (f := pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
        (g := (residueFieldBaseChangeSituation h t).g),
      pullbackRightPullbackFstIso_hom_snd_assoc, compBaseChangeChain_comp_snd_assoc,
      fibreBaseChangeIso_hom_fst_assoc,
      restrictedFiberMap_comp_fiberToSpecResidueField (f ≫ g) (pullback.snd (f ≫ g) h)
        (pullback.fst (f ≫ g) h) h pullback.condition t,
      fiberRestrict_fiberToSpecResidueField_assoc, residueFieldBaseChangeSituation_g]
  have d3 : compBaseChangeChain f g h t ≫
        (pullbackRightPullbackFstIso (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g
            (pullback.snd f (g.fiberι (h t)))).hom ≫ compBaseChangeFibre f g h t ≫
          pullback.snd ((f ≫ g).fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g =
      fiberRestrict (pullback.snd (f ≫ g) h)
            (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
            (pullbackRightPullbackFstIso g h f).hom
            (pullbackRightPullbackFstIso_hom_snd g h f) t ≫
          (fibreBaseChangeIso (f ≫ g) h t).hom ≫
            pullback.snd ((f ≫ g).fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g := by
    rw [compBaseChangeFibre_comp_snd, pullbackRightPullbackFstIso_hom_snd,
      compBaseChangeChain_comp_snd, fibreBaseChangeIso_hom_snd,
      fiberRestrict_fiberToSpecResidueField]
  refine pullback.hom_ext (pullback.hom_ext
    (?_ : _ ≫ (f ≫ g).fiberι (h t) = _ ≫ (f ≫ g).fiberι (h t))
    (?_ : _ ≫ (f ≫ g).fiberToSpecResidueField (h t) = _ ≫ (f ≫ g).fiberToSpecResidueField (h t))) ?_
  · simpa only [Category.assoc] using d1
  · simpa only [Category.assoc] using d2
  · simpa only [Category.assoc] using d3

/-! ### Base change of a composition -/

/-- The formation of the composition `α ∘ β` of a family of `r`-cycles on the fibres of `X/Y` with
a family of `e`-cycles on the fibres of `Y/S` is compatible with an arbitrary base change
`h : S' ⟶ S`: the composition of the base change of `α` along `Y ×_S S' ⟶ Y` with the base change
of `β` along `h` is the base change of `α ∘ β` along `h`, read on the fibre over a point `t` of
`S'` through the canonical identification of `(X ×_Y (Y ×_S S'))_t` with `(X ×_S S')_t`. -/
@[stacks 0H6K]
theorem compFamily_baseChangeFamily (r e : ℕ) (α : FamilyOfCycles f r)
    (β : FamilyOfCycles g e) :
    compFamily (pullback.snd f (pullback.fst g h)) (pullback.snd g h) r e
        (baseChangeFamily f (pullback.fst g h) r α) (baseChangeFamily g h e β) t =
      fiberCycleRestrict (pullback.snd (f ≫ g) h)
        (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
        (pullbackRightPullbackFstIso g h f).hom
        (pullbackRightPullbackFstIso_hom_snd g h f) t (r + e)
        (baseChangeFamily (f ≫ g) h (r + e) (compFamily f g r e α β) t) := by
  classical
  let : LocallyOfFiniteType (g.fiberToSpecResidueField (h t)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField (h t))))
  let : LocallyOfFiniteType ((pullback.snd g h).fiberToSpecResidueField t) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (pullback.snd g h) (S'.fromSpecResidueField t)))
  have hγ : ∀ y : ↥((pullback.snd g h).fiber t),
      (baseChangeFamily g h e β t : AlgebraicCycle ((pullback.snd g h).fiber t) ℤ) y =
        (baseChangeCyclePullback (residueFieldBaseChangeSituation h t)
            (g.fiberToSpecResidueField (h t)) (e : ℤ) (β (h t)) :
          AlgebraicCycle (pullback (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g : Scheme.{u}) ℤ)
          ((fibreBaseChangeIso g h t).hom y) := by
    intro y
    rw [baseChangeFamily_eq_baseChangeFiberCycle g h e β t]
    rfl
  have key : ∀ z : ↥((pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiber t),
      (compFamily (pullback.snd f (pullback.fst g h)) (pullback.snd g h) r e
          (baseChangeFamily f (pullback.fst g h) r α) (baseChangeFamily g h e β) t :
        AlgebraicCycle ((pullback.snd f (pullback.fst g h) ≫ pullback.snd g h).fiber t) ℤ) z =
      capCoeff
        (pullback.snd (pullback.snd f (g.fiberι (h t)))
          (pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g))
        (baseChangeFamily (pullback.snd f (g.fiberι (h t)))
          (pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g) r
          (baseChangeFamily f (g.fiberι (h t)) r α))
        (baseChangeCyclePullback (residueFieldBaseChangeSituation h t)
            (g.fiberToSpecResidueField (h t)) (e : ℤ) (β (h t)) :
          AlgebraicCycle (pullback (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g : Scheme.{u}) ℤ)
        (compBaseChangeChain f g h t z) := by
    intro z
    rw [compFamily_apply_cap (pullback.snd f (pullback.fst g h)) (pullback.snd g h) r e
        (baseChangeFamily f (pullback.fst g h) r α) (baseChangeFamily g h e β) t z,
      cap_apply,
      capCoeff_baseChangeFamily_comp f (pullback.fst g h) ((pullback.snd g h).fiberι t) r α
        (baseChangeFamily_baseChangeFamily_of_residueIso f (pullback.fst g h)
          ((pullback.snd g h).fiberι t)
          (fun w ↦ isIso_residueFieldMap_of_isPreimmersion ((pullback.snd g h).fiberι t) w) r α),
      capCoeff_baseChangeFamily_congr f _ _ (fiberι_comp_pullbackFst_eq g h t) r α,
      capCoeff_baseChangeFamily_comp' f (g.fiberι (h t))
        ((fibreBaseChangeIso g h t).hom ≫
          pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g) r α
        (baseChangeFamily_baseChangeFamily f (g.fiberι (h t))
          ((fibreBaseChangeIso g h t).hom ≫
            pullback.fst (g.fiberToSpecResidueField (h t))
              (residueFieldBaseChangeSituation h t).g)
          (fun w ↦ isIso_residueFieldMap_of_isPreimmersion (g.fiberι (h t)) w) r α),
      capCoeff_baseChangeFamily_comp' (pullback.snd f (g.fiberι (h t)))
        (pullback.fst (g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g) (fibreBaseChangeIso g h t).hom r
        (baseChangeFamily f (g.fiberι (h t)) r α)
        (baseChangeFamily_baseChangeFamily_of_residueIso (pullback.snd f (g.fiberι (h t)))
          (pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g) (fibreBaseChangeIso g h t).hom
          (fun w ↦ inferInstance) r (baseChangeFamily f (g.fiberι (h t)) r α)),
      capCoeff_baseChangeFamily_of_residueIso
        (pullback.snd (pullback.snd f (g.fiberι (h t)))
          (pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g)) (fibreBaseChangeIso g h t).hom
        (fun w ↦ inferInstance) r
        (baseChangeFamily (pullback.snd f (g.fiberι (h t)))
          (pullback.fst (g.fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g) r
          (baseChangeFamily f (g.fiberι (h t)) r α)) _ _ hγ]
    congr 1
  have hfst : ∀ z : ↥(pullback
      (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
      (residueFieldBaseChangeSituation h t).g : Scheme.{u}),
      pullback.fst (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g z =
        (compFiberIso f g (h t)).inv
          (pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
            (residueFieldBaseChangeSituation h t).g (compBaseChangeFibre f g h t z)) := by
    intro z
    have hm := hom_apply_congr (compBaseChangeFibre_comp_fst f g h t) z
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hm
    rw [hm, Scheme.hom_inv_apply]
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hpt : compBaseChangeFibre f g h t
        ((pullbackRightPullbackFstIso (g.fiberToSpecResidueField (h t))
          (residueFieldBaseChangeSituation h t).g
          (pullback.snd f (g.fiberι (h t)))).hom (compBaseChangeChain f g h t x)) =
      (fibreBaseChangeIso (f ≫ g) h t).hom
        (fiberRestrict (pullback.snd (f ≫ g) h)
          (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
          (pullbackRightPullbackFstIso g h f).hom
          (pullbackRightPullbackFstIso_hom_snd g h f) t x) := by
    simpa only [Scheme.Hom.comp_apply] using
      hom_apply_congr (compBaseChangeChain_comp_compBaseChangeFibre f g h t) x
  rw [fiberCycleRestrict_apply, key x]
  refine (cap_apply (residueFieldBaseChangeSituation h t).baseChange
    (pullback.snd (g.fiberToSpecResidueField (h t)) (residueFieldBaseChangeSituation h t).g)
    (pullback.snd (pullback.snd f (g.fiberι (h t)))
      (pullback.fst (g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g))
    (baseChangeFamily (pullback.snd f (g.fiberι (h t)))
      (pullback.fst (g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g) r (baseChangeFamily f (g.fiberι (h t)) r α))
    (baseChangeCyclePullback (residueFieldBaseChangeSituation h t)
      (g.fiberToSpecResidueField (h t)) (e : ℤ) (β (h t))) _).symm.trans ?_
  refine (cap_baseChange (residueFieldBaseChangeSituation h t)
    (g.fiberToSpecResidueField (h t)) (pullback.snd f (g.fiberι (h t))) r (e : ℤ)
    (baseChangeFamily f (g.fiberι (h t)) r α) (β (h t)) _).trans ?_
  rw [baseChangeCyclePullback_apply,
    baseChangeFamily_apply_flatPullbackWeight (f ≫ g) h (r + e) (compFamily f g r e α β) t,
    compFamily_apply_cap f g r e α β (h t), hfst,
    flatPullbackWeight_eq_of_isIso (residueFieldBaseChangeSituation h t).baseChange
      (pullback.snd (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g)
      (pullback.snd ((f ≫ g).fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g)
      (compFiberIso f g (h t)).hom (compBaseChangeFibre f g h t)
      (compBaseChangeFibre_comp_snd f g h t)
      (pullback.fst (pullback.snd f (g.fiberι (h t)) ≫ g.fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g)
      (pullback.fst ((f ≫ g).fiberToSpecResidueField (h t))
        (residueFieldBaseChangeSituation h t).g)
      (compBaseChangeFibre_comp_fst f g h t).symm _ _,
    hpt, fst_fibreBaseChangeIso_hom]
  rfl

end BaseChange

end Stacks.Chow

end
