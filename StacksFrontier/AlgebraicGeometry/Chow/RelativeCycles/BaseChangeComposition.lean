module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange

/-!
# Associativity of base change of families of cycles on fibres

Let `f : X ⟶ S` be locally of finite type, let `r ≥ 0`, let `g : S' ⟶ S` and `h : S'' ⟶ S'` be
morphisms of schemes and let `α` be a family of `r`-cycles on the fibres of `X/S`. Base changing
`α` along `g` and then along `h` gives a family of `r`-cycles on the fibres of
`(X ×_S S') ×_{S'} S'' ⟶ S''`, while base changing along `h ≫ g` gives one on the fibres of
`X ×_S S'' ⟶ S''`. This file identifies the two: the total spaces of the two base changes have
canonically isomorphic fibres over each point of `S''`, and the two families have the same
coefficients under that isomorphism.

This is the "associativity of base change" whose detail the proof of
[Stacks, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X) (2) omits, together with the
multiplicativity of the base change multiplicities that the source displays and the consequence
the source draws from it, `pr₁^* ∘ g^* = pr₂^* ∘ g^*` on the double overlap `S' ×_S S'`.

## Main definitions

* `Stacks.Chow.secondFiberMap` and `Stacks.Chow.compFiberMapOfBaseChange` — the canonical
  morphisms from the fibre of a twofold base change to the fibre of the first base change and to
  the fibre of `f`.
* `Stacks.Chow.compBaseChangeFiberIso` — the canonical isomorphism, over the spectrum of the
  residue field of a point `u` of `S''`, between the fibre of `(X ×_S S') ×_{S'} S''` over `u`
  and the fibre of `X ×_S S''` over `u`.
* `Stacks.Chow.baseChangeFiberCongr` — the identification of the base changes along two equal
  morphisms of bases.
* `Stacks.Chow.overlapComparison` — the canonical isomorphism between the two iterated base
  changes `(X ×_S S') ×_{S', pr_i} S''` over `S'' = S' ×_S S'`, and
  `Stacks.Chow.overlapFiberComparison` — the isomorphism it induces on the fibres over a point
  of `S''`.

## Main results

* `Stacks.Chow.baseChangeFamily_apply_comp` — the coefficient of a twofold base change at a
  point: the coefficient of `α` at the image point in the fibre of `f`, times a single
  multiplicity read on the fibre of the twofold base change.
* `Stacks.Chow.flatPullbackWeight_mul_comp` — the multiplicativity the source displays: the
  multiplicity for the composite is the product of the two multiplicities.
* `Stacks.Chow.baseChangeFamily_apply_compBaseChangeFiberIso` — `h^*(g^*α) = (h ≫ g)^*α` under
  `Stacks.Chow.compBaseChangeFiberIso`.
* `Stacks.Chow.baseChangeFamily_apply_overlapFiberComparison` — `pr₁^*(g^*α) = pr₂^*(g^*α)`
  under `Stacks.Chow.overlapFiberComparison`; this is the step of the proof of Tag 0H4X (2)
  which says that a base-changed family satisfies the descent condition of that part.

## Implementation notes

Base change of families of cycles on fibres, `Stacks.Chow.baseChangeFamily`, is defined
fibrewise by a coefficient formula, and
`Stacks.Chow.baseChangeFamily_apply_eq_baseChangeCyclePullbackSquare` recognizes that formula as
the base change of cycle groups `Stacks.Chow.baseChangeCyclePullbackSquare` along the cartesian
square which exhibits the fibre of `X ×_S S' ⟶ S'` over `t` as the base change of the fibre of
`f` over `g t` along `κ(t)/κ(g t)`. Composition is then Stacks 0FVP part (2),
`Stacks.Chow.baseChangeCyclePullbackSquare_comp_apply`, for the two composable flat base changes
of Chow situations attached to `κ(h u)/κ(g (h u))` and `κ(u)/κ(h u)`; the composite of those two
is the base change attached to `κ(u)/κ(g (h u))` because `Spec` turns
`AlgebraicGeometry.Scheme.residueFieldMap_comp` into the required factorization of the
base-change morphism.

The flat pullback of cycles along a morphism locally of finite type is unavailable here, because
a residue field extension need not be of finite type; this is why the composition used is the one
for base changes of Chow situations rather than
`Stacks.Chow.flatPullbackWeight_comp`.

The two fibres being compared are not equal but canonically isomorphic, and the comparison is
made along the isomorphism of fibres rather than by transporting a type; the isomorphism is the
one supplied by the universal property, two cartesian squares over the same cospan being
induced by the comparison of the total spaces, so that it also carries the scheme-level
information the descent argument needs: `Stacks.Chow.overlapComparison` lies over `S''` and over
`X`, which is what exhibits the iterated base change as a fibre product in two ways
(`Stacks.Chow.overlap_isPullback_snd` and `Stacks.Chow.overlap_isPullback_fst`) and makes it
preserve the residue transcendence degree (`Stacks.Chow.residueTrdeg_overlap`). For the double
overlap the two composite morphisms `pr₁ ≫ g` and `pr₂ ≫ g` are equal but not identical, so the
fibre comparison factors as the composite of two copies of
`Stacks.Chow.compBaseChangeFiberIso` with `Stacks.Chow.baseChangeFiberCongr`; that
factorization is `Stacks.Chow.overlapFiberComparison_hom_compBaseChangeFiberIso`.

`Stacks.Chow.flatPullbackWeight_mul_comp` needs the image point to have the relative dimension
that an `r`-cycle can occupy, and is proved by evaluating the coefficient identity on the
fundamental cycle of the reduced closure of that point, which has coefficient one there.

## References

* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Tag 0FVP](https://stacks.math.columbia.edu/tag/0FVP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S S' S'' : Scheme.{u}}

/-- The base change of a family of cycles on fibres, read as the base change of cycle groups
along the cartesian square exhibiting the fibre of `X ×_S S' ⟶ S'` over `t` as the base change
of the fibre of `f` over `g t` along `κ(t)/κ(g t)`. -/
theorem baseChangeFamily_apply_eq_baseChangeCyclePullbackSquare (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S')
    (x : (pullback.snd f g).fiber t) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (baseChangeCyclePullbackSquare (residueFieldBaseChangeSituation g t)
          (f.fiberToSpecResidueField (g t))
          (isPullback_restrictedFiberMap_baseChange f g t) (r : ℤ) (α (g t))).1 x := by
  rw [baseChangeCyclePullbackSquare_apply, baseChangeFamily_apply]
  rfl

section Comp

variable (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (h : S'' ⟶ S') (r : ℕ) (u : S'')

/-- The canonical morphism of fibres from the fibre of the twofold base change
`(X ×_S S') ×_{S'} S''` over `u` to the fibre of `X ×_S S'` over `h u`. -/
abbrev secondFiberMap :
    (pullback.snd (pullback.snd f g) h).fiber u ⟶ (pullback.snd f g).fiber (h u) :=
  restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h)
    (pullback.fst (pullback.snd f g) h) h pullback.condition u

/-- The canonical morphism of fibres from the fibre of the twofold base change
`(X ×_S S') ×_{S'} S''` over `u` to the fibre of `f` over `g (h u)`. -/
abbrev compFiberMapOfBaseChange :
    (pullback.snd (pullback.snd f g) h).fiber u ⟶ f.fiber (g (h u)) :=
  secondFiberMap f g h u ≫
    restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h u)

/-- `Spec` turns the factorization of the residue field map of a composite into a composite of
base-change morphisms, in the order the two base changes are taken. -/
theorem specMap_residueFieldMap_comp :
    Spec.map ((h ≫ g).residueFieldMap u) =
      Spec.map (h.residueFieldMap u) ≫ Spec.map (g.residueFieldMap (h u)) :=
  (congrArg Spec.map (Scheme.residueFieldMap_comp h g u)).trans (Spec.map_comp _ _)

omit [LocallyOfFiniteType f] in
/-- The square exhibiting the fibre of the twofold base change `(X ×_S S') ×_{S'} S''` over `u`
as the base change of the fibre of `f` over `g (h u)` along the composite of the two residue
field extensions. -/
theorem isPullback_compFiberMapOfBaseChange :
    IsPullback (compFiberMapOfBaseChange f g h u)
      ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
      (f.fiberToSpecResidueField (g (h u)))
      (Spec.map (h.residueFieldMap u) ≫ Spec.map (g.residueFieldMap (h u))) :=
  (isPullback_restrictedFiberMap_baseChange (pullback.snd f g) h u).paste_horiz
    (isPullback_restrictedFiberMap_baseChange f g (h u))

omit [LocallyOfFiniteType f] in
/-- The square exhibiting the fibre of `X ×_S S'' ⟶ S''` over `u` as the base change of the
fibre of `f` over `g (h u)`, with the residue field extension written as the composite of the
two extensions. -/
theorem isPullback_restrictedFiberMap_comp :
    IsPullback (restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
        pullback.condition u)
      ((pullback.snd f (h ≫ g)).fiberToSpecResidueField u)
      (f.fiberToSpecResidueField (g (h u)))
      (Spec.map (h.residueFieldMap u) ≫ Spec.map (g.residueFieldMap (h u))) := by
  have hsq := isPullback_restrictedFiberMap_baseChange f (h ≫ g) u
  rw [residueFieldBaseChangeSituation_g, specMap_residueFieldMap_comp g h u] at hsq
  exact hsq

/-- The canonical isomorphism, over `Spec κ(u)`, between the fibre over `u` of the twofold base
change `(X ×_S S') ×_{S'} S''` and the fibre over `u` of the single base change `X ×_S S''`:
both are the base change of the fibre of `f` over `g (h u)` along `κ(u)/κ(g (h u))`. -/
def compBaseChangeFiberIso :
    (pullback.snd (pullback.snd f g) h).fiber u ≅ (pullback.snd f (h ≫ g)).fiber u :=
  have hbase : pullback.snd (pullback.snd f g) h ≫ 𝟙 S'' =
      (pullbackLeftPullbackSndIso f g h).hom ≫ pullback.snd f (h ≫ g) := by simp
  have hfib : S''.fromSpecResidueField u ≫ 𝟙 S'' =
      𝟙 (Spec (S''.residueField u)) ≫ S''.fromSpecResidueField u := by simp
  (asIso (pullback.map (pullback.snd (pullback.snd f g) h) (S''.fromSpecResidueField u)
      (pullback.snd f (h ≫ g)) (S''.fromSpecResidueField u)
      (pullbackLeftPullbackSndIso f g h).hom (𝟙 _) (𝟙 _) hbase hfib) :
    pullback (pullback.snd (pullback.snd f g) h) (S''.fromSpecResidueField u) ≅
      pullback (pullback.snd f (h ≫ g)) (S''.fromSpecResidueField u))

omit [LocallyOfFiniteType f] in
/-- `Stacks.Chow.compBaseChangeFiberIso` is induced by the pasting isomorphism of the total
spaces. -/
@[reassoc] theorem compBaseChangeFiberIso_hom_fiberι :
    (compBaseChangeFiberIso f g h u).hom ≫ (pullback.snd f (h ≫ g)).fiberι u =
      (pullback.snd (pullback.snd f g) h).fiberι u ≫
        (pullbackLeftPullbackSndIso f g h).hom := by
  simp only [compBaseChangeFiberIso, asIso_hom, Scheme.Hom.fiberι, Scheme.Hom.fiber,
    pullback.map, pullback.lift_fst]

omit [LocallyOfFiniteType f] in
/-- `Stacks.Chow.compBaseChangeFiberIso` is an isomorphism over `Spec κ(u)`. -/
@[reassoc] theorem compBaseChangeFiberIso_hom_snd :
    (compBaseChangeFiberIso f g h u).hom ≫
        (pullback.snd f (h ≫ g)).fiberToSpecResidueField u =
      (pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u := by
  simp only [compBaseChangeFiberIso, asIso_hom, Scheme.Hom.fiberToSpecResidueField,
    Scheme.Hom.fiber, pullback.map, pullback.lift_snd, Category.comp_id]

omit [LocallyOfFiniteType f] in
/-- `Stacks.Chow.compBaseChangeFiberIso` commutes with the canonical morphisms to the fibre of
`f` over `g (h u)`. -/
@[reassoc] theorem compBaseChangeFiberIso_hom_fst :
    (compBaseChangeFiberIso f g h u).hom ≫
        restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
          pullback.condition u =
      compFiberMapOfBaseChange f g h u := by
  have hfib : IsPullback (f.fiberι (g (h u))) (f.fiberToSpecResidueField (g (h u))) f
      (S.fromSpecResidueField (g (h u))) := IsPullback.of_hasPullback _ _
  have hL : ((compBaseChangeFiberIso f g h u).hom ≫
        restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
          pullback.condition u) ≫ f.fiberι ((h ≫ g) u) =
      (pullback.snd (pullback.snd f g) h).fiberι u ≫
        pullback.fst (pullback.snd f g) h ≫ pullback.fst f g := by
    simp only [Category.assoc, restrictedFiberMap_fiberι,
      compBaseChangeFiberIso_hom_fiberι_assoc, pullbackLeftPullbackSndIso_hom_fst]
  have hR : compFiberMapOfBaseChange f g h u ≫ f.fiberι (g (h u)) =
      (pullback.snd (pullback.snd f g) h).fiberι u ≫
        pullback.fst (pullback.snd f g) h ≫ pullback.fst f g := by
    unfold compFiberMapOfBaseChange secondFiberMap
    rw [Category.assoc, restrictedFiberMap_fiberι, ← Category.assoc,
      restrictedFiberMap_fiberι, Category.assoc]
  have hL' : ((compBaseChangeFiberIso f g h u).hom ≫
        restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
          pullback.condition u) ≫ f.fiberToSpecResidueField ((h ≫ g) u) =
      (pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u ≫
        Spec.map (h.residueFieldMap u) ≫ Spec.map (g.residueFieldMap (h u)) := by
    rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField, ← Category.assoc,
      compBaseChangeFiberIso_hom_snd, specMap_residueFieldMap_comp]
    simp
  have hR' : compFiberMapOfBaseChange f g h u ≫ f.fiberToSpecResidueField (g (h u)) =
      (pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u ≫
        Spec.map (h.residueFieldMap u) ≫ Spec.map (g.residueFieldMap (h u)) := by
    unfold compFiberMapOfBaseChange secondFiberMap
    rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField, ← Category.assoc,
      restrictedFiberMap_comp_fiberToSpecResidueField]
    simp
  exact hfib.hom_ext (hL.trans hR.symm) (hL'.trans hR'.symm)

/-- The coefficient at a point `x` of the twofold base change of a family of `r`-cycles on
fibres: the coefficient of the family at the image of `x` in the fibre of `f`, times the
multiplicity with which `x` enters the inverse image of the reduced closure of that image under
the composite morphism of fibres. -/
theorem baseChangeFamily_apply_comp (α : FamilyOfCycles f r)
    (x : (pullback.snd (pullback.snd f g) h).fiber u) :
    (baseChangeFamily (pullback.snd f g) h r (baseChangeFamily f g r α) u :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) h).fiber u) ℤ) x =
      (α (g (h u)) : AlgebraicCycle (f.fiber (g (h u))) ℤ)
          (compFiberMapOfBaseChange f g h u x) *
        flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
          ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
          (compFiberMapOfBaseChange f g h u) (r : ℤ) x := by
  have key := baseChangeCyclePullbackSquare_comp_apply
    (residueFieldBaseChangeSituation g (h u))
    (fieldChowSituation ↥(S''.residueField u))
    (Spec.map (h.residueFieldMap u)) 0
    (residueFieldBaseChangeSituation h u).dimensionFunction_eq_add
    (f.fiberToSpecResidueField (g (h u)))
    (isPullback_restrictedFiberMap_baseChange f g (h u))
    (isPullback_restrictedFiberMap_baseChange (pullback.snd f g) h u)
    (r : ℤ) (α (g (h u))) x
  rw [baseChangeCyclePullbackSquare_apply, baseChangeCyclePullbackSquare_apply,
    baseChangeCyclePullbackSquare_apply] at key
  rw [baseChangeFamily_apply, baseChangeFamily_apply]
  exact key

/-- The coefficient of a twofold base change, written as the coefficient of the family at the
image point times the two multiplicities. -/
theorem baseChangeFamily_apply_comp_mul (α : FamilyOfCycles f r)
    (x : (pullback.snd (pullback.snd f g) h).fiber u) :
    (baseChangeFamily (pullback.snd f g) h r (baseChangeFamily f g r α) u :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) h).fiber u) ℤ) x =
      (α (g (h u)) : AlgebraicCycle (f.fiber (g (h u))) ℤ)
            (compFiberMapOfBaseChange f g h u x) *
          flatPullbackWeight (fieldChowSituation ↥(S'.residueField (h u)))
            ((pullback.snd f g).fiberToSpecResidueField (h u))
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
              (h u)) (r : ℤ) (secondFiberMap f g h u x) *
        flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
          ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
          (secondFiberMap f g h u) (r : ℤ) x := by
  rw [baseChangeFamily_apply, baseChangeFamily_apply]
  rfl

/-- **The displayed multiplicativity of the proof of Stacks Project, Tag 0H4X (2).** The
multiplicity with which a point of the fibre of a twofold base change enters is the product of
the two multiplicities of the two steps, at a point whose image has the relative dimension the
cycles in question occupy. -/
theorem flatPullbackWeight_mul_comp (x : (pullback.snd (pullback.snd f g) h).fiber u)
    (hx : relativeDimension (fieldChowSituation ↥(S.residueField (g (h u)))).dimensionFunction
      (f.fiberToSpecResidueField (g (h u))) (compFiberMapOfBaseChange f g h u x) = (r : ℤ)) :
    flatPullbackWeight (fieldChowSituation ↥(S'.residueField (h u)))
          ((pullback.snd f g).fiberToSpecResidueField (h u))
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h u))
          (r : ℤ) (secondFiberMap f g h u x) *
        flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
          ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
          (secondFiberMap f g h u) (r : ℤ) x =
      flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
        ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
        (compFiberMapOfBaseChange f g h u) (r : ℤ) x := by
  classical
  have hdim := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq
    (fieldChowSituation ↥(S.residueField (g (h u)))) (f.fiberToSpecResidueField (g (h u)))
    (compFiberMapOfBaseChange f g h u x) hx
  have hone := cycleAssociatedToClosedSubscheme_integralComponentAt_self
    (fieldChowSituation ↥(S.residueField (g (h u)))) (f.fiberToSpecResidueField (g (h u)))
    (k := (r : ℤ)) (compFiberMapOfBaseChange f g h u x) hdim
  set α : FamilyOfCycles f r := Function.update (0 : FamilyOfCycles f r) (g (h u))
    (cycleAssociatedToClosedSubscheme (fieldChowSituation ↥(S.residueField (g (h u))))
      (f.fiberToSpecResidueField (g (h u)))
      (integralComponentAt (compFiberMapOfBaseChange f g h u x)).subschemeι (r : ℤ))
  have hαs : α (g (h u)) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ↥(S.residueField (g (h u))))
        (f.fiberToSpecResidueField (g (h u)))
        (integralComponentAt (compFiberMapOfBaseChange f g h u x)).subschemeι (r : ℤ) :=
    Function.update_self _ _ _
  have key := (baseChangeFamily_apply_comp_mul f g h r u α x).symm.trans
    (baseChangeFamily_apply_comp f g h r u α x)
  rw [hαs, hone, one_mul, one_mul] at key
  exact key

/-- Base changing a family of cycles on fibres along `g` and then along `h` is base changing it
along `h ≫ g`, the two families being compared through the canonical isomorphism
`Stacks.Chow.compBaseChangeFiberIso` of the fibres over a point of `S''`. -/
theorem baseChangeFamily_apply_compBaseChangeFiberIso (α : FamilyOfCycles f r)
    (x : (pullback.snd (pullback.snd f g) h).fiber u) :
    (baseChangeFamily (pullback.snd f g) h r (baseChangeFamily f g r α) u :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) h).fiber u) ℤ) x =
      (baseChangeFamily f (h ≫ g) r α u :
          AlgebraicCycle ((pullback.snd f (h ≫ g)).fiber u) ℤ)
        ((compBaseChangeFiberIso f g h u).hom x) := by
  have hpt : restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
        pullback.condition u ((compBaseChangeFiberIso f g h u).hom x) =
      compFiberMapOfBaseChange f g h u x :=
    (Scheme.Hom.comp_apply (compBaseChangeFiberIso f g h u).hom _ x).symm.trans
      (congrArg (fun m : (pullback.snd (pullback.snd f g) h).fiber u ⟶ f.fiber (g (h u)) ↦ m x)
        (compBaseChangeFiberIso_hom_fst f g h u))
  have hw := flatPullbackWeight_eq_of_isIso (fieldChowSituation ↥(S''.residueField u))
    ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
    ((pullback.snd f (h ≫ g)).fiberToSpecResidueField u)
    (𝟙 (f.fiber (g (h u)))) (compBaseChangeFiberIso f g h u).hom
    (compBaseChangeFiberIso_hom_snd f g h u) (compFiberMapOfBaseChange f g h u)
    (restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
      pullback.condition u)
    ((Category.comp_id _).trans (compBaseChangeFiberIso_hom_fst f g h u).symm) (r : ℤ) x
  calc (baseChangeFamily (pullback.snd f g) h r (baseChangeFamily f g r α) u :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) h).fiber u) ℤ) x
      = (α (g (h u)) : AlgebraicCycle (f.fiber (g (h u))) ℤ)
            (compFiberMapOfBaseChange f g h u x) *
          flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
            ((pullback.snd (pullback.snd f g) h).fiberToSpecResidueField u)
            (compFiberMapOfBaseChange f g h u) (r : ℤ) x :=
        baseChangeFamily_apply_comp f g h r u α x
    _ = (α (g (h u)) : AlgebraicCycle (f.fiber (g (h u))) ℤ)
            (restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
              pullback.condition u ((compBaseChangeFiberIso f g h u).hom x)) *
          flatPullbackWeight (fieldChowSituation ↥(S''.residueField u))
            ((pullback.snd f (h ≫ g)).fiberToSpecResidueField u)
            (restrictedFiberMap f (pullback.snd f (h ≫ g)) (pullback.fst f (h ≫ g)) (h ≫ g)
              pullback.condition u) (r : ℤ) ((compBaseChangeFiberIso f g h u).hom x) := by
        rw [hw, hpt]
        rfl
    _ = (baseChangeFamily f (h ≫ g) r α u :
          AlgebraicCycle ((pullback.snd f (h ≫ g)).fiber u) ℤ)
        ((compBaseChangeFiberIso f g h u).hom x) :=
      (baseChangeFamily_apply f (h ≫ g) r α u _).symm

end Comp

section CongrMorphism

variable (f : X ⟶ S) [LocallyOfFiniteType f]

/-- Two equal morphisms of bases give the same base change, and in particular isomorphic fibres
over a point of the new base. -/
def baseChangeFiberCongr {k₁ k₂ : S'' ⟶ S} (e : k₁ = k₂) (u : S'') :
    (pullback.snd f k₁).fiber u ≅ (pullback.snd f k₂).fiber u :=
  have hbase : pullback.snd f k₁ ≫ 𝟙 S'' =
      (pullback.congrHom (show f = f from rfl) e).hom ≫ pullback.snd f k₂ := by
    simp only [Category.comp_id, pullback.congrHom_hom, pullback.map, pullback.lift_snd]
  have hfib : S''.fromSpecResidueField u ≫ 𝟙 S'' =
      𝟙 (Spec (S''.residueField u)) ≫ S''.fromSpecResidueField u := by simp
  (asIso (pullback.map (pullback.snd f k₁) (S''.fromSpecResidueField u)
      (pullback.snd f k₂) (S''.fromSpecResidueField u)
      (pullback.congrHom (show f = f from rfl) e).hom (𝟙 _) (𝟙 _) hbase hfib) :
    pullback (pullback.snd f k₁) (S''.fromSpecResidueField u) ≅
      pullback (pullback.snd f k₂) (S''.fromSpecResidueField u))

omit [LocallyOfFiniteType f] in
/-- `Stacks.Chow.baseChangeFiberCongr` is induced by the identification of the total spaces. -/
@[reassoc] theorem baseChangeFiberCongr_hom_fiberι {k₁ k₂ : S'' ⟶ S} (e : k₁ = k₂) (u : S'') :
    (baseChangeFiberCongr f e u).hom ≫ (pullback.snd f k₂).fiberι u =
      (pullback.snd f k₁).fiberι u ≫ (pullback.congrHom (show f = f from rfl) e).hom := by
  simp only [baseChangeFiberCongr, asIso_hom, Scheme.Hom.fiberι, Scheme.Hom.fiber,
    pullback.map, pullback.lift_fst]

omit [LocallyOfFiniteType f] in
/-- `Stacks.Chow.baseChangeFiberCongr` is an isomorphism over `Spec κ(u)`. -/
@[reassoc] theorem baseChangeFiberCongr_hom_snd {k₁ k₂ : S'' ⟶ S} (e : k₁ = k₂) (u : S'') :
    (baseChangeFiberCongr f e u).hom ≫ (pullback.snd f k₂).fiberToSpecResidueField u =
      (pullback.snd f k₁).fiberToSpecResidueField u := by
  simp only [baseChangeFiberCongr, asIso_hom, Scheme.Hom.fiberToSpecResidueField,
    Scheme.Hom.fiber, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Base change along equal morphisms of bases gives families with the same coefficients. -/
theorem baseChangeFamily_apply_baseChangeFiberCongr {k₁ k₂ : S'' ⟶ S} (e : k₁ = k₂) (r : ℕ)
    (α : FamilyOfCycles f r) (u : S'') (x : (pullback.snd f k₁).fiber u) :
    (baseChangeFamily f k₁ r α u : AlgebraicCycle ((pullback.snd f k₁).fiber u) ℤ) x =
      (baseChangeFamily f k₂ r α u : AlgebraicCycle ((pullback.snd f k₂).fiber u) ℤ)
        ((baseChangeFiberCongr f e u).hom x) := by
  subst e
  have he : (baseChangeFiberCongr f (k₁ := k₁) rfl u).hom = 𝟙 _ := by
    simp [baseChangeFiberCongr, pullback.congrHom, pullback.map, Scheme.Hom.fiber]
  rw [he]
  rfl

end CongrMorphism

section Overlap

variable (f : X ⟶ S) (g : S' ⟶ S)

/-- The canonical isomorphism `(X ×_S S') ×_{S', pr₁} S'' ≅ (X ×_S S') ×_{S', pr₂} S''` over
`S'' = S' ×_S S'`, where `pr₁, pr₂ : S'' ⟶ S'` are the two projections. Both sides are the total
space `(S' ×_S S') ×_S X` of the source; the isomorphism is the composite of the two pasting
isomorphisms with the identification coming from `pr₁ ≫ g = pr₂ ≫ g`. -/
def overlapComparison :
    pullback (pullback.snd f g) (pullback.fst g g) ≅
      pullback (pullback.snd f g) (pullback.snd g g) :=
  pullbackLeftPullbackSndIso f g (pullback.fst g g) ≪≫
    pullback.congrHom rfl pullback.condition ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.snd g g)).symm

/-- The comparison isomorphism of the two iterated base changes lies over `S'' = S' ×_S S'`. -/
@[simp] theorem overlapComparison_hom_snd :
    (overlapComparison f g).hom ≫ pullback.snd (pullback.snd f g) (pullback.snd g g) =
      pullback.snd (pullback.snd f g) (pullback.fst g g) := by
  rw [overlapComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- The comparison isomorphism of the two iterated base changes lies over `X`. -/
theorem overlapComparison_hom_fst_fst :
    (overlapComparison f g).hom ≫ pullback.fst (pullback.snd f g) (pullback.snd g g) ≫
        pullback.fst f g =
      pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g := by
  simp only [overlapComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- The isomorphism induced by `Stacks.Chow.overlapComparison` on the scheme-theoretic fibres
over a point `t` of `S'' = S' ×_S S'`. It identifies the cycles on the fibre of
`(X ×_S S') ×_{S', pr₁} S''` over `t` with the cycles on the fibre of
`(X ×_S S') ×_{S', pr₂} S''` over `t`, and so lets the two pullbacks `pr₁^*α'` and `pr₂^*α'` be
compared. -/
def overlapFiberComparison (t : (pullback g g : Scheme.{u})) :
    (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t ≅
      (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t :=
  have hbase : pullback.snd (pullback.snd f g) (pullback.fst g g) ≫ 𝟙 (pullback g g) =
      (overlapComparison f g).hom ≫ pullback.snd (pullback.snd f g) (pullback.snd g g) := by
    simp
  have hfib : (pullback g g).fromSpecResidueField t ≫ 𝟙 (pullback g g) =
      𝟙 (Spec ((pullback g g).residueField t)) ≫ (pullback g g).fromSpecResidueField t := by
    simp
  (asIso (pullback.map (pullback.snd (pullback.snd f g) (pullback.fst g g))
      ((pullback g g).fromSpecResidueField t)
      (pullback.snd (pullback.snd f g) (pullback.snd g g))
      ((pullback g g).fromSpecResidueField t)
      (overlapComparison f g).hom (𝟙 _) (𝟙 _) hbase hfib) :
    pullback (pullback.snd (pullback.snd f g) (pullback.fst g g))
        ((pullback g g).fromSpecResidueField t) ≅
      pullback (pullback.snd (pullback.snd f g) (pullback.snd g g))
        ((pullback g g).fromSpecResidueField t))

/-- `Stacks.Chow.overlapFiberComparison` is induced by `Stacks.Chow.overlapComparison`. -/
@[reassoc] theorem overlapFiberComparison_hom_fiberι (t : (pullback g g : Scheme.{u})) :
    (overlapFiberComparison f g t).hom ≫
        (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberι t =
      (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiberι t ≫
        (overlapComparison f g).hom := by
  simp only [overlapFiberComparison, asIso_hom, Scheme.Hom.fiberι, Scheme.Hom.fiber,
    pullback.map, pullback.lift_fst]

/-- `Stacks.Chow.overlapFiberComparison` is an isomorphism over `Spec κ(t)`. -/
@[reassoc] theorem overlapFiberComparison_hom_snd (t : (pullback g g : Scheme.{u})) :
    (overlapFiberComparison f g t).hom ≫
        (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberToSpecResidueField t =
      (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiberToSpecResidueField t := by
  simp only [overlapFiberComparison, asIso_hom, Scheme.Hom.fiberToSpecResidueField,
    Scheme.Hom.fiber, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The first projection of the overlap, read through `Stacks.Chow.overlapComparison`, exhibits
the first iterated base change as the base change of `X ×_S S'` along `pr₂`. -/
theorem overlap_isPullback_snd :
    IsPullback
      ((overlapComparison f g).hom ≫ pullback.fst (pullback.snd f g) (pullback.snd g g))
      (pullback.snd (pullback.snd f g) (pullback.fst g g))
      (pullback.snd f g) (pullback.snd g g) :=
  IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, overlapComparison_hom_snd]⟩
    (overlapComparison f g) rfl (overlapComparison_hom_snd f g)

/-- The two projections of the overlap to `X ×_S S'`, read through
`Stacks.Chow.overlapComparison`, exhibit the first iterated base change as `X' ×_X X'`. -/
theorem overlap_isPullback_fst :
    IsPullback (pullback.fst (pullback.snd f g) (pullback.fst g g))
      ((overlapComparison f g).hom ≫ pullback.fst (pullback.snd f g) (pullback.snd g g))
      (pullback.fst f g) (pullback.fst f g) := by
  apply IsPullback.of_bot (v₁₁ := (overlapComparison f g).hom ≫
    pullback.fst (pullback.snd f g) (pullback.snd g g))
    (v₁₂ := pullback.fst f g) (v₂₂ := f) ?_
    (by simpa only [Category.assoc] using (overlapComparison_hom_fst_fst f g).symm)
    (IsPullback.of_hasPullback f g)
  convert (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g g)).paste_vert
    (IsPullback.of_hasPullback g g) using 1
  · exact (overlap_isPullback_snd f g).w
  · exact pullback.condition

/-- `Stacks.Chow.overlapComparison` preserves the residue transcendence degree over `X`. -/
theorem residueTrdeg_overlap
    (z : (pullback (pullback.snd f g) (pullback.fst g g) : Scheme.{u})) :
    residueTrdeg (pullback.snd (pullback.snd f g) (pullback.snd g g))
        ((overlapComparison f g).hom z) =
      residueTrdeg (pullback.snd (pullback.snd f g) (pullback.fst g g)) z := by
  have h := residueTrdeg_comp (overlapComparison f g).hom
    (pullback.snd (pullback.snd f g) (pullback.snd g g)) z
  rw [residueTrdeg_eq_zero_of_isPreimmersion (overlapComparison f g).hom, add_zero,
    overlapComparison_hom_snd] at h
  exact h.symm

/-- The composite of the two canonical comparisons with the identification coming from
`pr₁ ≫ g = pr₂ ≫ g` is `Stacks.Chow.overlapFiberComparison`. -/
theorem overlapFiberComparison_hom_compBaseChangeFiberIso [LocallyOfFiniteType f]
    (t : (pullback g g : Scheme.{u})) :
    (compBaseChangeFiberIso f g (pullback.fst g g) t).hom ≫
        (baseChangeFiberCongr f (pullback.condition (f := g) (g := g)) t).hom =
      (overlapFiberComparison f g t).hom ≫
        (compBaseChangeFiberIso f g (pullback.snd g g) t).hom := by
  have hfib : IsPullback ((pullback.snd f (pullback.snd g g ≫ g)).fiberι t)
      ((pullback.snd f (pullback.snd g g ≫ g)).fiberToSpecResidueField t)
      (pullback.snd f (pullback.snd g g ≫ g))
      ((pullback g g).fromSpecResidueField t) := IsPullback.of_hasPullback _ _
  refine hfib.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeFiberCongr_hom_fiberι, ← Category.assoc,
      compBaseChangeFiberIso_hom_fiberι, Category.assoc, Category.assoc,
      compBaseChangeFiberIso_hom_fiberι, overlapFiberComparison_hom_fiberι_assoc]
    congr 1
    simp only [overlapComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, baseChangeFiberCongr_hom_snd, compBaseChangeFiberIso_hom_snd,
      Category.assoc, compBaseChangeFiberIso_hom_snd, overlapFiberComparison_hom_snd]

/-- **A step in the proof of Stacks Project, Tag 0H4X (2).** The two pullbacks of a base-changed
family `g^*α` to the double overlap `S'' = S' ×_S S'` agree: `pr₁^*g^*α = pr₂^*g^*α`, compared
through the canonical isomorphism `Stacks.Chow.overlapFiberComparison` of the fibres. This is
the associativity of base change, which the source invokes to see that the family it descends
satisfies the hypothesis of part (2). -/
theorem baseChangeFamily_apply_overlapFiberComparison [LocallyOfFiniteType f] (r : ℕ)
    (t : (pullback g g : Scheme.{u})) (α : FamilyOfCycles f r)
    (x : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) :
    (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r (baseChangeFamily f g r α) t :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) x =
      (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r (baseChangeFamily f g r α) t :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
        ((overlapFiberComparison f g t).hom x) := by
  rw [baseChangeFamily_apply_compBaseChangeFiberIso f g (pullback.fst g g) r t α x,
    baseChangeFamily_apply_baseChangeFiberCongr f (pullback.condition (f := g) (g := g)) r α t,
    baseChangeFamily_apply_compBaseChangeFiberIso f g (pullback.snd g g) r t α
      ((overlapFiberComparison f g t).hom x)]
  congr 1
  exact congrArg (fun m : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t ⟶
    (pullback.snd f (pullback.snd g g ≫ g)).fiber t ↦ m x)
    (overlapFiberComparison_hom_compBaseChangeFiberIso f g t)

end Overlap

end Stacks.Chow

end
