module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeCompositeResidueIso
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of families of cycles on fibres commutes with proper push-pull

Let `S` be a scheme and let

```
X' --f--> X
|         |
v         v
Y' --g--> Y
```

be a cartesian square of schemes locally of finite type over `S` with `g` proper, realized by
the fibre product `X' = X ×_Y Y'`. Let `α` be a family of `r`-cycles on the fibres of `X/Y` and
let `β'` be a family of `e`-cycles on the fibres of `Y'/S`. This file proves

`f_*(g^*α ∘ β') = α ∘ g_*β'`

as families of `(r + e)`-cycles on the fibres of `X/S`, where `∘` is the composition
`Stacks.Chow.compFamily`, `g^*` is `Stacks.Chow.baseChangeFamily` and `f_*`, `g_*` are
`Stacks.Chow.properPushforwardFamily`.

## Main results

* `Stacks.Chow.properPushforwardFamily_compFamily_baseChangeFamily` — the asserted equality.

## Implementation notes

Unwinding the definitions, this is the projection formula
`Stacks.Chow.properPushforward_cap_baseChangeFamily` (Tag 0H6B) applied on each fibre. Over a
point `s` of `S` the composition `α ∘ β` is, by construction, the action
`(Y_s → Y)^*α ∩ β_s` read on `X_s` through the canonical isomorphism `X ×_Y Y_s ≅ X_s`; so the
right hand side over `s` is the right hand side of Tag 0H6B for the square

```
(X ×_Y Y_s) ×_{Y_s} Y'_s --> X ×_Y Y_s
          |                      |
          v                      v
        Y'_s        --g_s-->    Y_s
```

over the Chow situation of `κ(s)`, with `g_s` the morphism induced on fibres — proper, being a
base change of `g`.

Two comparisons turn its left hand side into the left hand side over `s`. The schemes
`X' ×_{Y'} Y'_s` and `(X ×_Y Y_s) ×_{Y_s} Y'_s` are canonically isomorphic, both being
`X ×_Y Y'_s`, and `Stacks.Chow.properPushforward_congr_iso` moves proper pushforward across that
isomorphism; what it needs is that the coefficients correspond, which is the base change of `α`
being computed along either of the two routes from `Y'_s` to `Y`. Those two routes are the two
orientations of base change along a composite: along `Y'_s → Y' → Y` the near morphism
`Y'_s → Y'` is a fibre inclusion, so
`Stacks.Chow.baseChangeFamily_baseChangeFamily_of_residueIso` applies, while along
`Y'_s → Y_s → Y` the far morphism `Y_s → Y` is the fibre inclusion and
`Stacks.Chow.baseChangeFamily_baseChangeFamily` applies.

## References

* [Stacks Project, Tag 0H6N](https://stacks.math.columbia.edu/tag/0H6N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Moving proper pushforward across isomorphisms -/

/-- The coefficient of the proper pushforward of a cycle along an isomorphism over the base,
read at a point of the target. -/
theorem properPushforward_apply_of_isIso_inv (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (i : A ≅ B)
    (hi : i.hom ≫ sB = sA) (k : ℤ) (c : CycleGroup C sA k) (b : B) :
    (properPushforward C sA sB i.hom hi k c).1 b = c.1 (i.inv b) := by
  have h := properPushforward_apply_of_isIso C sA sB i.hom hi k c (i.inv b)
  rwa [Scheme.inv_hom_apply] at h

/-- Proper pushforward of the underlying cycles is functorial. -/
theorem properPushforward_val_comp (C : ChowSituation.{u}) {A B D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (a : A ⟶ B) [IsProper a] (b : B ⟶ D) [IsProper b]
    (ha : a ≫ sB = sA) (hb : b ≫ sD = sB) (k : ℤ) (c : CycleGroup C sA k) :
    AlgebraicCycle.map b (relativeDimension C.dimensionFunction sB)
        (relativeDimension C.dimensionFunction sD)
        (AlgebraicCycle.map a (relativeDimension C.dimensionFunction sA)
          (relativeDimension C.dimensionFunction sB) c.1) =
      AlgebraicCycle.map (a ≫ b) (relativeDimension C.dimensionFunction sA)
        (relativeDimension C.dimensionFunction sD) c.1 :=
  congrArg Subtype.val (congrFun (properPushforward_comp C sA sB sD a b ha hb k) c)

/-- **Proper pushforward across a relabelling of a square by isomorphisms.** Given two proper
morphisms over the base identified by isomorphisms `i` and `j` of their sources and targets, and
cycles on the two sources whose coefficients correspond under `i`, the coefficients of the two
pushforwards correspond under `j`.

The two cycles may carry different delta-dimensions: pushforward does not mix them, so no
transport of the grading is needed. -/
theorem properPushforward_congr_iso (C : ChowSituation.{u}) {A B A' B' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (a : A ⟶ B) [IsProper a] (a' : A' ⟶ B') [IsProper a'] (ha : a ≫ sB = sA)
    (ha' : a' ≫ sB' = sA') (i : A ≅ A') (j : B ≅ B') (hi : i.hom ≫ sA' = sA)
    (hj : j.hom ≫ sB' = sB) (hij : a ≫ j.hom = i.hom ≫ a') (k k' : ℤ)
    (c : CycleGroup C sA k) (c' : CycleGroup C sA' k') (hc : ∀ x, c.1 x = c'.1 (i.hom x))
    (y : B) :
    (properPushforward C sA sB a ha k c).1 y =
      (properPushforward C sA' sB' a' ha' k' c').1 (j.hom y) := by
  have hci : (properPushforward C sA sA' i.hom hi k c).1 = c'.1 := by
    ext x
    rw [properPushforward_apply_of_isIso_inv, hc]
    simp [← Scheme.Hom.comp_apply]
  have hmap : (properPushforward C sB sB' j.hom hj k
        (properPushforward C sA sB a ha k c)).1 =
      (properPushforward C sA' sB' a' ha' k' c').1 := by
    change AlgebraicCycle.map j.hom _ _ (AlgebraicCycle.map a _ _ c.1) = _
    rw [properPushforward_val_comp C sA sB sB' a j.hom ha hj k c]
    simp only [hij]
    rw [← properPushforward_val_comp C sA sA' sB' i.hom a' hi ha' k c]
    change AlgebraicCycle.map a' _ _ (properPushforward C sA sA' i.hom hi k c).1 = _
    rw [hci]
    rfl
  have heval := congrArg (fun z : AlgebraicCycle B' ℤ => z (j.hom y)) hmap
  rwa [properPushforward_apply_of_isIso_inv, Scheme.hom_inv_apply] at heval

/-! ### The action against a reindexed family -/

/-- The coefficients of the action are unchanged by relabelling the source along a morphism over
the base, provided the two families of fibre cycles correspond under the induced maps of
fibres. -/
theorem capCoeff_congr_fiberRestrict {X Y U : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (fU : U ⟶ Y) [LocallyOfFiniteType fU] (i : U ⟶ X) (hi : i ≫ f = fU) {r : ℕ}
    (α : FamilyOfCycles f r) (α' : FamilyOfCycles fU r)
    (hα : ∀ (y : Y) (ξ : fU.fiber y), (α' y).1 ξ = (α y).1 (fiberRestrict f fU i hi y ξ))
    (β : AlgebraicCycle Y ℤ) (x : U) :
    capCoeff fU α' β x = capCoeff f α β (i x) := by
  have hbase : f (i x) = fU x := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : U ⟶ Y => m x) hi
  have hpt : f.fiberι (fU x) (fiberRestrict f fU i hi (fU x) (fU.asFiber x)) = i x := by
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using
      congrArg (fun m : fU.fiber (fU x) ⟶ X => m (fU.asFiber x))
        (fiberRestrict_fiberι f fU i hi (fU x))
  unfold capCoeff
  rw [hα, familyOfCycles_apply_of_fiberι f α (fU x) _ (i x) hpt]
  exact congrArg (fun z : Y ↦ β z *
    (α (f (i x)) : AlgebraicCycle (f.fiber (f (i x))) ℤ) (f.asFiber (i x))) hbase.symm

/-- The action of a twice-base-changed family on a cycle has the coefficients of the action of
the family base changed along the composite, read through the comparison isomorphism
`(X ×_S S') ×_{S'} T ≅ X ×_S T`, given the identification `hcomp` of the two base changes. -/
theorem capCoeff_baseChangeFamily_comp {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (g' : T' ⟶ T) (r : ℕ) (α : FamilyOfCycles f r)
    (hcomp : ∀ t : T', baseChangeFamily (pullback.snd f g) g' r (baseChangeFamily f g r α) t =
      fiberCycleRestrict (pullback.snd f (g' ≫ g)) (pullback.snd (pullback.snd f g) g')
        (pullbackLeftPullbackSndIso f g g').hom
        (pullbackLeftPullbackSndIso_hom_snd f g g') t r (baseChangeFamily f (g' ≫ g) r α t))
    (β : AlgebraicCycle T' ℤ) (x : ↥(pullback (pullback.snd f g) g' : Scheme.{u})) :
    capCoeff (pullback.snd (pullback.snd f g) g')
        (baseChangeFamily (pullback.snd f g) g' r (baseChangeFamily f g r α)) β x =
      capCoeff (pullback.snd f (g' ≫ g)) (baseChangeFamily f (g' ≫ g) r α) β
        ((pullbackLeftPullbackSndIso f g g').hom x) :=
  capCoeff_congr_fiberRestrict (pullback.snd f (g' ≫ g))
    (pullback.snd (pullback.snd f g) g') (pullbackLeftPullbackSndIso f g g').hom
    (pullbackLeftPullbackSndIso_hom_snd f g g') (baseChangeFamily f (g' ≫ g) r α)
    (baseChangeFamily (pullback.snd f g) g' r (baseChangeFamily f g r α))
    (fun t ξ ↦ by rw [hcomp t, fiberCycleRestrict_apply]) β x

/-- The action of a base-changed family is unchanged by replacing the morphism along which the
base change is taken by an equal one. -/
theorem capCoeff_baseChangeFamily_congr {X S T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g g' : T ⟶ S) (h : g = g') (r : ℕ) (α : FamilyOfCycles f r)
    (β : AlgebraicCycle T ℤ) (x : ↥(pullback f g : Scheme.{u})) :
    capCoeff (pullback.snd f g) (baseChangeFamily f g r α) β x =
      capCoeff (pullback.snd f g') (baseChangeFamily f g' r α) β
        ((pullback.congrHom (rfl : f = f) h).hom x) := by
  subst h
  simp

/-! ### The composition read as an action on a fibre -/

/-- The coefficient of the composition `α ∘ β` over `s` is the coefficient of the action
`(Y_s → Y)^*α ∩ β_s`, taken over the Chow situation of `κ(s)`, at the corresponding point of
`X ×_Y Y_s`, with the base change written as `Stacks.Chow.baseChangeFamily`. -/
theorem compFamily_apply_cap {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r)
    (β : FamilyOfCycles g e) (s : S) (x : (f ≫ g).fiber s) :
    letI : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField s)))
    (compFamily f g r e α β s : AlgebraicCycle ((f ≫ g).fiber s) ℤ) x =
      (cap (fieldChowSituation (S.residueField s)) (g.fiberToSpecResidueField s)
          (pullback.snd f (g.fiberι s)) (baseChangeFamily f (g.fiberι s) r α) (β s)).1
        ((compFiberIso f g s).inv x) := by
  let : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField s)))
  rw [baseChangeFamily_eq_baseChangeFamilyOfResidueIso f (g.fiberι s)
    (fun t ↦ isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) r α]
  rfl

/-! ### The comparison isomorphism of the two fibre squares -/

/-- The comparison isomorphism of two fibre products with the same first leg and equal second
legs is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackCongrHom_hom_fst {D : Type*} [Category D] {A B Z : D} {f : A ⟶ Z}
    {g₁ g₂ : B ⟶ Z} (h : g₁ = g₂) [HasPullback f g₁] [HasPullback f g₂] :
    (pullback.congrHom (rfl : f = f) h).hom ≫ pullback.fst f g₂ = pullback.fst f g₁ := by
  subst h
  simp

/-- The comparison isomorphism of two fibre products with the same first leg and equal second
legs is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem pullbackCongrHom_hom_snd {D : Type*} [Category D] {A B Z : D} {f : A ⟶ Z}
    {g₁ g₂ : B ⟶ Z} (h : g₁ = g₂) [HasPullback f g₁] [HasPullback f g₂] :
    (pullback.congrHom (rfl : f = f) h).hom ≫ pullback.snd f g₂ = pullback.snd f g₁ := by
  subst h
  simp

section FibreSquare

variable {X Y Y' S : Scheme.{u}} (sY : Y ⟶ S) [LocallyOfFiniteType sY] (sY' : Y' ⟶ S)
  [LocallyOfFiniteType sY'] (p : X ⟶ Y) [LocallyOfFiniteType p] (g : Y' ⟶ Y)
  (hg : g ≫ sY = sY') (s : S)

/-- The canonical isomorphism `X' ×_{Y'} Y'_s ≅ (X ×_Y Y_s) ×_{Y_s} Y'_s` for `X' = X ×_Y Y'`,
both sides being `X ×_Y Y'_s`. -/
def fibreSquareIso : pullback (pullback.snd p g) (sY'.fiberι s) ≅
    pullback (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) :=
  pullbackLeftPullbackSndIso p g (sY'.fiberι s) ≪≫
    pullback.congrHom (rfl : p = p) (inducedFiberMap_fiberι sY' sY g hg s).symm ≪≫
      (pullbackLeftPullbackSndIso p (sY.fiberι s) (inducedFiberMap sY' sY g hg s)).symm

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [LocallyOfFiniteType p] in
/-- The comparison isomorphism is compatible with the projections to `Y'_s`. -/
@[reassoc (attr := simp)]
theorem fibreSquareIso_hom_snd :
    (fibreSquareIso sY sY' p g hg s).hom ≫
        pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) =
      pullback.snd (pullback.snd p g) (sY'.fiberι s) := by
  simp [fibreSquareIso, -pullback.congrHom_hom]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [LocallyOfFiniteType p] in
/-- The comparison isomorphism is compatible with the projections to `X`. -/
@[reassoc]
theorem fibreSquareIso_hom_fst_fst :
    (fibreSquareIso sY sY' p g hg s).hom ≫
        pullback.fst (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
          pullback.fst p (sY.fiberι s) =
      pullback.fst (pullback.snd p g) (sY'.fiberι s) ≫ pullback.fst p g := by
  simp [fibreSquareIso, -pullback.congrHom_hom]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [LocallyOfFiniteType p] in
/-- The comparison isomorphism is, by construction, the comparison of the two presentations of
`X ×_Y Y'_s` as an iterated fibre product. -/
@[reassoc]
theorem fibreSquareIso_hom_comp_pullbackLeftPullbackSndIso :
    (fibreSquareIso sY sY' p g hg s).hom ≫
        (pullbackLeftPullbackSndIso p (sY.fiberι s) (inducedFiberMap sY' sY g hg s)).hom =
      (pullbackLeftPullbackSndIso p g (sY'.fiberι s)).hom ≫
        (pullback.congrHom (rfl : p = p) (inducedFiberMap_fiberι sY' sY g hg s).symm).hom := by
  simp [fibreSquareIso, pullback.map]

end FibreSquare

/-! ### The projection formula for the composition -/

/-- **Stacks Project, Tag 0H6N.** Let `S` be a scheme, let
```
X' --f--> X
|         |
v         v
Y' --g--> Y
```
be a cartesian square of schemes locally of finite type over `S` with `g` proper, realized by
the fibre product `X' = X ×_Y Y'` with `f = pullback.fst`, let `r, e ≥ 0`, let `α` be a family
of `r`-cycles on the fibres of `X/Y` and let `β'` be a family of `e`-cycles on the fibres of
`Y'/S`. Then

`f_*(g^*α ∘ β') = α ∘ g_*β'`

as families of `(r + e)`-cycles on the fibres of `X/S`, where `∘` is the composition
`Stacks.Chow.compFamily`, `g^*` is `Stacks.Chow.baseChangeFamily` and `f_*`, `g_*` are
`Stacks.Chow.properPushforwardFamily`. -/
@[stacks 0H6N]
theorem properPushforwardFamily_compFamily_baseChangeFamily {X Y Y' S : Scheme.{u}}
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] (sY' : Y' ⟶ S) [LocallyOfFiniteType sY']
    (p : X ⟶ Y) [LocallyOfFiniteType p] (g : Y' ⟶ Y) [IsProper g] (hg : g ≫ sY = sY')
    (r e : ℕ) (α : FamilyOfCycles p r) (β' : FamilyOfCycles sY' e) :
    properPushforwardFamily (pullback.snd p g ≫ sY') (p ≫ sY) (pullback.fst p g)
        (pullbackFst_comp_eq_of_base g rfl hg) (r + e)
        (compFamily (pullback.snd p g) sY' r e (baseChangeFamily p g r α) β') =
      compFamily p sY r e α (properPushforwardFamily sY' sY g hg e β') := by
  funext s
  apply Subtype.ext
  ext x
  let : LocallyOfFiniteType (sY.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd sY (S.fromSpecResidueField s)))
  let : LocallyOfFiniteType (sY'.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd sY' (S.fromSpecResidueField s)))
  let : LocallyOfFiniteType ((p ≫ sY).fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (p ≫ sY) (S.fromSpecResidueField s)))
  let : LocallyOfFiniteType ((pullback.snd p g ≫ sY').fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (pullback.snd p g ≫ sY') (S.fromSpecResidueField s)))
  let : LocallyOfFiniteType (pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s) :=
    inferInstance
  have hgf : inducedFiberMap sY' sY g hg s ≫ sY.fiberToSpecResidueField s =
      sY'.fiberToSpecResidueField s :=
    inducedFiberMap_fiberToSpecResidueField sY' sY g hg s
  have hqout : inducedFiberMap (pullback.snd p g ≫ sY') (p ≫ sY) (pullback.fst p g)
        (pullbackFst_comp_eq_of_base g rfl hg) s ≫ (p ≫ sY).fiberToSpecResidueField s =
      (pullback.snd p g ≫ sY').fiberToSpecResidueField s :=
    inducedFiberMap_fiberToSpecResidueField (pullback.snd p g ≫ sY') (p ≫ sY)
      (pullback.fst p g) (pullbackFst_comp_eq_of_base g rfl hg) s
  have hf0fst : (compFiberIso p sY s).hom ≫ (p ≫ sY).fiberι s = pullback.fst p (sY.fiberι s) :=
    pullbackRightPullbackFstIso_hom_fst sY (S.fromSpecResidueField s) p
  have hf0 : (compFiberIso p sY s).hom ≫ (p ≫ sY).fiberToSpecResidueField s =
      pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s :=
    pullbackRightPullbackFstIso_hom_snd sY (S.fromSpecResidueField s) p
  have hfcfst : (compFiberIso (pullback.snd p g) sY' s).hom ≫
      (pullback.snd p g ≫ sY').fiberι s = pullback.fst (pullback.snd p g) (sY'.fiberι s) :=
    pullbackRightPullbackFstIso_hom_fst sY' (S.fromSpecResidueField s) (pullback.snd p g)
  have hfc : (compFiberIso (pullback.snd p g) sY' s).hom ≫
        (pullback.snd p g ≫ sY').fiberToSpecResidueField s =
      pullback.snd (pullback.snd p g) (sY'.fiberι s) ≫ sY'.fiberToSpecResidueField s :=
    pullbackRightPullbackFstIso_hom_snd sY' (S.fromSpecResidueField s) (pullback.snd p g)
  have hmap : (compFiberIso (pullback.snd p g) sY' s).hom ≫
        inducedFiberMap (pullback.snd p g ≫ sY') (p ≫ sY) (pullback.fst p g)
          (pullbackFst_comp_eq_of_base g rfl hg) s =
      (fibreSquareIso sY sY' p g hg s).hom ≫
        pullback.fst (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
          (compFiberIso p sY s).hom := by
    refine pullback.hom_ext (?_ : _ ≫ (p ≫ sY).fiberι s = _ ≫ (p ≫ sY).fiberι s)
        (?_ : _ ≫ (p ≫ sY).fiberToSpecResidueField s = _ ≫ (p ≫ sY).fiberToSpecResidueField s)
    · simp only [Category.assoc]
      rw [inducedFiberMap_fiberι, ← Category.assoc, hfcfst, hf0fst]
      exact (fibreSquareIso_hom_fst_fst sY sY' p g hg s).symm
    · simp only [Category.assoc]
      rw [hqout, hfc, hf0,
        show pullback.fst (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
            pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s =
          pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
            inducedFiberMap sY' sY g hg s ≫ sY.fiberToSpecResidueField s from by
            rw [← Category.assoc, pullback.condition, Category.assoc],
        hgf, ← Category.assoc, fibreSquareIso_hom_snd]
  have hi : ((compFiberIso (pullback.snd p g) sY' s).symm ≪≫ fibreSquareIso sY sY' p g hg s).hom ≫
        (pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
          sY'.fiberToSpecResidueField s) =
      (pullback.snd p g ≫ sY').fiberToSpecResidueField s := by
    change (compFiberIso (pullback.snd p g) sY' s).inv ≫ (fibreSquareIso sY sY' p g hg s).hom ≫
      pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
        sY'.fiberToSpecResidueField s = _
    rw [← Category.assoc (fibreSquareIso sY sY' p g hg s).hom, fibreSquareIso_hom_snd]
    exact (Iso.inv_comp_eq _).2 hfc.symm
  have ht : (compFiberIso p sY s).symm.hom ≫
        (pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s) =
      (p ≫ sY).fiberToSpecResidueField s := by
    exact (Iso.inv_comp_eq _).2 hf0.symm
  have hsq : inducedFiberMap (pullback.snd p g ≫ sY') (p ≫ sY) (pullback.fst p g)
          (pullbackFst_comp_eq_of_base g rfl hg) s ≫ (compFiberIso p sY s).symm.hom =
      ((compFiberIso (pullback.snd p g) sY' s).symm ≪≫ fibreSquareIso sY sY' p g hg s).hom ≫
        pullback.fst (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.trans_hom, Iso.symm_hom] using congrArg (fun q ↦
        (compFiberIso (pullback.snd p g) sY' s).inv ≫ q ≫ (compFiberIso p sY s).inv) hmap
  have hsource : ∀ z : (pullback.snd p g ≫ sY').fiber s,
      (compFamily (pullback.snd p g) sY' r e (baseChangeFamily p g r α) β' s).1 z =
        (cap (fieldChowSituation (S.residueField s)) (sY'.fiberToSpecResidueField s)
          (pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s))
          (baseChangeFamily (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) r
            (baseChangeFamily p (sY.fiberι s) r α)) (β' s)).1
          (((compFiberIso (pullback.snd p g) sY' s).symm ≪≫
            fibreSquareIso sY sY' p g hg s).hom z) := by
    intro z
    rw [compFamily_apply_cap (pullback.snd p g) sY' r e (baseChangeFamily p g r α) β' s z,
      cap_apply, cap_apply,
      capCoeff_baseChangeFamily_comp p g (sY'.fiberι s) r α
        (baseChangeFamily_baseChangeFamily_of_residueIso p g (sY'.fiberι s)
          (fun w ↦ isIso_residueFieldMap_of_isPreimmersion (sY'.fiberι s) w) r α) (β' s).1
        ((compFiberIso (pullback.snd p g) sY' s).inv z),
      capCoeff_baseChangeFamily_comp p (sY.fiberι s) (inducedFiberMap sY' sY g hg s) r α
        (baseChangeFamily_baseChangeFamily p (sY.fiberι s) (inducedFiberMap sY' sY g hg s)
          (fun w ↦ isIso_residueFieldMap_of_isPreimmersion (sY.fiberι s) w) r α) (β' s).1
        (((compFiberIso (pullback.snd p g) sY' s).symm ≪≫ fibreSquareIso sY sY' p g hg s).hom z),
      capCoeff_baseChangeFamily_congr p (sY'.fiberι s ≫ g)
        (inducedFiberMap sY' sY g hg s ≫ sY.fiberι s)
        (inducedFiberMap_fiberι sY' sY g hg s).symm r α (β' s).1
        ((pullbackLeftPullbackSndIso p g (sY'.fiberι s)).hom
          ((compFiberIso (pullback.snd p g) sY' s).inv z))]
    refine congrArg (capCoeff
      (pullback.snd p (inducedFiberMap sY' sY g hg s ≫ sY.fiberι s))
      (baseChangeFamily p (inducedFiberMap sY' sY g hg s ≫ sY.fiberι s) r α) (β' s).1) ?_
    have h := congrArg (fun m : pullback (pullback.snd p g) (sY'.fiberι s) ⟶
        pullback p (inducedFiberMap sY' sY g hg s ≫ sY.fiberι s) ↦
      m ((compFiberIso (pullback.snd p g) sY' s).inv z))
      (fibreSquareIso_hom_comp_pullbackLeftPullbackSndIso sY sY' p g hg s)
    simpa only [Scheme.Hom.comp_apply, Iso.trans_hom, Iso.symm_hom] using h.symm
  have hcompare := properPushforward_congr_iso (fieldChowSituation (S.residueField s))
    ((pullback.snd p g ≫ sY').fiberToSpecResidueField s)
    ((p ≫ sY).fiberToSpecResidueField s)
    (pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) ≫
      sY'.fiberToSpecResidueField s)
    (pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s)
    (inducedFiberMap (pullback.snd p g ≫ sY') (p ≫ sY) (pullback.fst p g)
      (pullbackFst_comp_eq_of_base g rfl hg) s)
    (pullback.fst (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s))
    hqout (pullbackFst_comp_eq_of_base (inducedFiberMap sY' sY g hg s) rfl hgf)
    ((compFiberIso (pullback.snd p g) sY' s).symm ≪≫ fibreSquareIso sY sY' p g hg s)
    (compFiberIso p sY s).symm hi ht hsq ((r + e : ℕ) : ℤ) ((r : ℤ) + (e : ℤ))
    (compFamily (pullback.snd p g) sY' r e (baseChangeFamily p g r α) β' s)
    (cap (fieldChowSituation (S.residueField s)) (sY'.fiberToSpecResidueField s)
      (pullback.snd (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s))
      (baseChangeFamily (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) r
        (baseChangeFamily p (sY.fiberι s) r α)) (β' s)) hsource x
  have hmain := properPushforward_cap_baseChangeFamily (fieldChowSituation (S.residueField s))
    (pullback.snd p (sY.fiberι s) ≫ sY.fiberToSpecResidueField s)
    (sY.fiberToSpecResidueField s) (sY'.fiberToSpecResidueField s)
    (pullback.snd p (sY.fiberι s)) (inducedFiberMap sY' sY g hg s) rfl hgf r (e : ℤ)
    (baseChangeFamily p (sY.fiberι s) r α) (β' s)
  have hmainCoeff := congrArg
    (fun z : AlgebraicCycle (pullback p (sY.fiberι s)) ℤ ↦
      z ((compFiberIso p sY s).symm.hom x)) (congrArg Subtype.val hmain)
  exact (hcompare.trans hmainCoeff).trans
    (compFamily_apply_cap p sY r e α (properPushforwardFamily sY' sY g hg e β') s x).symm

end Stacks.Chow

end
