module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionPushPull
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Compatibilities between the operations on families of cycles on fibres

Let `f : X ⟶ S` be locally of finite type and let `r ≥ 0`. A family `α` of `r`-cycles on the
fibres of `X/S` can be base changed along a morphism `g : S' ⟶ S`, restricted to open
subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, pulled back along a flat morphism `X' ⟶ X` of
relative dimension `e`, and pushed forward along a proper morphism `X ⟶ Y` over `S`
(Section 0H4N). This file proves Lemma 0H4P: the seven compatibilities between these operations.

## Main results

* `Stacks.Chow.baseChangeFamily_baseChangeFamily_comp` — **part (1)**, base change is functorial.
* `Stacks.Chow.restrictedFamily_eq_flatPullbackFamily_baseChangeFamily` — **part (2)**,
  restriction is base change to `V` followed by flat pullback along `U ⟶ X ×_S V`.
* `Stacks.Chow.baseChangeFamily_flatPullbackFamily` — **part (3)**, flat pullback commutes with
  base change.
* `Stacks.Chow.flatPullbackFamily_flatPullbackFamily` — **part (4)**, flat pullback is
  functorial.
* `Stacks.Chow.baseChangeFamily_properPushforwardFamily_of_isProper` — **part (5)**, proper
  pushforward commutes with base change.
* `Stacks.Chow.properPushforwardFamily_properPushforwardFamily` — **part (6)**, proper
  pushforward is functorial.
* `Stacks.Chow.flatPullbackFamily_properPushforwardFamily` — **part (7)**, proper pushforward
  commutes with flat pullback.

## Implementation notes

Each part is the corresponding result of Chow homology applied on the fibres over `S`, as in the
source: part (1) is Tag 0FVP, part (3) Tag 0FVK, part (4) Tag 02RD, part (5) Tag 0FVL, part (6)
Tag 02R5 and part (7) Tag 02RG, each over the Chow situation of a residue field. Part (2) is
the observation that base change along an open immersion and flat pullback along an open
immersion change no coefficient.

The fibre of `X ×_S S'` over a point `t` of `S'` is only canonically isomorphic to the base
change `X_{g t} ×_{κ(g t)} κ(t)` used by the Chow-homology statements, through
`Stacks.Chow.fibreBaseChangeIso`; parts (3) and (5) transport the Chow-homology squares along
these isomorphisms, the multiplicities of flat pullback being invariant under them by
`Stacks.Chow.flatPullbackWeight_eq_of_isIso`.

Where the two sides of an identity are families on canonically isomorphic but distinct schemes —
`(X ×_S S') ×_{S'} S''` and `X ×_S S''` in part (1) — the comparison is made along the
isomorphism by `Stacks.Chow.fiberCycleRestrict`. Where they are families of cycles of equal but
not definitionally equal dimensions — `(r + e) + e'` and `r + (e' + e)` in part (4) — the
statement is the equality of the underlying cycles on every fibre.

## References

* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Base change read on the chosen fibre product over the residue field -/

/-- The coefficient of the base change `g^*α` on the fibre over `t` is the coefficient of the
base change of the cycle `α_{g t}` along `κ(t)/κ(g t)`, read through the canonical isomorphism
`Stacks.Chow.fibreBaseChangeIso`. -/
theorem baseChangeFamily_apply_fibreBaseChangeIso {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S')
    (x : (pullback.snd f g).fiber t) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (baseChangeCyclePullback (residueFieldBaseChangeSituation g t)
        (f.fiberToSpecResidueField (g t)) (r : ℤ) (α (g t))).1
          ((fibreBaseChangeIso f g t).hom x) := by
  rw [baseChangeFamily_eq_baseChangeFiberCycle]
  rfl

/-! ### Part (1): base change is functorial -/

/-- **Stacks Project, Tag 0H4P, part (1).** Base change of families of cycles on fibres is
functorial: base changing a family `α` of `r`-cycles on the fibres of `X/S` along `g : S' ⟶ S`
and then along `h : S'' ⟶ S'` is base changing it along `h ≫ g`, the two families being
identified through the canonical isomorphism `(X ×_S S') ×_{S'} S'' ≅ X ×_S S''`. -/
@[stacks 0H4P "part (1): base change is functorial"]
theorem baseChangeFamily_baseChangeFamily_comp {X S S' S'' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (h : S'' ⟶ S') (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamily (pullback.snd f g) h r (baseChangeFamily f g r α) =
      fun u => fiberCycleRestrict (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
        (pullbackLeftPullbackSndIso f g h).hom (pullbackLeftPullbackSndIso_hom_snd f g h) u r
        (baseChangeFamily f (h ≫ g) r α u) := by
  funext u
  exact Subtype.ext <| Function.locallyFinsuppWithin.ext fun x =>
    baseChangeFamily_apply_compBaseChangeFiberIso f g h r u α x

/-! ### Part (2): restriction is base change followed by flat pullback -/

/-- Two morphisms into a fibre agree if they agree after composing with `fiberι` and with
`fiberToSpecResidueField`. -/
private theorem fiber_hom_ext {X S T : Scheme.{u}} (f : X ⟶ S) (s : S) {a b : T ⟶ f.fiber s}
    (h₁ : a ≫ f.fiberι s = b ≫ f.fiberι s)
    (h₂ : a ≫ f.fiberToSpecResidueField s = b ≫ f.fiberToSpecResidueField s) : a = b :=
  pullback.hom_ext h₁ h₂

section Restriction

variable {X S U V : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ V)
  [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
  (h : j ≫ f = fU ≫ i)

/-- The open immersion `U ⟶ X ×_S V` induced by open immersions `j : U ⟶ X` and `i : V ⟶ S`
with `f(U) ⊆ V`. -/
instance isOpenImmersion_pullbackLift : IsOpenImmersion (pullback.lift j fU h) := by
  have : IsOpenImmersion (pullback.lift j fU h ≫ pullback.fst f i) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst f i)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType fU] [IsOpenImmersion j] [IsOpenImmersion i] in
/-- The canonical open immersion of fibres `U_t ⟶ X_{i t}` factors through the fibre of
`X ×_S V` over `t`. -/
theorem fiberRestrict_pullbackLift_comp_restrictedFiberMap (t : V) :
    fiberRestrict (pullback.snd f i) fU (pullback.lift j fU h) (pullback.lift_snd _ _ _) t ≫
        restrictedFiberMap f (pullback.snd f i) (pullback.fst f i) i pullback.condition t =
      restrictedFiberMap f fU j i h t := by
  refine fiber_hom_ext f (i t) ?_ ?_
  · rw [Category.assoc, restrictedFiberMap_fiberι, fiberRestrict_fiberι_assoc, pullback.lift_fst,
      restrictedFiberMap_fiberι]
  · rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField,
      fiberRestrict_fiberToSpecResidueField_assoc, restrictedFiberMap_comp_fiberToSpecResidueField]

/-- **Stacks Project, Tag 0H4P, part (2).** Restriction of families of cycles on fibres is a
combination of base change and flat pullback: for open subschemes `U ⊆ X` and `V ⊆ S` with
`f(U) ⊆ V`, the restriction `α|_U` of a family `α` of `r`-cycles on the fibres of `X/S` is the
flat pullback, along the open immersion `U ⟶ X ×_S V` (flat of relative dimension zero), of the
base change of `α` along `V ⟶ S`. -/
@[stacks 0H4P "part (2): restriction is base change followed by flat pullback"]
theorem restrictedFamily_eq_flatPullbackFamily_baseChangeFamily (r : ℕ)
    (α : FamilyOfCycles f r) :
    (restrictedFamily f fU j i h r α).1 =
      flatPullbackFamily (pullback.snd f i) fU (pullback.lift j fU h) (pullback.lift_snd _ _ _) 0
        (relativeDimension_of_isOpenImmersion _) r (baseChangeFamily f i r α) := by
  have hres : ∀ t : V, IsIso (i.residueFieldMap t) := fun t => by
    have : IsIso (i.stalkMap t) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i)).2 t
    exact (IsLocalRing.ResidueField.mapEquiv
      (asIso (i.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  funext t
  apply Subtype.ext
  let jt := fiberRestrict (pullback.snd f i) fU (pullback.lift j fU h) (pullback.lift_snd _ _ _) t
  have hflat := cycleGroupRestrict_eq_flatPullback (fieldChowSituation (V.residueField t))
    ((pullback.snd f i).fiberToSpecResidueField t) (fU.fiberToSpecResidueField t) jt
    (fiberRestrict_fiberToSpecResidueField _ _ _ _ t)
    (relativeDimension_fiberRestrict _ _ _ _ t (relativeDimension_of_isOpenImmersion _)) (r : ℤ)
    (baseChangeFamily f i r α t)
  refine Eq.trans (Function.locallyFinsuppWithin.ext fun x => ?_) hflat
  rw [(restrictedFamily f fU j i h r α).2 t x, cycleGroupRestrict_apply,
    baseChangeFamily_eq_baseChangeFamilyOfResidueIso f i hres r α,
    baseChangeFamilyOfResidueIso_apply, ← Scheme.Hom.comp_apply,
    fiberRestrict_pullbackLift_comp_restrictedFiberMap]

end Restriction

/-! ### Part (3): flat pullback commutes with base change -/

/-- **Stacks Project, Tag 0H4P, part (3).** Flat pullback of families of cycles on fibres commutes
with base change: for a flat morphism `j : U ⟶ X` over `S`, locally of finite type and of
relative dimension `e`, and a morphism `g : T ⟶ S`, the base change of `j^*α` along `g` is the
flat pullback of `g^*α` along the base change `U ×_S T ⟶ X ×_S T` of `j`. -/
@[stacks 0H4P "part (3): flat pullback commutes with base change"]
theorem baseChangeFamily_flatPullbackFamily {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (g : T ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) :
    baseChangeFamily fU g (r + e) (flatPullbackFamily f fU j h e he r α) =
      flatPullbackFamily (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
        (pullbackRestrict_snd f fU j h g) e (relativeDimension_pullbackRestrict f fU j h g he) r
        (baseChangeFamily f g r α) := by
  funext t
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  let B := residueFieldBaseChangeSituation g t
  let sY := fU.fiberToSpecResidueField (g t)
  let sX := f.fiberToSpecResidueField (g t)
  let jt := fiberRestrict f fU j h (g t)
  have hjt : jt ≫ sX = sY := fiberRestrict_fiberToSpecResidueField f fU j h (g t)
  have hejt : AlgebraicGeometry.RelativeDimension jt e :=
    relativeDimension_fiberRestrict f fU j h (g t) he
  let j' := pullbackRestrict sX sY jt hjt B.g
  have hej' : AlgebraicGeometry.RelativeDimension j' e :=
    relativeDimension_pullbackRestrict sX sY jt hjt B.g hejt
  let jT := fiberRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
    (pullbackRestrict_snd f fU j h g) t
  have key := baseChangeCyclePullback_flatPullback_apply B sY sX jt hjt j'
    (pullbackRestrict_snd sX sY jt hjt B.g) (pullbackRestrict_fst sX sY jt hjt B.g).symm e hejt
    hej' (r : ℤ) (baseChangeClosedSubschemeCycleRule_holds B)
    (flatPullbackClosedSubschemeCycleRule_holds B.baseChange (pullback.snd sY B.g)
      (pullback.snd sX B.g) j' (pullbackRestrict_snd sX sY jt hjt B.g) e hej' ((r : ℤ) + B.c))
    (α (g t)) ((fibreBaseChangeIso fU g t).hom z)
  have hpt : (fibreBaseChangeIso f g t).hom (jT z) = j' ((fibreBaseChangeIso fU g t).hom z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : (pullback.snd fU g).fiber t ⟶ pullback sX B.g => m z)
        (fibreBaseChangeIso_hom_pullbackRestrict f fU j h g t)
  have hw := flatPullbackWeight_eq_of_isIso (fieldChowSituation (T.residueField t))
    ((pullback.snd fU g).fiberToSpecResidueField t) (pullback.snd sY B.g)
    (fibreBaseChangeIso f g t).hom (fibreBaseChangeIso fU g t).hom
    (fibreBaseChangeIso_hom_snd fU g t) jT j'
    (fibreBaseChangeIso_hom_pullbackRestrict f fU j h g t) ((r : ℤ) + (e : ℤ)) z
  refine (baseChangeFamily_apply_fibreBaseChangeIso fU g (r + e) _ t z).trans
    (key.trans ?_)
  change (baseChangeCyclePullback B sX (r : ℤ) (α (g t))).1
      (j' ((fibreBaseChangeIso fU g t).hom z)) *
        flatPullbackWeight B.baseChange (pullback.snd sY B.g) j' ((r : ℤ) + 0 + (e : ℤ))
          ((fibreBaseChangeIso fU g t).hom z) =
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) (jT z) *
      flatPullbackWeight (fieldChowSituation (T.residueField t))
        ((pullback.snd fU g).fiberToSpecResidueField t) jT ((r : ℤ) + (e : ℤ)) z
  rw [baseChangeFamily_apply_fibreBaseChangeIso f g r α t (jT z), hpt, hw]
  rfl

/-! ### Part (4): flat pullback is functorial -/

/-- The morphism of fibres induced by a composite of two morphisms over the base is the composite
of the two induced morphisms of fibres. -/
theorem fiberRestrict_comp {X S U V : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (fV : V ⟶ S)
    (j : U ⟶ X) (k : V ⟶ U) (h : j ≫ f = fU) (hk : k ≫ fU = fV) (s : S) :
    fiberRestrict f fV (k ≫ j) (by rw [Category.assoc, h, hk]) s =
      fiberRestrict fU fV k hk s ≫ fiberRestrict f fU j h s := by
  refine fiber_hom_ext f s ?_ ?_
  · rw [fiberRestrict_fiberι, Category.assoc, fiberRestrict_fiberι, fiberRestrict_fiberι_assoc]
  · rw [fiberRestrict_fiberToSpecResidueField, Category.assoc,
      fiberRestrict_fiberToSpecResidueField, fiberRestrict_fiberToSpecResidueField]

/-- **Stacks Project, Tag 0H4P, part (4).** Flat pullback of families of cycles on fibres is
functorial: for flat morphisms `j : U ⟶ X` and `k : V ⟶ U` over `S`, locally of finite type and
of relative dimensions `e` and `e'`, pulling a family `α` of `r`-cycles on the fibres of `X/S`
back along `j` and then along `k` is pulling it back along `k ≫ j`, which has relative dimension
`e' + e`.

The two families are families of cycles of the dimensions `(r + e) + e'` and `r + (e' + e)`,
which are equal but not definitionally so; the statement is the equality of the underlying
cycles on every fibre of `V/S`. -/
@[stacks 0H4P "part (4): flat pullback is functorial"]
theorem flatPullbackFamily_flatPullbackFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (fV : V ⟶ S)
    [LocallyOfFiniteType fV] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (k : V ⟶ U)
    [LocallyOfFiniteType k] [Flat k] (h : j ≫ f = fU) (hk : k ≫ fU = fV) (e e' : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e)
    (he' : AlgebraicGeometry.RelativeDimension k e') (r : ℕ) (α : FamilyOfCycles f r) (s : S) :
    (flatPullbackFamily fU fV k hk e' he' (r + e) (flatPullbackFamily f fU j h e he r α) s :
        AlgebraicCycle (fV.fiber s) ℤ) =
      (flatPullbackFamily f fV (k ≫ j) (by rw [Category.assoc, h, hk]) (e' + e)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat k j he' he) r α s :
          AlgebraicCycle (fV.fiber s) ℤ) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  let C := fieldChowSituation (S.residueField s)
  have hcomp := flatPullback_comp_apply C (fV.fiberToSpecResidueField s)
    (fU.fiberToSpecResidueField s) (f.fiberToSpecResidueField s) (fiberRestrict fU fV k hk s)
    (fiberRestrict f fU j h s) (fiberRestrict_fiberToSpecResidueField fU fV k hk s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) e' e
    (relativeDimension_fiberRestrict fU fV k hk s he')
    (relativeDimension_fiberRestrict f fU j h s he) (r : ℤ) (α s) x
  refine hcomp.trans ?_
  rw [flatPullback_apply, flatPullbackFamily_apply, fiberCycleFlatPullback_apply,
    fiberRestrict_comp f fU fV j k h hk s]

/-! ### Part (5): proper pushforward commutes with base change -/

section ProperBaseChange

variable {X Y S S' : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (g : S' ⟶ S)

/-- The base change of a proper morphism over the base is proper. -/
instance isProper_baseChangeMap : IsProper (baseChangeMap sX sY f hf g) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMap sX sY f hf g) inferInstance

end ProperBaseChange

/-- The base change of a proper morphism of schemes over a fixed base is proper. -/
instance isProper_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [IsProper j] (h : j ≫ f = fU) (g : T ⟶ S) :
    IsProper (pullbackRestrict f fU j h g) :=
  MorphismProperty.of_isPullback (isPullback_pullbackRestrict f fU j h g) inferInstance

/-- **Stacks Project, Tag 0FVL, the cycle square, for an arbitrary structure morphism of the
source.** The cycle square of `Stacks.Chow.properPushforward_baseChangeCyclePullback`, with the
source of the proper morphism `f : A ⟶ Y` carrying any structure morphism `s_A` equal to
`f ≫ s_Y`, and the base change of `f` the morphism `A ×_S S' ⟶ Y ×_S S'` it induces. -/
theorem properPushforward_baseChangeCyclePullback_of_comp_eq (B : FlatBaseChangeSituation.{u})
    {A Y : Scheme.{u}} (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sA : A ⟶ B.base.S)
    [LocallyOfFiniteType sA] (f : A ⟶ Y) [IsProper f] (hf : f ≫ sY = sA) (k : ℤ)
    (z : CycleGroup B.base sA k) (y : (pullback sY B.g : Scheme.{u})) :
    (properPushforward B.baseChange (pullback.snd sA B.g) (pullback.snd sY B.g)
        (pullbackRestrict sY sA f hf B.g) (pullbackRestrict_snd sY sA f hf B.g) (k + B.c)
        (baseChangeCyclePullback B sA k z)).1 y =
      (baseChangeCyclePullback B sY k (properPushforward B.base sA sY f hf k z)).1 y := by
  subst hf
  exact congrArg (fun c => c.1 y) (properPushforward_baseChangeCyclePullback B sY f k z)

section ProperBaseChange

variable {X Y S S' : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (g : S' ⟶ S)

/-- **Stacks Project, Tag 0H4P, part (5).** Proper pushforward of families of cycles on fibres
commutes with base change: for a proper morphism `f : X ⟶ Y` of schemes locally of finite type
over `S` and a morphism `g : S' ⟶ S`, the base change of `f_*α` along `g` is the pushforward of
`g^*α` along the base change `X ×_S S' ⟶ Y ×_S S'` of `f`. -/
@[stacks 0H4P "part (5): proper pushforward commutes with base change"]
theorem baseChangeFamily_properPushforwardFamily_of_isProper (r : ℕ) (α : FamilyOfCycles sX r) :
    baseChangeFamily sY g r (properPushforwardFamily sX sY f hf r α) =
      properPushforwardFamily (pullback.snd sX g) (pullback.snd sY g)
        (baseChangeMap sX sY f hf g) (baseChangeMap_snd sX sY f hf g) r
        (baseChangeFamily sX g r α) := by
  funext t
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun y => ?_
  let B := residueFieldBaseChangeSituation g t
  let sXt := sX.fiberToSpecResidueField (g t)
  let sYt := sY.fiberToSpecResidueField (g t)
  let ft := inducedFiberMap sX sY f hf (g t)
  have hft : ft ≫ sYt = sXt := inducedFiberMap_fiberToSpecResidueField sX sY f hf (g t)
  let fT := inducedFiberMap (pullback.snd sX g) (pullback.snd sY g) (baseChangeMap sX sY f hf g)
    (baseChangeMap_snd sX sY f hf g) t
  have hij : fT ≫ (fibreBaseChangeIso sY g t).hom =
      (fibreBaseChangeIso sX g t).hom ≫ pullbackRestrict sYt sXt ft hft B.g := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, fibreBaseChangeIso_hom_fst, Category.assoc, pullbackRestrict_fst,
        ← Category.assoc, fibreBaseChangeIso_hom_fst]
      exact (restrictedFiberMap_comp_inducedFiberMap sX sY f hf g t).symm
    · rw [Category.assoc, fibreBaseChangeIso_hom_snd, Category.assoc, pullbackRestrict_snd,
        fibreBaseChangeIso_hom_snd]
      exact inducedFiberMap_fiberToSpecResidueField _ _ _ _ t
  have hmove := properPushforward_congr_iso (fieldChowSituation (S'.residueField t))
    ((pullback.snd sX g).fiberToSpecResidueField t) ((pullback.snd sY g).fiberToSpecResidueField t)
    (pullback.snd sXt B.g) (pullback.snd sYt B.g) fT (pullbackRestrict sYt sXt ft hft B.g)
    (inducedFiberMap_fiberToSpecResidueField _ _ _ _ t) (pullbackRestrict_snd sYt sXt ft hft B.g)
    (fibreBaseChangeIso sX g t) (fibreBaseChangeIso sY g t) (fibreBaseChangeIso_hom_snd sX g t)
    (fibreBaseChangeIso_hom_snd sY g t) hij (r : ℤ) ((r : ℤ) + B.c) (baseChangeFamily sX g r α t)
    (baseChangeCyclePullback B sXt (r : ℤ) (α (g t)))
    (baseChangeFamily_apply_fibreBaseChangeIso sX g r α t) y
  exact (baseChangeFamily_apply_fibreBaseChangeIso sY g r _ t y).trans <|
    (properPushforward_baseChangeCyclePullback_of_comp_eq B sYt sXt ft hft (r : ℤ) (α (g t))
      ((fibreBaseChangeIso sY g t).hom y)).symm.trans hmove.symm

end ProperBaseChange

/-! ### Part (6): proper pushforward is functorial -/

/-- The morphism of fibres induced by a composite of two morphisms over the base is the composite
of the two induced morphisms of fibres. -/
theorem inducedFiberMap_comp {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (hf₁ : f₁ ≫ sY = sX) (hf₂ : f₂ ≫ sZ = sY) (s : S) :
    inducedFiberMap sX sZ (f₁ ≫ f₂) (by rw [Category.assoc, hf₂, hf₁]) s =
      inducedFiberMap sX sY f₁ hf₁ s ≫ inducedFiberMap sY sZ f₂ hf₂ s := by
  refine fiber_hom_ext sZ s ?_ ?_
  · rw [inducedFiberMap_fiberι, Category.assoc, inducedFiberMap_fiberι,
      inducedFiberMap_fiberι_assoc]
  · rw [inducedFiberMap_fiberToSpecResidueField, Category.assoc,
      inducedFiberMap_fiberToSpecResidueField, inducedFiberMap_fiberToSpecResidueField]

/-- Proper pushforward of cycles along two equal proper morphisms agrees. -/
private theorem properPushforward_congr_hom (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (a b : A ⟶ B) [IsProper a] [IsProper b] (ha : a ≫ sB = sA) (hb : b ≫ sB = sA) (hab : a = b)
    (k : ℤ) (c : CycleGroup C sA k) :
    properPushforward C sA sB a ha k c = properPushforward C sA sB b hb k c := by
  subst hab
  rfl

/-- **Stacks Project, Tag 0H4P, part (6).** Proper pushforward of families of cycles on fibres is
functorial: for proper morphisms `f₁ : X ⟶ Y` and `f₂ : Y ⟶ Z` of schemes locally of finite type
over `S`, pushing a family of `r`-cycles on the fibres of `X/S` forward along `f₁` and then along
`f₂` is pushing it forward along `f₁ ≫ f₂`. -/
@[stacks 0H4P "part (6): proper pushforward is functorial"]
theorem properPushforwardFamily_properPushforwardFamily {S X Y Z : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (sZ : Z ⟶ S)
    [LocallyOfFiniteType sZ] (f₁ : X ⟶ Y) [IsProper f₁] (f₂ : Y ⟶ Z) [IsProper f₂]
    (hf₁ : f₁ ≫ sY = sX) (hf₂ : f₂ ≫ sZ = sY) (r : ℕ) (α : FamilyOfCycles sX r) :
    properPushforwardFamily sY sZ f₂ hf₂ r (properPushforwardFamily sX sY f₁ hf₁ r α) =
      properPushforwardFamily sX sZ (f₁ ≫ f₂) (by rw [Category.assoc, hf₂, hf₁]) r α := by
  funext s
  let C := fieldChowSituation (S.residueField s)
  exact (congrFun (properPushforward_comp C (sX.fiberToSpecResidueField s)
    (sY.fiberToSpecResidueField s) (sZ.fiberToSpecResidueField s) (inducedFiberMap sX sY f₁ hf₁ s)
    (inducedFiberMap sY sZ f₂ hf₂ s) (inducedFiberMap_fiberToSpecResidueField sX sY f₁ hf₁ s)
    (inducedFiberMap_fiberToSpecResidueField sY sZ f₂ hf₂ s) (r : ℤ)) (α s)).trans <|
    properPushforward_congr_hom C _ _ _ _ _
    (inducedFiberMap_fiberToSpecResidueField _ _ _ _ s)
    (inducedFiberMap_comp sX sY sZ f₁ f₂ hf₁ hf₂ s).symm _ _

/-! ### Part (7): proper pushforward commutes with flat pullback -/

/-- The fibres over a point `s` of the base of a cartesian square of schemes over `S` form a
cartesian square: if `X' = X ×_Y Y'`, then `X'_s = X_s ×_{Y_s} Y'_s`. -/
theorem isPullback_fiber_of_isPullback {S X Y X' Y' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (sX' : X' ⟶ S) (sY' : Y' ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : IsPullback g' f' f g) (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (hf' : f' ≫ sY' = sX') (s : S) :
    IsPullback (fiberRestrict sX sX' g' hg' s) (inducedFiberMap sX' sY' f' hf' s)
      (inducedFiberMap sX sY f hf s) (fiberRestrict sY sY' g hg s) := by
  have houter : IsPullback (sX'.fiberι s ≫ g') (inducedFiberMap sX' sY' f' hf' s) f
      (sY'.fiberι s ≫ g) :=
    (isPullback_inducedFiberMap sX' sY' f' hf' s).paste_horiz hsq
  rw [← fiberRestrict_fiberι sX sX' g' hg' s, ← fiberRestrict_fiberι sY sY' g hg s] at houter
  refine houter.of_right ?_ (isPullback_inducedFiberMap sX sY f hf s)
  refine fiber_hom_ext sY s ?_ ?_
  · simp only [Category.assoc, inducedFiberMap_fiberι, fiberRestrict_fiberι_assoc]
    rw [hsq.w, fiberRestrict_fiberι, inducedFiberMap_fiberι_assoc]
  · rw [Category.assoc, inducedFiberMap_fiberToSpecResidueField,
      fiberRestrict_fiberToSpecResidueField, Category.assoc,
      fiberRestrict_fiberToSpecResidueField, inducedFiberMap_fiberToSpecResidueField]

section ProperFlat

variable {X Y Y' S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (sY' : Y' ⟶ S) [LocallyOfFiniteType sY'] (f : X ⟶ Y) [IsProper f]
  (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g] (hg : g ≫ sY = sY')

/-- The second projection of `X ×_Y Y'` is a morphism over `S`. -/
theorem pullback_snd_comp_eq_fst_comp {X Y Y' S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (sY' : Y' ⟶ S) (f : X ⟶ Y) (hf : f ≫ sY = sX) (g : Y' ⟶ Y) (hg : g ≫ sY = sY') :
    pullback.snd f g ≫ sY' = pullback.fst f g ≫ sX := by
  rw [← hg, ← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- **Stacks Project, Tag 0H4P, part (7).** Proper pushforward of families of cycles on fibres
commutes with flat pullback: for a proper morphism `f : X ⟶ Y` and a flat morphism `g : Y' ⟶ Y`
of relative dimension `e` of schemes locally of finite type over `S`, with base changes
`f' : X ×_Y Y' ⟶ Y'` and `g' : X ×_Y Y' ⟶ X`, one has `g^*(f_*α) = f'_*((g')^*α)` for every
family `α` of `r`-cycles on the fibres of `X/S`. -/
@[stacks 0H4P "part (7): proper pushforward commutes with flat pullback"]
theorem flatPullbackFamily_properPushforwardFamily (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension g e) (r : ℕ) (α : FamilyOfCycles sX r) :
    flatPullbackFamily sY sY' g hg e he r (properPushforwardFamily sX sY f hf r α) =
      properPushforwardFamily (pullback.fst f g ≫ sX) sY' (pullback.snd f g)
        (pullback_snd_comp_eq_fst_comp sX sY sY' f hf g hg) (r + e)
        (flatPullbackFamily sX (pullback.fst f g ≫ sX) (pullback.fst f g) rfl e
          (AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback f g).flip
            he) r α) := by
  funext s
  exact flatPullback_properPushforward_cycles (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
    ((pullback.fst f g ≫ sX).fiberToSpecResidueField s) (sY'.fiberToSpecResidueField s)
    (inducedFiberMap sX sY f hf s) (fiberRestrict sY sY' g hg s)
    (fiberRestrict sX (pullback.fst f g ≫ sX) (pullback.fst f g) rfl s)
    (inducedFiberMap (pullback.fst f g ≫ sX) sY' (pullback.snd f g)
      (pullback_snd_comp_eq_fst_comp sX sY sY' f hf g hg) s)
    (isPullback_fiber_of_isPullback sX sY (pullback.fst f g ≫ sX) sY' f g (pullback.fst f g)
      (pullback.snd f g) (IsPullback.of_hasPullback f g) hf hg rfl
      (pullback_snd_comp_eq_fst_comp sX sY sY' f hf g hg) s)
    (inducedFiberMap_fiberToSpecResidueField sX sY f hf s)
    (fiberRestrict_fiberToSpecResidueField sY sY' g hg s)
    (fiberRestrict_fiberToSpecResidueField sX _ _ rfl s) e
    (relativeDimension_fiberRestrict sY sY' g hg s he) (r : ℤ) (α s)

end ProperFlat

end Stacks.Chow

end
