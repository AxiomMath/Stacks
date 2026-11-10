module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.CapCommute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine

/-!
# The exterior product over a Dedekind base commutes with proper pushforward

Let `(S, δ)` be as in Stacks section 42.63, let `X` be locally of finite type over `S`, let
`h : T' ⟶ T` be a proper morphism of schemes locally of finite type over `S` and let
`1 × h : X ×_S T' ⟶ X ×_S T` be its base change. Then for `α ∈ CH_n(X)` and `β ∈ CH_m(T')`

  `α × h_* β = (1 × h)_* (α × β)`   in   `CH_{n+m-1}(X ×_S T)`.

This is condition (1) of Stacks 0B76 for the operation `β ↦ α × β`.

## Main results

* `Stacks.Chow.exteriorProductDedekindCycles_properPushforward`: the identity for cycles, up to
  rational equivalence.
* `Stacks.Chow.exteriorProductDedekindChowTensor_properChowPushforward`: the identity on Chow
  groups.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The fibre of a point closure over a proper morphism of test schemes -/

section Geometry

variable {S X T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) (x : X)

/-- Inside `X ×_S T'`, the subscheme `closure {x} ×_S T'` is the inverse image of
`closure {x} ×_S T ⊆ X ×_S T` under the base change of `h`. -/
theorem dedekindPointFibre_comp_eq_comap :
    dedekindPointFibre f (h ≫ g) x =
      (dedekindPointFibre f g x).comap (bivariantBaseChangeMap f g h) := by
  rw [dedekindPointFibre, dedekindPointFibre, ← Scheme.IdealSheafData.comap_comp,
    bivariantBaseChangeMap_fst]

/-- The morphism `closure {x} ×_S T' ⟶ closure {x} ×_S T` over `h`. -/
def properPointFibreMap :
    (dedekindPointFibre f (h ≫ g) x).subscheme ⟶ (dedekindPointFibre f g x).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (bivariantBaseChangeMap f g h)
    (Scheme.IdealSheafData.le_map_iff_comap_le.2
      (le_of_eq (dedekindPointFibre_comp_eq_comap f g h x).symm))

/-- `properPointFibreMap` lies over the base change `X ×_S T' ⟶ X ×_S T` of `h`. -/
@[reassoc (attr := simp)]
theorem properPointFibreMap_subschemeι :
    properPointFibreMap f g h x ≫ (dedekindPointFibre f g x).subschemeι =
      (dedekindPointFibre f (h ≫ g) x).subschemeι ≫ bivariantBaseChangeMap f g h :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The square exhibiting `closure {x} ×_S T'` as the base change of `closure {x} ×_S T ⟶ T`
along `h`. -/
theorem isPullback_properPointFibreMap :
    IsPullback ((dedekindPointFibre f (h ≫ g) x).subschemeι ≫ pullback.snd f (h ≫ g))
      (properPointFibreMap f g h x) h ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) :=
  ((isPullback_subschemeMap_of_eq_comap (bivariantBaseChangeMap f g h) _ _
    (dedekindPointFibre_comp_eq_comap f g h x)).flip.paste_vert
      (isPullback_bivariantBaseChangeMap f g h).flip).flip

/-- The base change `closure {x} ×_S T' ⟶ closure {x} ×_S T` of a proper morphism is proper. -/
instance isProper_properPointFibreMap [IsProper h] : IsProper (properPointFibreMap f g h x) :=
  MorphismProperty.of_isPullback (isPullback_properPointFibreMap f g h x) inferInstance

/-- A morphism into `X ×_S T` has the same structure morphism over `S` via either projection. -/
private theorem comp_snd_comp_eq_comp_fst_comp {Z : Scheme.{u}} (ι : Z ⟶ pullback f g) :
    (ι ≫ pullback.snd f g) ≫ g = ι ≫ (pullback.fst f g ≫ f) := by
  rw [Category.assoc, ← pullback.condition]

end Geometry

/-! ### The summands on the two sides -/

section Summands

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X T T' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (g : T ⟶ C.S) [LocallyOfFiniteType g] (h : T' ⟶ T)
  [IsProper h] (n m : ℤ) (a₀ : CycleGroup C sX n) (b₀ : CycleGroup C (h ≫ g) m)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] [IsProper h] in
/-- The structure morphisms of the two point fibres are compatible with the map between them. -/
theorem properPointFibreMap_comp_structureMorphism (x : X) :
    properPointFibreMap sX g h x ≫
        ((dedekindPointFibre sX g x).subschemeι ≫ (pullback.fst sX g ≫ sX)) =
      (dedekindPointFibre sX (h ≫ g) x).subschemeι ≫ (pullback.fst sX (h ≫ g) ≫ sX) := by
  rw [properPointFibreMap_subschemeι_assoc, bivariantBaseChangeMap_comp_structureMorphism]

/-- The summand of `α × h_* β` at a point `x` of the support of `α`, on `closure {x} ×_S T`, and
the summand of `α × β` at `x`, on `closure {x} ×_S T'`, the first being the pushforward of the
second along `closure {x} ×_S T' ⟶ closure {x} ×_S T` up to rational equivalence. -/
def ProperSummandData (x : X) : Prop :=
  ∃ (a : CycleGroup C ((dedekindPointFibre sX g x).subschemeι ≫ (pullback.fst sX g ≫ sX))
      (n + m - 1))
    (a' : CycleGroup C ((dedekindPointFibre sX (h ≫ g) x).subschemeι ≫
      (pullback.fst sX (h ≫ g) ≫ sX)) (n + m - 1)),
    (∀ z, (properPushforward C ((dedekindPointFibre sX g x).subschemeι ≫
      (pullback.fst sX g ≫ sX)) (pullback.fst sX g ≫ sX) (dedekindPointFibre sX g x).subschemeι
        rfl (n + m - 1) a).1 z =
        ∑ᶠ y : T, exteriorProductDedekindTerm C sX g n m a₀
          (properPushforward C (h ≫ g) g h rfl m b₀) z (x, y)) ∧
    (∀ z, (properPushforward C ((dedekindPointFibre sX (h ≫ g) x).subschemeι ≫
      (pullback.fst sX (h ≫ g) ≫ sX)) (pullback.fst sX (h ≫ g) ≫ sX)
        (dedekindPointFibre sX (h ≫ g) x).subschemeι rfl (n + m - 1) a').1 z =
        ∑ᶠ y : T', exteriorProductDedekindTerm C sX (h ≫ g) n m a₀ b₀ z (x, y)) ∧
    QuotientAddGroup.mk' (rationalEquivalences C _ (n + m - 1)) a =
      properChowPushforward C _ _ (properPointFibreMap sX g h x)
        (properPointFibreMap_comp_structureMorphism sX g h x) (n + m - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (QuotientAddGroup.mk' (rationalEquivalences C _ (n + m - 1)) a')

include hC in
/-- **The summands at a dominating point.** Proper pushforward commutes with the summand at a
point whose closure dominates an irreducible component of the base. -/
theorem properSummandData_of_dominates (x : X) (hdom : DominatesBaseComponent C sX x) :
    ProperSummandData sX g h n m a₀ b₀ x := by
  classical
  obtain ⟨hflat, r, hr, hrel⟩ := exists_relativeDimension_dedekindPointFibre C sX g hC x hdom
  obtain ⟨hflat', r', hr', hrel'⟩ :=
    exists_relativeDimension_dedekindPointFibre C sX (h ≫ g) hC x hdom
  obtain rfl : r = r' := by omega
  by_cases hdeg : m + (r : ℤ) = n + m - 1
  swap
  · refine ⟨0, 0, fun z ↦ ?_, fun z ↦ ?_, by rw [map_zero, map_zero, map_zero]⟩
    · rw [properPushforward_zero, finsum_exteriorProductDedekindTerm_eq_zero sX g n m a₀ _ x hdom
        r hr hdeg z]
      rfl
    · rw [properPushforward_zero, finsum_exteriorProductDedekindTerm_eq_zero sX (h ≫ g) n m a₀ b₀
        x hdom r hr' hdeg z]
      rfl
  have hbase := comp_snd_comp_eq_comp_fst_comp sX g (dedekindPointFibre sX g x).subschemeι
  have hbase' :=
    comp_snd_comp_eq_comp_fst_comp sX (h ≫ g) (dedekindPointFibre sX (h ≫ g) x).subschemeι
  refine ⟨hdeg ▸ flatPullback C _ g _ hbase r hr m
      (a₀.1 x • properPushforward C (h ≫ g) g h rfl m b₀),
    hdeg ▸ flatPullback C _ (h ≫ g) _ hbase' r hr' m (a₀.1 x • b₀),
    properPushforward_flatPullback_of_dominates C sX g n m a₀ _ x hdom r hr hdeg _
      (val_cycleGroup_cast C _ hdeg _),
    properPushforward_flatPullback_of_dominates C sX (h ≫ g) n m a₀ b₀ x hdom r hr' hdeg _
      (val_cycleGroup_cast C _ hdeg _), ?_⟩
  have h02RG := flatPullbackChow_properChowPushforward_unconditional C (h ≫ g) g _ _ h
    ((dedekindPointFibre sX g x).subschemeι ≫ pullback.snd sX g)
    ((dedekindPointFibre sX (h ≫ g) x).subschemeι ≫ pullback.snd sX (h ≫ g))
    (properPointFibreMap sX g h x) (isPullback_properPointFibreMap sX g h x) rfl hbase hbase' r hr
    m (QuotientAddGroup.mk' (rationalEquivalences C (h ≫ g) m) (a₀.1 x • b₀))
  have hpush : properChowPushforward C (h ≫ g) g h rfl m (properPushforwardDescends C _ _ _ _ _)
      (QuotientAddGroup.mk' (rationalEquivalences C (h ≫ g) m) (a₀.1 x • b₀)) =
      QuotientAddGroup.mk' (rationalEquivalences C g m)
        (a₀.1 x • properPushforward C (h ≫ g) g h rfl m b₀) := by
    rw [properChowPushforward_mk, properPushforward_zsmul]
  rw [hpush] at h02RG
  apply eq_of_heq
  refine (mk_cast_heq _ hdeg _).trans ?_
  refine HEq.trans (heq_of_eq ((flatPullbackChow_mk C _ g _ hbase r hr m
    (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans h02RG)) ?_
  refine properChowPushforward_heq_congr C _ _ _ _ hdeg _ _ _ _ ?_
  refine HEq.trans (heq_of_eq (flatPullbackChow_mk C _ (h ≫ g) _ hbase' r _ m
    (flatPullbackDescends C _ _ _ _ _ _ _) _)) ?_
  exact (mk_cast_heq _ hdeg _).symm

include hC in
/-- **The summands at a point over a closed point.** Proper pushforward commutes with the summand
at a point whose closure lies over a closed point of the base. -/
theorem properSummandData_of_not_dominates (x : X) (hx : a₀.1 x ≠ 0)
    (hnd : ¬ DominatesBaseComponent C sX x) :
    ProperSummandData sX g h n m a₀ b₀ x := by
  classical
  have hs : closure ({sX.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  obtain ⟨L, hLinv, σ, hσ, htriv⟩ := hC.exists_section_zeroScheme_eq hs
  set DT := Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback g).obj L)
    (AlgebraicGeometry.pullbackGlobalSections g L σ) with hDTdef
  set DT' := Stacks.Divisors.zeroScheme T'
    ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback g).obj L))
    (AlgebraicGeometry.pullbackGlobalSections h _
      (AlgebraicGeometry.pullbackGlobalSections g L σ)) with hDT'def
  have htrivT := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections g L σ htriv
  have hDT : DT = (Stacks.Divisors.zeroScheme C.S L σ).comap g :=
    Stacks.Divisors.zeroScheme_pullback g L σ
  obtain ⟨wT, hwTlft, hwTflat, r, hwT, hrT, hrn⟩ :=
    exists_flat_dedekindPointFibre_fibre C sX g n hC x hnd L σ hσ a₀ hx _ hDT
  have htrivT' := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections h _ _
    htrivT
  have hDTh : DT' = DT.comap h := Stacks.Divisors.zeroScheme_pullback h _ _
  have hDT' : DT' = (Stacks.Divisors.zeroScheme C.S L σ).comap (h ≫ g) := by
    rw [hDTh, hDT, ← Scheme.IdealSheafData.comap_comp]
  obtain ⟨wT', hwT'lft, hwT'flat, r', hwT', hrT', hrn'⟩ :=
    exists_flat_dedekindPointFibre_fibre C sX (h ≫ g) n hC x hnd L σ hσ a₀ hx _ hDT'
  obtain rfl : r = r' := by omega
  have hdeg : m - 1 + (r : ℤ) = n + m - 1 := by omega
  have hm : m = m - 1 + 1 := (Int.sub_add_cancel m 1).symm
  have hsqD := isPullback_subschemeMap_of_eq_comap h DT DT' hDTh
  set hD := Scheme.IdealSheafData.subschemeMap DT' DT h
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hDTh.symm)) with hhD
  have hDι : hD ≫ DT.subschemeι = DT'.subschemeι ≫ h :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have : IsProper hD := MorphismProperty.of_isPullback hsqD inferInstance
  have hsqw : IsPullback wT' (properPointFibreMap sX g h x) hD wT := by
    have s := (isPullback_properPointFibreMap sX g h x).flip
    rw [← hwT, ← hwT'] at s
    refine (IsPullback.of_bot s ?_ hsqD.flip).flip
    refine (cancel_mono DT.subschemeι).1 ?_
    rw [Category.assoc, Category.assoc, hwT, hDι, ← Category.assoc wT', hwT',
      properPointFibreMap_subschemeι_assoc]
    simp only [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd]
  have hwTbase : wT ≫ (DT.subschemeι ≫ g) =
      (dedekindPointFibre sX g x).subschemeι ≫ (pullback.fst sX g ≫ sX) := by
    rw [← Category.assoc, hwT]
    exact comp_snd_comp_eq_comp_fst_comp sX g _
  have hwT'base : wT' ≫ (DT'.subschemeι ≫ (h ≫ g)) =
      (dedekindPointFibre sX (h ≫ g) x).subschemeι ≫ (pullback.fst sX (h ≫ g) ≫ sX) := by
    rw [← Category.assoc, hwT']
    exact comp_snd_comp_eq_comp_fst_comp sX (h ≫ g) _
  set β' := cycleOfDegreeEq g hm (properPushforward C (h ≫ g) g h rfl m b₀) with hβ'
  set b₀' := cycleOfDegreeEq (h ≫ g) hm b₀ with hb₀'
  refine ⟨cycleOfDegreeEq _ hdeg (flatPullback C _ (DT.subschemeι ≫ g) wT hwTbase r hrT (m - 1)
      (a₀.1 x • gysinCycleMap C g (m - 1) _ _ htrivT β')),
    cycleOfDegreeEq _ hdeg (flatPullback C _ (DT'.subschemeι ≫ (h ≫ g)) wT' hwT'base r hrT'
      (m - 1) (a₀.1 x • gysinCycleMap C (h ≫ g) (m - 1) _ _ htrivT' b₀')),
    properPushforward_flatPullback_gysin_of_not_dominates C sX g n m hC x hnd L σ hσ a₀ _ _ _
      htrivT hDT wT hwT r hrT hdeg β' rfl _ rfl,
    properPushforward_flatPullback_gysin_of_not_dominates C sX (h ≫ g) n m hC x hnd L σ hσ a₀ b₀
      _ _ htrivT' hDT' wT' hwT' r hrT' hdeg b₀' rfl _ rfl, ?_⟩
  have hβ'push : β' = properPushforward C (h ≫ g) g h rfl (m - 1 + 1) b₀' :=
    Subtype.ext (properPushforward_val_cycleOfDegreeEq _ _ _ _ hm b₀).symm
  have hgysT : QuotientAddGroup.mk' (rationalEquivalences C (DT.subschemeι ≫ g) (m - 1))
      (a₀.1 x • gysinCycleMap C g (m - 1) _ _ htrivT β') =
      properChowPushforward C (DT'.subschemeι ≫ (h ≫ g)) (DT.subschemeι ≫ g) hD
        (by rw [← Category.assoc, hDι, Category.assoc]) (m - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (QuotientAddGroup.mk' (rationalEquivalences C (DT'.subschemeι ≫ (h ≫ g)) (m - 1))
          (a₀.1 x • gysinCycleMap C (h ≫ g) (m - 1) _ _ htrivT' b₀')) := by
    have h02TA := gysinSystemOfInvertible_onChow_properChowPushforward C (h ≫ g) g h rfl
      ((Scheme.Modules.pullback g).obj L) (AlgebraicGeometry.pullbackGlobalSections g L σ)
      ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback g).obj L))
      (AlgebraicGeometry.pullbackGlobalSections h _
        (AlgebraicGeometry.pullbackGlobalSections g L σ)) (Iso.refl _) rfl hD hDι
      (by rw [← Category.assoc, hDι, Category.assoc]) (m - 1)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (QuotientAddGroup.mk' (rationalEquivalences C (h ≫ g) (m - 1 + 1)) b₀')
    rw [map_zsmul, map_zsmul, map_zsmul]
    congr 1
    refine ((mk_gysinCycleMap C g (m - 1) _ _ htrivT β').trans
      (gysinChowOfInvertible_mk C _ _ _ _ β').symm).trans ?_
    rw [hβ'push, ← properChowPushforward_mk C (h ≫ g) g h rfl (m - 1 + 1)
      (properPushforwardDescends C _ _ _ _ _)]
    refine h02TA.trans ?_
    exact congrArg _ ((mk_gysinCycleMap C (h ≫ g) (m - 1) _ _ htrivT' b₀').trans
      (gysinChowOfInvertible_mk C _ _ _ _ b₀').symm).symm
  have h02RG := flatPullbackChow_properChowPushforward_unconditional C
    (DT'.subschemeι ≫ (h ≫ g)) (DT.subschemeι ≫ g) _ _ hD wT wT'
    (properPointFibreMap sX g h x) hsqw (by rw [← Category.assoc, hDι, Category.assoc]) hwTbase
    hwT'base r hrT (m - 1)
    (QuotientAddGroup.mk' (rationalEquivalences C (DT'.subschemeι ≫ (h ≫ g)) (m - 1))
      (a₀.1 x • gysinCycleMap C (h ≫ g) (m - 1) _ _ htrivT' b₀'))
  rw [← hgysT] at h02RG
  apply eq_of_heq
  refine (mk_heq_of_val_eq _ hdeg.symm _ _ rfl).trans ?_
  refine HEq.trans (heq_of_eq ((flatPullbackChow_mk C _ _ wT hwTbase r hrT (m - 1)
    (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans h02RG)) ?_
  refine properChowPushforward_heq_congr C _ _ _ _ hdeg _ _ _ _ ?_
  refine HEq.trans (heq_of_eq (flatPullbackChow_mk C _ _ wT' hwT'base r _ (m - 1)
    (flatPullbackDescends C _ _ _ _ _ _ _) _)) ?_
  exact mk_heq_of_val_eq _ hdeg _ _ rfl

end Summands

/-! ### The identity -/

section Main

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X T T' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (g : T ⟶ C.S) [LocallyOfFiniteType g] (h : T' ⟶ T)
  [IsProper h] (n m : ℤ)

include hC in
/-- **The exterior product over a Dedekind base commutes with proper pushforward in the second
variable, on cycles.** For a proper `h : T' ⟶ T`, an `n`-cycle `α` on `X` and an `m`-cycle `β`
on `T'`, the cycles `α × h_* β` and `(1 × h)_* (α × β)` on `X ×_S T` are rationally
equivalent. -/
theorem exteriorProductDedekindCycles_properPushforward (a₀ : CycleGroup C sX n)
    (b₀ : CycleGroup C (h ≫ g) m) :
    QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX g ≫ sX) (n + m - 1))
        (exteriorProductDedekindCycles C sX g n m a₀ (properPushforward C (h ≫ g) g h rfl m b₀)) =
      properChowPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
        (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
        (n + m - 1) (properPushforwardDescends C _ _ _ _ _)
        (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX (h ≫ g) ≫ sX) (n + m - 1))
          (exteriorProductDedekindCycles C sX (h ≫ g) n m a₀ b₀)) := by
  classical
  have hsum : ∀ x : a₀.1.support, ProperSummandData sX g h n m a₀ b₀ x := fun x ↦ by
    by_cases hdom : DominatesBaseComponent C sX x.1
    · exact properSummandData_of_dominates hC sX g h n m a₀ b₀ x.1 hdom
    · exact properSummandData_of_not_dominates hC sX g h n m a₀ b₀ x.1 x.2 hdom
  choose a a' hP1 hP2 hP3 using hsum
  have hfin_aux : ∀ {Y : Scheme.{u}} (q : Y ⟶ C.S), LocallyFinite fun x : a₀.1.support ↦
      Set.range (dedekindPointFibre sX q x.1).subschemeι := fun q ↦
    (locallyFinite_dedekindPointFibre sX q a₀.1).subset fun x ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
  have hfin := hfin_aux g
  have hfin' := hfin_aux (h ≫ g)
  have hA := exteriorProductDedekindCycles_apply_eq_finsum C sX g n m a₀ _ a hP1
  have hB := exteriorProductDedekindCycles_apply_eq_finsum C sX (h ≫ g) n m a₀ b₀ a' hP2
  have hHB : ∀ z, (properPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
      (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
      (n + m - 1) (exteriorProductDedekindCycles C sX (h ≫ g) n m a₀ b₀)).1 z =
      ∑ᶠ x : a₀.1.support, (properPushforward C
        ((dedekindPointFibre sX g x.1).subschemeι ≫ (pullback.fst sX g ≫ sX))
        (pullback.fst sX g ≫ sX) (dedekindPointFibre sX g x.1).subschemeι rfl (n + m - 1)
        (properPushforward C _ _ (properPointFibreMap sX g h x.1)
          (properPointFibreMap_comp_structureMorphism sX g h x.1) (n + m - 1) (a' x))).1 z := by
    intro z
    have hmap := algebraicCycle_map_finsum_apply (bivariantBaseChangeMap sX g h)
      (relativeDimension C.dimensionFunction (pullback.fst sX (h ≫ g) ≫ sX))
      (relativeDimension C.dimensionFunction (pullback.fst sX g ≫ sX))
      (fun x : a₀.1.support ↦ Set.range (dedekindPointFibre sX (h ≫ g) x.1).subschemeι) hfin'
      (fun x ↦ (properPushforward C _ _ (dedekindPointFibre sX (h ≫ g) x.1).subschemeι rfl
        (n + m - 1) (a' x)).1)
      (fun x ↦ support_properPushforward_subset C _ _ _ _ _ _)
      (exteriorProductDedekindCycles C sX (h ≫ g) n m a₀ b₀).1 hB z
    change (properPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
      (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
      (n + m - 1) (exteriorProductDedekindCycles C sX (h ≫ g) n m a₀ b₀)).1 z = _ at hmap
    rw [hmap]
    refine finsum_congr fun x ↦ ?_
    change (properPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
      (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
      (n + m - 1) (properPushforward C _ _ (dedekindPointFibre sX (h ≫ g) x.1).subschemeι rfl
        (n + m - 1) (a' x))).1 z = _
    rw [properPushforward_properPushforward, properPushforward_properPushforward,
      properPushforward_congr C _ _ _ _ (properPointFibreMap_subschemeι sX g h x.1).symm]
  rw [properChowPushforward_mk, eq_comm, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  have hfinz : ∀ e : ∀ x : a₀.1.support, CycleGroup C
      ((dedekindPointFibre sX g x.1).subschemeι ≫ (pullback.fst sX g ≫ sX)) (n + m - 1),
      ∀ z, (Function.support fun x : a₀.1.support ↦ (properPushforward C _
        (pullback.fst sX g ≫ sX) (dedekindPointFibre sX g x.1).subschemeι rfl (n + m - 1)
          (e x)).1 z).Finite := fun e z ↦
    (hfin.point_finite z).subset fun x hx ↦
      support_properPushforward_subset C _ _ _ _ (n + m - 1) (e x) hx
  refine mem_rationalEquivalences_of_finsum_isClosedImmersion (pullback.fst sX g ≫ sX)
    (n + m - 1) (fun x : a₀.1.support ↦ (dedekindPointFibre sX g x.1).subschemeι) hfin
    (fun x ↦ (dedekindPointFibre sX g x.1).subschemeι ≫ (pullback.fst sX g ≫ sX))
    (fun _ ↦ rfl)
    (fun x ↦ properPushforward C _ _ (properPointFibreMap sX g h x.1)
        (properPointFibreMap_comp_structureMorphism sX g h x.1) (n + m - 1) (a' x) - a x)
    (fun x ↦ ?_) _ (fun z ↦ ?_)
  · refine (QuotientAddGroup.eq_zero_iff (N := rationalEquivalences C _ (n + m - 1)) _).1 ?_
    rw [QuotientAddGroup.mk_sub]
    exact sub_eq_zero.2 (hP3 x).symm
  · change (properPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
      (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
      (n + m - 1) (exteriorProductDedekindCycles C sX (h ≫ g) n m a₀ b₀)).1 z -
      (exteriorProductDedekindCycles C sX g n m a₀ (properPushforward C (h ≫ g) g h rfl m b₀)).1 z
        = _
    rw [hHB z, hA z, ← finsum_sub_distrib (hfinz _ z) (hfinz a z)]
    refine finsum_congr fun x ↦ ?_
    rw [properPushforward_sub]
    rfl

include hC in
/-- **The exterior product over a Dedekind base commutes with proper pushforward in the second
variable.** For a proper `h : T' ⟶ T`, `α ∈ CH_n(X)` and `β ∈ CH_m(T')`,
`α × h_* β = (1 × h)_* (α × β)` in `CH_{n+m-1}(X ×_S T)`. -/
theorem exteriorProductDedekindChowTensor_properChowPushforward (α : chowGroup C sX n)
    (β : chowGroup C (h ≫ g) m) :
    exteriorProductDedekindChowTensor C sX g n m hC
        (α ⊗ₜ[ℤ] properChowPushforward C (h ≫ g) g h rfl m (properPushforwardDescends C _ _ _ _ _)
          β) =
      properChowPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
        (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h)
        (n + m - 1) (properPushforwardDescends C _ _ _ _ _)
        (exteriorProductDedekindChowTensor C sX (h ≫ g) n m hC (α ⊗ₜ[ℤ] β)) := by
  obtain ⟨a₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX n) α
  obtain ⟨b₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C (h ≫ g) m) β
  rw [properChowPushforward_mk, exteriorProductDedekindChowTensor_tmul_mk,
    exteriorProductDedekindChowTensor_tmul_mk]
  exact exteriorProductDedekindCycles_properPushforward hC sX g h n m a₀ b₀

end Main

end Stacks.Chow

end
