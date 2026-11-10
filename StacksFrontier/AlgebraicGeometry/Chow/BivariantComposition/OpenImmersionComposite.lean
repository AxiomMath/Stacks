module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClassOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# Composing a bivariant class with flat pullback along an open immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `j : U ⟶ X` be an open
immersion and `i' : Z ⟶ U` a morphism of schemes locally of finite type over `S`. A bivariant class
`c ∈ A^p(Z ⟶ U)` composes (Stacks 0B75) with the flat-pullback class `j^* ∈ A^0(U ⟶ X)` of Stacks
0B78 to a class `c ∘ j^* ∈ A^p(Z ⟶ X)`. This is the shape of the definition of Stacks 0FBQ (3),
`c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`.

The source asserts that the result does not depend on the choice of `U`. The general fact behind
it is proved here: if `ι : V ⟶ U` is an open immersion through which `i'` factors, and
`c_V ∈ A^p(Z ⟶ V)` is the restriction of `c_U ∈ A^p(Z ⟶ U)` to `V` — on every test scheme over `V`
it caps as `c_U` does — then `c_U ∘ (U ⟶ X)^* = c_V ∘ (V ⟶ X)^*`.

## Main definitions

* `Stacks.Chow.openImmersionComposite` — the composite `c ∘ j^*`.
* `Stacks.Chow.IsOpenRestriction` — `c_V` caps on test schemes over `V` as `c_U` does.

## Main results

* `Stacks.Chow.openImmersionComposite_cap_heq` — `(c ∘ j^*) ∩ α = c ∩ (α|_{U ×_X T})`, read
  through the associativity isomorphism of pullbacks.
* `Stacks.Chow.openImmersionComposite_heq_of_isOpenRestriction` — the composite does not change
  when `U` is shrunk to an open `V` through which `i'` factors, and `c_U` to its restriction.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Bivariant classes for equal morphisms -/

section HEq

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Two bivariant classes for equal morphisms `f = f'` are the same class as soon as their cap
operations agree, read through the identification `X ×_{f,Y} T ≅ X ×_{f',Y} T`. -/
theorem BivariantClass.heq_of_cap_eq {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') {hf : f ≫ sY = sX} {hf' : f' ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) (c' : BivariantClass C G sX sY f' hf' p)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sY) k),
      chowPushforwardOfIso C (pullback.fst f t ≫ sX) (pullback.fst f' t ≫ sX)
          (pullback.congrHom hff rfl).hom (by simp) (k - p) (c.cap t k α) =
        c'.cap t k α) :
    c ≍ c' := by
  subst hff
  refine heq_of_eq (BivariantClass.ext C G sX sY f hf p ?_)
  intro T t _ k α
  rw [← h t k α, chowPushforwardOfIso_congr_apply C _ _ (pullback.congrHom rfl rfl).hom (𝟙 _)
    (by simp) _ (Category.id_comp _), chowPushforwardOfIso_id]

end HEq

/-! ### Pullback bookkeeping -/

section Bookkeeping

variable {C : ChowSituation.{u}} {Z N W W' : Scheme.{u}} (sZ : Z ⟶ C.S) (i : Z ⟶ N)

/-- The base change `W' ×_N Z ⟶ W ×_N Z` of test schemes along `m : W' ⟶ W` is compatible with
the projections to `Z`. -/
private theorem bivariantBaseChangeMap_hom_comp_fst (q : W ⟶ N) (m : W' ⟶ W) :
    bivariantBaseChangeMap i q m ≫ pullback.fst i q = pullback.fst i (m ≫ q) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change `W' ×_N Z ⟶ W ×_N Z` of test schemes along `m : W' ⟶ W` carries the
projection to `W` to the projection to `W'` followed by `m`. -/
private theorem bivariantBaseChangeMap_hom_comp_snd (q : W ⟶ N) (m : W' ⟶ W) :
    bivariantBaseChangeMap i q m ≫ pullback.snd i q = pullback.snd i (m ≫ q) ≫ m :=
  pullback.lift_snd _ _ _

/-- The base change `W' ×_N Z ⟶ W ×_N Z` of test schemes lies over the base. -/
private theorem bivariantBaseChangeMap_hom_comp_fst_comp (q : W ⟶ N) (m : W' ⟶ W) :
    bivariantBaseChangeMap i q m ≫ (pullback.fst i q ≫ sZ) = pullback.fst i (m ≫ q) ≫ sZ := by
  rw [← Category.assoc]
  exact congrArg (· ≫ sZ) (bivariantBaseChangeMap_hom_comp_fst i q m)

/-- The comparison `Z ×_{g₁} W ≅ Z ×_{g₂} W` of the base changes of `i` along two equal morphisms
is compatible with the projections to `Z`. -/
private theorem congrHom_rfl_hom_comp_fst {g₁ g₂ : W ⟶ N} (he : g₁ = g₂) :
    (pullback.congrHom (rfl : i = i) he).hom ≫ pullback.fst i g₂ = pullback.fst i g₁ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The comparison `Z ×_{g₁} W ≅ Z ×_{g₂} W` of the base changes of `i` along two equal morphisms
is compatible with the projections to `W`. -/
private theorem congrHom_rfl_hom_comp_snd {g₁ g₂ : W ⟶ N} (he : g₁ = g₂) :
    (pullback.congrHom (rfl : i = i) he).hom ≫ pullback.snd i g₂ = pullback.snd i g₁ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The comparison `Z ×_{g₁} W ≅ Z ×_{g₂} W` of the base changes of `i` along two equal morphisms
lies over the base. -/
private theorem congrHom_rfl_hom_comp_fst_comp {g₁ g₂ : W ⟶ N} (he : g₁ = g₂) :
    (pullback.congrHom (rfl : i = i) he).hom ≫ (pullback.fst i g₂ ≫ sZ) =
      pullback.fst i g₁ ≫ sZ := by
  rw [← Category.assoc]
  exact congrArg (· ≫ sZ) (congrHom_rfl_hom_comp_fst i he)

end Bookkeeping

section Composite

variable (C : ChowSituation.{u}) {Z U X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ U) [LocallyOfFiniteType i] (j : U ⟶ X) [IsOpenImmersion j]
  (hi : i ≫ sU = sZ) (hj : j ≫ sX = sU) (p : ℤ)

/-- **The composite `c ∘ j^*`** of a bivariant class `c ∈ A^p(Z ⟶ U)` with the flat-pullback
class `j^* ∈ A^0(U ⟶ X)` of an open immersion (Stacks 0B78), at the Gysin system of the first
Chern class rule (Stacks 0B75). -/
abbrev openImmersionComposite (c : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj) (p + -((0 : ℕ) : ℤ)) :=
  bivariantCompositeOfInvertible C sZ sU sX i j hi hj p (-((0 : ℕ) : ℤ)) c
    (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sU sX j hj)

/-- **The cap operation of `c ∘ j^*`.** On a test scheme `t : T ⟶ X` it restricts a class on `T`
to the open subscheme `U ×_X T`, caps with `c` there, and pushes the result forward along the
associativity isomorphism `Z ×_U (U ×_X T) ≅ Z ×_X T`. The degree is written `k - p` here and
`k - (p + -0)` in the class, whence the heterogeneous equality. -/
theorem openImmersionComposite_cap_heq
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (openImmersionComposite C sZ sU sX i j hi hj p c).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i (pullback.fst j t) ≫ sZ)
        (pullback.fst (i ≫ j) t ≫ sZ) (pullbackRightPullbackFstIso j t i).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i j t) (k - p)
        (c.cap (pullback.fst j t) k
          (chowGroupRestrict C (t ≫ sX) (pullback.fst j t ≫ sU) (pullback.snd j t)
            (pullbackSnd_comp_structureMorphism hj t) k α)) := by
  have hdeg : k - -((0 : ℕ) : ℤ) = k := by simp
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  rw [bivariantCompositeCap_apply]
  refine properChowPushforward_heq_congr C _ _ _ _ (by rw [hdeg]) _ _ _ _ ?_
  refine heq_cap_of_heq C (gysinSystemOfInvertible C) sZ sU i hi p c (pullback.fst j t) hdeg ?_
  exact flatPullbackBivariantCap_heq_chowGroupRestrict C sU sX j hj t k α

end Composite

/-! ### Shrinking the open subscheme -/

section Shrink

variable (C : ChowSituation.{u}) {Z U V X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ U) [LocallyOfFiniteType i] (iV : Z ⟶ V) [LocallyOfFiniteType iV]
  (j : U ⟶ X) [IsOpenImmersion j] (jV : V ⟶ X) [IsOpenImmersion jV]
  (ι : V ⟶ U) [IsOpenImmersion ι]
  (hi : i ≫ sU = sZ) (hiV : iV ≫ sV = sZ) (hj : j ≫ sX = sU) (hjV : jV ≫ sX = sV)
  (hι : ι ≫ sU = sV) (hιi : iV ≫ ι = i) (hιj : ι ≫ j = jV) (p : ℤ)

include hιi in
/-- For a test scheme `t : T ⟶ V`, the base change of `iV : Z ⟶ V` along `t` is the base change of
`i = iV ≫ ι : Z ⟶ U` along `t ≫ ι`, the open immersion `ι` being a monomorphism. -/
def openRestrictionPullbackIso {T : Scheme.{u}} (t : T ⟶ V) :
    pullback iV t ≅ pullback i (t ≫ ι) where
  hom := pullback.map iV t i (t ≫ ι) (𝟙 Z) (𝟙 T) ι (by simp [hιi]) (by simp)
  inv := pullback.lift (f := iV) (g := t) (pullback.fst i (t ≫ ι)) (pullback.snd i (t ≫ ι)) (by
    rw [← cancel_mono ι, Category.assoc, hιi, pullback.condition, Category.assoc])
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id,
      Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id,
      Category.id_comp])
  inv_hom_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id,
      Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp])

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType i] [LocallyOfFiniteType iV] in
include hιi in
/-- The first projection to `Z` is unchanged by the identification `Z ×_V T ≅ Z ×_U T`. -/
theorem openRestrictionPullbackIso_hom_fst {T : Scheme.{u}} (t : T ⟶ V) :
    (openRestrictionPullbackIso i iV ι hιi t).hom ≫ pullback.fst i (t ≫ ι) = pullback.fst iV t := by
  rw [openRestrictionPullbackIso, pullback.lift_fst, Category.comp_id]

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType i] [LocallyOfFiniteType iV] in
include hιi in
/-- The second projection to `T` is unchanged by the identification `Z ×_V T ≅ Z ×_U T`. -/
theorem openRestrictionPullbackIso_hom_snd {T : Scheme.{u}} (t : T ⟶ V) :
    (openRestrictionPullbackIso i iV ι hιi t).hom ≫ pullback.snd i (t ≫ ι) = pullback.snd iV t := by
  rw [openRestrictionPullbackIso, pullback.lift_snd, Category.comp_id]

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType i] [LocallyOfFiniteType iV] in
include hιi in
/-- The identification `Z ×_V T ≅ Z ×_U T` lies over the base. -/
theorem openRestrictionPullbackIso_hom_comp_fst_comp {T : Scheme.{u}} (t : T ⟶ V) :
    (openRestrictionPullbackIso i iV ι hιi t).hom ≫ (pullback.fst i (t ≫ ι) ≫ sZ) =
      pullback.fst iV t ≫ sZ := by
  rw [← Category.assoc, openRestrictionPullbackIso_hom_fst]

/-- **`c_V` is the restriction of `c_U` to `V`.** For an open immersion `ι : V ⟶ U` through which
`i : Z ⟶ U` factors as `iV ≫ ι`, a class `c_V ∈ A^p(Z ⟶ V)` restricts `c_U ∈ A^p(Z ⟶ U)` when, on
every test scheme `t : T ⟶ V`, capping with `c_V` is capping with `c_U` at `t ≫ ι`, read through
the identification `Z ×_V T ≅ Z ×_U T` of `Stacks.Chow.openRestrictionPullbackIso`.

This is the cap formula `res(c) ∩ α = c ∩ α` of the restriction of Stacks 0F9Z along `ι`, with the
base change `Z ×_U V` of `i` identified with `Z`. -/
def IsOpenRestriction (cU : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p)
    (cV : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV hiV p) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ V) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sV) k),
    chowPushforwardOfIso C (pullback.fst iV t ≫ sZ) (pullback.fst i (t ≫ ι) ≫ sZ)
        (openRestrictionPullbackIso i iV ι hιi t).hom
        (by rw [← Category.assoc, openRestrictionPullbackIso_hom_fst]) (k - p) (cV.cap t k α) =
      cU.cap (t ≫ ι) k (chowGroupCongr C (by rw [Category.assoc, hι]) k α)

/-- For a test scheme `t : T ⟶ X`, the open immersion `V ×_X T ⟶ U ×_X T` induced by `ι`. -/
abbrev openShrinkTestMap {T : Scheme.{u}} (t : T ⟶ X) : pullback jV t ⟶ pullback j t :=
  pullback.map jV t j t ι (𝟙 T) (𝟙 X) (by rw [Category.comp_id, hιj]) (by simp)

omit [IsOpenImmersion j] [IsOpenImmersion jV] [IsOpenImmersion ι] in
include hιj in
/-- Composing `V ×_X T ⟶ U ×_X T` with the first projection to `U` is the first projection to `V`
followed by `ι`. -/
theorem openShrinkTestMap_fst {T : Scheme.{u}} (t : T ⟶ X) :
    openShrinkTestMap j jV ι hιj t ≫ pullback.fst j t = pullback.fst jV t ≫ ι := by
  rw [pullback.lift_fst]

omit [IsOpenImmersion j] [IsOpenImmersion jV] [IsOpenImmersion ι] in
include hιj in
/-- The map `V ×_X T ⟶ U ×_X T` commutes with the second projections to `T`. -/
theorem openShrinkTestMap_snd {T : Scheme.{u}} (t : T ⟶ X) :
    openShrinkTestMap j jV ι hιj t ≫ pullback.snd j t = pullback.snd jV t := by
  rw [pullback.lift_snd, Category.comp_id]

omit [IsOpenImmersion j] [IsOpenImmersion jV] [IsOpenImmersion ι] in
include hιj in
/-- The square `V ×_X T ⟶ U ×_X T` over `ι : V ⟶ U` is cartesian. -/
theorem isPullback_openShrinkTestMap {T : Scheme.{u}} (t : T ⟶ X) :
    IsPullback (pullback.fst jV t) (openShrinkTestMap j jV ι hιj t) ι (pullback.fst j t) := by
  refine IsPullback.flip (IsPullback.of_right ?_ (openShrinkTestMap_fst j jV ι hιj t)
    (IsPullback.of_hasPullback j t).flip)
  rw [openShrinkTestMap_snd, hιj]
  exact (IsPullback.of_hasPullback jV t).flip

/-- Being a base change of the open immersion `ι`, the map `V ×_X T ⟶ U ×_X T` is an open
immersion. -/
instance isOpenImmersion_openShrinkTestMap {T : Scheme.{u}} (t : T ⟶ X) :
    IsOpenImmersion (openShrinkTestMap j jV ι hιj t) :=
  MorphismProperty.of_isPullback (isPullback_openShrinkTestMap j jV ι hιj t)
    (P := @IsOpenImmersion) inferInstance

omit [LocallyOfFiniteType i] [LocallyOfFiniteType iV] [IsOpenImmersion j] [IsOpenImmersion jV] in
include hιi hιj in
/-- **`Z ×_U (V ×_X T) = Z ×_U (U ×_X T)`.** Since `i` factors through `V`, the base change of `i`
along `V ×_X T ⟶ U ×_X T ⟶ U` is all of the base change along `U ×_X T ⟶ U`: the induced open
immersion is an isomorphism. Its inverse sends a point to itself, read in `V ×_X T` through
`iV`. -/
theorem isIso_bivariantBaseChangeMap_openShrinkTestMap {T : Scheme.{u}} (t : T ⟶ X) :
    IsIso (bivariantBaseChangeMap i (pullback.fst j t) (openShrinkTestMap j jV ι hιj t)) := by
  set m := openShrinkTestMap j jV ι hιj t with hm
  have hmf := openShrinkTestMap_fst j jV ι hιj t
  have hms := openShrinkTestMap_snd j jV ι hιj t
  rw [← hm] at hmf hms
  have hn : (pullback.fst i (pullback.fst j t) ≫ iV) ≫ jV =
      (pullback.snd i (pullback.fst j t) ≫ pullback.snd j t) ≫ t := by
    rw [← hιj, Category.assoc, ← Category.assoc iV, hιi, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, pullback.condition]
  set n : pullback i (pullback.fst j t) ⟶ pullback jV t := pullback.lift _ _ hn
  have hnf : n ≫ pullback.fst jV t = pullback.fst i (pullback.fst j t) ≫ iV :=
    pullback.lift_fst _ _ _
  have hns : n ≫ pullback.snd jV t = pullback.snd i (pullback.fst j t) ≫ pullback.snd j t :=
    pullback.lift_snd _ _ _
  have hnm : n ≫ m = pullback.snd i (pullback.fst j t) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hmf, ← Category.assoc, hnf, Category.assoc, hιi, pullback.condition]
    · rw [Category.assoc, hms, hns]
  have hw : pullback.fst i (pullback.fst j t) ≫ i = n ≫ (m ≫ pullback.fst j t) := by
    rw [← Category.assoc, hnm, pullback.condition]
  refine ⟨⟨pullback.lift (f := i) (g := m ≫ pullback.fst j t) _ _ hw, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp, bivariantBaseChangeMap,
        pullback.map, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hnf, ← cancel_mono ι]
        simp only [bivariantBaseChangeMap, pullback.map, Category.assoc, pullback.lift_fst_assoc,
          Category.comp_id, hιi, pullback.condition, hmf]
      · rw [Category.assoc, hns]
        simp only [bivariantBaseChangeMap, pullback.map, Category.assoc, pullback.lift_snd_assoc,
          hms]
  · refine pullback.hom_ext ?_ ?_
    · simp only [bivariantBaseChangeMap, pullback.map, Category.assoc, pullback.lift_fst,
        Category.comp_id, Category.id_comp]
    · simp only [bivariantBaseChangeMap, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, hnm, Category.id_comp]

/-- Restriction of Chow classes along open immersions depends on its open immersion and on the
structure morphism of its target only up to equality. -/
theorem chowGroupRestrict_heq_congr {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB sB' : B ⟶ C.S) [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (v v' : B ⟶ A)
    [IsOpenImmersion v] [IsOpenImmersion v'] (hv : v ≫ sA = sB) (hv' : v' ≫ sA = sB')
    (hvv' : v = v') (k : ℤ) (α : chowGroup C sA k) :
    chowGroupRestrict C sA sB v hv k α ≍ chowGroupRestrict C sA sB' v' hv' k α := by
  subst hvv'
  obtain rfl : sB = sB' := hv.symm.trans hv'
  rfl

/-- **Capping with `c_U` is determined by capping with its restriction `c_V`.** If an open immersion
`φ : W' ⟶ W` over `ι` induces an isomorphism on the base changes of `i`, and `γ ∈ A_k(W)` restricts
along `φ` to `γ' ∈ A_k(W')`, then `c_U ∩ γ` is the pushforward of `c_V ∩ γ'` along the chain
`Z ×_V W' ≅ Z ×_U W' ≅ Z ×_U W`. -/
private theorem cap_eq_pushforward_of_isOpenRestriction
    (cU : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p)
    (cV : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV hiV p)
    (H : IsOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p cU cV) {W W' : Scheme.{u}}
    (g : W ⟶ U) [LocallyOfFiniteType g] (s : W' ⟶ V) [LocallyOfFiniteType s] (φ : W' ⟶ W)
    [IsOpenImmersion φ] (hφf : φ ≫ g = s ≫ ι) [IsIso (bivariantBaseChangeMap i g φ)] (k : ℤ)
    (γ : chowGroup C (g ≫ sU) k) (γ' : chowGroup C (s ≫ sV) k)
    (h₂ : s ≫ sV = (φ ≫ g) ≫ sU)
    (h3 : chowGroupRestrict C (g ≫ sU) ((φ ≫ g) ≫ sU) φ (Category.assoc _ _ _).symm k γ =
      chowGroupCongr C h₂ k γ') :
    cU.cap g k γ =
      chowPushforwardOfIso C _ _ (bivariantBaseChangeMap i g φ)
          (bivariantBaseChangeMap_hom_comp_fst_comp sZ i g φ) (k - p)
        (chowPushforwardOfIso C _ _ (pullback.congrHom (rfl : i = i) hφf.symm).hom
            (congrHom_rfl_hom_comp_fst_comp sZ i hφf.symm) (k - p)
          (chowPushforwardOfIso C _ _ (openRestrictionPullbackIso i iV ι hιi s).hom
              (openRestrictionPullbackIso_hom_comp_fst_comp C sZ i iV ι hιi s) (k - p)
            (cV.cap s k γ'))) := by
  have hb := bivariantBaseChangeMap_hom_comp_fst_comp sZ i g φ
  rw [H s k γ', chowPushforwardOfIso_congrHom_cap C (gysinSystemOfInvertible C) sZ sU i hi p cU
      hφf.symm (congrHom_rfl_hom_comp_fst_comp sZ i hφf.symm) k γ' _ h₂, ← h3,
    ← BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sZ sU i hi p cU g φ _ rfl
      (bivariantBaseChangeMap i g φ) (isPullback_bivariantBaseChangeMap i g φ)
      (bivariantBaseChangeMap_hom_comp_fst i g φ) k _ hb γ]
  exact eq_chowPushforwardOfIso_chowGroupRestrict C _ _ _ hb (k - p) _

/-- **The cap product of `c_U` with the restriction of `α` to `U ×_X T`.**  It is the cap product
of `c_V` with the restriction of `α` to `V ×_X T`, pushed forward along the chain of
identifications `Z ×_V (V ×_X T) ≅ Z ×_U (V ×_X T) ≅ Z ×_U (U ×_X T)`: the class
`c_U ∩ (α|_{U ×_X T})` is determined by its restriction to the open subscheme `Z ×_U (V ×_X T)`,
which is all of `Z ×_U (U ×_X T)` because `i` factors through `V`, and that restriction is
`c_V ∩ (α|_{V ×_X T})` by hypothesis. -/
private theorem openShrink_cap_chowGroupRestrict_eq
    (cU : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p)
    (cV : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV hiV p)
    (H : IsOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p cU cV) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k)
    [IsIso (bivariantBaseChangeMap i (pullback.fst j t) (openShrinkTestMap j jV ι hιj t))] :
    cU.cap (pullback.fst j t) k
        (chowGroupRestrict C (t ≫ sX) (pullback.fst j t ≫ sU) (pullback.snd j t)
          (pullbackSnd_comp_structureMorphism hj t) k α) =
      chowPushforwardOfIso C _ _
          (bivariantBaseChangeMap i (pullback.fst j t) (openShrinkTestMap j jV ι hιj t))
          (bivariantBaseChangeMap_hom_comp_fst_comp sZ i (pullback.fst j t)
            (openShrinkTestMap j jV ι hιj t)) (k - p)
        (chowPushforwardOfIso C _ _
            (pullback.congrHom (rfl : i = i) (openShrinkTestMap_fst j jV ι hιj t).symm).hom
            (congrHom_rfl_hom_comp_fst_comp sZ i (openShrinkTestMap_fst j jV ι hιj t).symm)
            (k - p)
          (chowPushforwardOfIso C _ _
              (openRestrictionPullbackIso i iV ι hιi (pullback.fst jV t)).hom
              (openRestrictionPullbackIso_hom_comp_fst_comp C sZ i iV ι hιi (pullback.fst jV t))
              (k - p)
            (cV.cap (pullback.fst jV t) k
              (chowGroupRestrict C (t ≫ sX) (pullback.fst jV t ≫ sV) (pullback.snd jV t)
                (pullbackSnd_comp_structureMorphism hjV t) k α)))) := by
  have hms := openShrinkTestMap_snd j jV ι hιj t
  have h₂ : pullback.fst jV t ≫ sV =
      (openShrinkTestMap j jV ι hιj t ≫ pullback.fst j t) ≫ sU := by
    rw [openShrinkTestMap_fst j jV ι hιj t, Category.assoc, hι]
  refine cap_eq_pushforward_of_isOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p cU cV H
    (pullback.fst j t) (pullback.fst jV t) (openShrinkTestMap j jV ι hιj t)
    (openShrinkTestMap_fst j jV ι hιj t) k _ _ h₂ ?_
  refine eq_of_heq ((heq_of_eq (chowGroupRestrict_comp C (t ≫ sX) (pullback.fst j t ≫ sU)
    (pullback.snd j t) (pullbackSnd_comp_structureMorphism hj t) k _
    (openShrinkTestMap j jV ι hιj t) _ α)).trans ?_)
  refine (chowGroupRestrict_heq_congr C (t ≫ sX)
    ((openShrinkTestMap j jV ι hιj t ≫ pullback.fst j t) ≫ sU) (pullback.fst jV t ≫ sV)
    (openShrinkTestMap j jV ι hιj t ≫ pullback.snd j t) (pullback.snd jV t) _
    (pullbackSnd_comp_structureMorphism hjV t) hms k α).trans ?_
  exact (chowGroupCongr_heq C h₂ k _).symm

/-- **Shrinking `U` does not change `c ∘ (U ⟶ X)^*`.** Let `ι : V ⟶ U` be an open immersion
through which `i : Z ⟶ U` factors as `iV ≫ ι`, with `ι ≫ j = jV`, and let `c_V ∈ A^p(Z ⟶ V)` be
the restriction of `c_U ∈ A^p(Z ⟶ U)` in the sense of `Stacks.Chow.IsOpenRestriction`. Then
`c_U ∘ j^* = c_V ∘ jV^*`, as bivariant classes for the morphism `i ≫ j = iV ≫ jV`.

On a test scheme `T ⟶ X`, both sides cap a class by restricting it to an open subscheme of `T`
and capping there; the class `c_U ∩ (α|_{U ×_X T})` is determined by its restriction to the open
subscheme `Z ×_U (V ×_X T)`, which is all of `Z ×_U (U ×_X T)` because `i` factors through `V`
(`Stacks.Chow.isIso_bivariantBaseChangeMap_openShrinkTestMap`), and that restriction is
`c_U ∩ (α|_{V ×_X T})` by the flat-pullback axiom of `c_U` along the open immersion
`V ×_X T ⟶ U ×_X T` (`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`), which is
`c_V ∩ (α|_{V ×_X T})` by hypothesis. -/
theorem openImmersionComposite_heq_of_isOpenRestriction (hιj : ι ≫ j = jV)
    (cU : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p)
    (cV : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV hiV p)
    (H : IsOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p cU cV) :
    openImmersionComposite C sZ sU sX i j hi hj p cU ≍
      openImmersionComposite C sZ sV sX iV jV hiV hjV p cV := by
  have hcomp : i ≫ j = iV ≫ jV := by rw [← hιi, ← hιj, Category.assoc]
  refine BivariantClass.heq_of_cap_eq hcomp _ _ ?_
  intro T t _ k α
  have hdeg : k - (p + -((0 : ℕ) : ℤ)) = k - p := by simp
  have hms := openShrinkTestMap_snd j jV ι hιj t
  have := isIso_bivariantBaseChangeMap_openShrinkTestMap i iV j jV ι hιi hιj t
  refine eq_of_heq ?_
  refine (properChowPushforward_heq_congr C (pullback.fst (i ≫ j) t ≫ sZ)
    (pullback.fst (iV ≫ jV) t ≫ sZ) (pullback.congrHom hcomp rfl).hom (by simp) hdeg
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _ _
    (openImmersionComposite_cap_heq C sZ sU sX i j hi hj p cU t k α)).trans ?_
  refine HEq.trans (heq_of_eq ?_)
    (openImmersionComposite_cap_heq C sZ sV sX iV jV hiV hjV p cV t k α).symm
  rw [openShrink_cap_chowGroupRestrict_eq C sZ sU sV sX i iV j jV ι hi hiV hj hjV hι hιi hιj p
      cU cV H t k α,
    properChowPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - p) _
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.congrHom, pullback.map, pullback.lift_fst,
      Category.comp_id, pullbackRightPullbackFstIso_hom_fst, bivariantBaseChangeMap,
      openRestrictionPullbackIso_hom_fst, asIso_hom]
  · simp only [Category.assoc, pullback.congrHom, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackRightPullbackFstIso_hom_snd, bivariantBaseChangeMap,
      pullback.lift_snd_assoc, asIso_hom, hms]
    rw [← Category.assoc, openRestrictionPullbackIso_hom_snd]

end Shrink

/-! ### Restriction of `c ∘ j^*` along an open immersion -/

section RestrictComposite

variable (C : ChowSituation.{u}) {Z N N' U V : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (sN' : N' ⟶ C.S) [LocallyOfFiniteType sN']
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (i : Z ⟶ N) [LocallyOfFiniteType i] (i' : Z ⟶ N') [LocallyOfFiniteType i']
  (j : N ⟶ U) [IsOpenImmersion j] (j' : N' ⟶ V) [IsOpenImmersion j']
  (κ : V ⟶ U) [IsOpenImmersion κ] (ιN : N' ⟶ N) [IsOpenImmersion ιN]
  (hi : i ≫ sN = sZ) (hi' : i' ≫ sN' = sZ) (hj : j ≫ sU = sN) (hj' : j' ≫ sV = sN')
  (hκ : κ ≫ sU = sV) (hιN : ιN ≫ sN = sN') (hii : i' ≫ ιN = i)
  (sq : IsPullback ιN j' j κ) (p : ℤ)

omit [LocallyOfFiniteType i] [LocallyOfFiniteType i'] [IsOpenImmersion j] [IsOpenImmersion j']
  [IsOpenImmersion κ] [IsOpenImmersion ιN] in
include hii sq in
/-- The factorization `(i' ≫ j') ≫ κ = i ≫ j` of the two composites. -/
theorem openImmersionComposite_comp_eq_of_isPullback : (i' ≫ j') ≫ κ = i ≫ j := by
  rw [Category.assoc, ← sq.w, ← Category.assoc, hii]

/-- **The cap product of `c` with the restriction of `α` to `N ×_U T`.**  It is the cap product of
`c'` with the restriction of `α` to `N' ×_V T`, pushed forward along the chain of identifications
`Z ×_{N'} (N' ×_V T) ≅ Z ×_N (N' ×_V T) ≅ Z ×_N (N ×_U T)`, the comparison `φ` of the two readings
`N' ×_V T = N ×_U T` of the test scheme being an isomorphism. -/
private theorem restrictComposite_cap_chowGroupRestrict_eq
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sN i hi p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sN' i' hi' p)
    (H : IsOpenRestriction C sZ sN sN' i i' ιN hi hi' hιN hii p c c') {T : Scheme.{u}}
    (t : T ⟶ V) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sV) k)
    (hακ : t ≫ sV = (t ≫ κ) ≫ sU) (φ : pullback j' t ⟶ pullback j (t ≫ κ))
    [IsOpenImmersion φ] (hφf : φ ≫ pullback.fst j (t ≫ κ) = pullback.fst j' t ≫ ιN)
    (hφs : φ ≫ pullback.snd j (t ≫ κ) = pullback.snd j' t)
    [IsIso (bivariantBaseChangeMap i (pullback.fst j (t ≫ κ)) φ)] :
    c.cap (pullback.fst j (t ≫ κ)) k
        (chowGroupRestrict C ((t ≫ κ) ≫ sU) (pullback.fst j (t ≫ κ) ≫ sN)
          (pullback.snd j (t ≫ κ)) (pullbackSnd_comp_structureMorphism hj (t ≫ κ)) k
          (chowGroupCongr C hακ k α)) =
      chowPushforwardOfIso C _ _ (bivariantBaseChangeMap i (pullback.fst j (t ≫ κ)) φ)
          (bivariantBaseChangeMap_hom_comp_fst_comp sZ i (pullback.fst j (t ≫ κ)) φ) (k - p)
        (chowPushforwardOfIso C _ _ (pullback.congrHom (rfl : i = i) hφf.symm).hom
            (congrHom_rfl_hom_comp_fst_comp sZ i hφf.symm) (k - p)
          (chowPushforwardOfIso C _ _
              (openRestrictionPullbackIso i i' ιN hii (pullback.fst j' t)).hom
              (openRestrictionPullbackIso_hom_comp_fst_comp C sZ i i' ιN hii (pullback.fst j' t))
              (k - p)
            (c'.cap (pullback.fst j' t) k
              (chowGroupRestrict C (t ≫ sV) (pullback.fst j' t ≫ sN') (pullback.snd j' t)
                (pullbackSnd_comp_structureMorphism hj' t) k α)))) := by
  have h₂ : pullback.fst j' t ≫ sN' = (φ ≫ pullback.fst j (t ≫ κ)) ≫ sN := by
    rw [hφf, Category.assoc, hιN]
  refine cap_eq_pushforward_of_isOpenRestriction C sZ sN sN' i i' ιN hi hi' hιN hii p c c' H
    (pullback.fst j (t ≫ κ)) (pullback.fst j' t) φ hφf k _ _ h₂ ?_
  have hv1 : (φ ≫ pullback.snd j (t ≫ κ)) ≫ (t ≫ sV) = (φ ≫ pullback.fst j (t ≫ κ)) ≫ sN := by
    rw [hφs, pullbackSnd_comp_structureMorphism hj' t, hφf, Category.assoc, hιN]
  rw [chowGroupRestrict_comp, chowGroupRestrict_chowGroupCongr C (t ≫ sV) _ _ _ hv1]
  refine eq_of_heq ((chowGroupRestrict_heq_congr C (t ≫ sV) _ (pullback.fst j' t ≫ sN')
    (φ ≫ pullback.snd j (t ≫ κ)) (pullback.snd j' t) hv1
    (pullbackSnd_comp_structureMorphism hj' t) hφs k α).trans ?_)
  exact (chowGroupCongr_heq C h₂ k _).symm

/-- **Restriction commutes with composing with flat pullback along an open immersion.** Let
`N' = N ×_U V` for open immersions `j : N ⟶ U` and `κ : V ⟶ U`, and let `c' ∈ A^p(Z ⟶ N')` be
the restriction of `c ∈ A^p(Z ⟶ N)` along `N' ⟶ N` (`Stacks.Chow.IsOpenRestriction`). Then
`c' ∘ j'^*` is the restriction of `c ∘ j^*` along `κ`. -/
theorem isOpenRestriction_openImmersionComposite
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sN i hi p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sN' i' hi' p)
    (H : IsOpenRestriction C sZ sN sN' i i' ιN hi hi' hιN hii p c c') :
    IsOpenRestriction C sZ sU sV (i ≫ j) (i' ≫ j') κ (comp_comp_structureMorphism_eq hi hj)
      (comp_comp_structureMorphism_eq hi' hj') hκ
      (openImmersionComposite_comp_eq_of_isPullback i i' j j' κ ιN hii sq) (p + -((0 : ℕ) : ℤ))
      (openImmersionComposite C sZ sN sU i j hi hj p c)
      (openImmersionComposite C sZ sN' sV i' j' hi' hj' p c') := by
  intro T t _ k α
  have hdeg : k - (p + -((0 : ℕ) : ℤ)) = k - p := by simp
  -- the identification `N' ×_V T = N ×_U T`
  have sqT : IsPullback (pullback.fst j' t ≫ ιN) (pullback.snd j' t) j (t ≫ κ) :=
    (IsPullback.of_hasPullback j' t).paste_horiz sq
  set φ := sqT.isoPullback.hom
  have hφf : φ ≫ pullback.fst j (t ≫ κ) = pullback.fst j' t ≫ ιN := sqT.isoPullback_hom_fst
  have hφs : φ ≫ pullback.snd j (t ≫ κ) = pullback.snd j' t := sqT.isoPullback_hom_snd
  have : IsIso (bivariantBaseChangeMap i (pullback.fst j (t ≫ κ)) φ) := by
    unfold bivariantBaseChangeMap; infer_instance
  refine eq_of_heq ?_
  refine (properChowPushforward_heq_congr C (pullback.fst (i' ≫ j') t ≫ sZ)
    (pullback.fst (i ≫ j) (t ≫ κ) ≫ sZ)
    (openRestrictionPullbackIso (i ≫ j) (i' ≫ j') κ
      (openImmersionComposite_comp_eq_of_isPullback i i' j j' κ ιN hii sq) t).hom
    (by rw [← Category.assoc, openRestrictionPullbackIso_hom_fst]) hdeg
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _ _
    (openImmersionComposite_cap_heq C sZ sN' sV i' j' hi' hj' p c' t k α)).trans ?_
  refine HEq.trans (heq_of_eq ?_)
    (openImmersionComposite_cap_heq C sZ sN sU i j hi hj p c (t ≫ κ) k _).symm
  rw [restrictComposite_cap_chowGroupRestrict_eq C sZ sN sN' sU sV i i' j j' κ ιN hi hi' hj hj'
      hιN hii p c c' H t k α (by rw [Category.assoc, hκ]) φ hφf hφs,
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - p) _
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
      openRestrictionPullbackIso_hom_fst]
    exact ((congrArg ((openRestrictionPullbackIso i i' ιN hii (pullback.fst j' t)).hom ≫ ·)
        ((congrArg ((pullback.congrHom (rfl : i = i) hφf.symm).hom ≫ ·)
            (bivariantBaseChangeMap_hom_comp_fst i (pullback.fst j (t ≫ κ)) φ)).trans
          (congrHom_rfl_hom_comp_fst i hφf.symm))).trans
      (openRestrictionPullbackIso_hom_fst i i' ιN hii (pullback.fst j' t))).symm
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      openRestrictionPullbackIso_hom_snd]
    rw [reassoc_of% (bivariantBaseChangeMap_hom_comp_snd i (pullback.fst j (t ≫ κ)) φ), hφs,
      reassoc_of% (congrHom_rfl_hom_comp_snd i hφf.symm),
      reassoc_of% openRestrictionPullbackIso_hom_snd]

end RestrictComposite

end Stacks.Chow

end
