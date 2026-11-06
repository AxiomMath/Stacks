module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedCompletion

/-!
# The Koszul system of a finite family of global sections has the Čech system as its colimit

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. On the poset of
subsets of `{1, …, r}` there are two systems of sheaves of `𝒪`-modules:
`AlgebraicGeometry.RingedSite.koszulPowerFunctor`, the constant system `S ↦ 𝒪` whose transition
map along `S ⊆ T` is multiplication by `f_{T ∖ S}^{n+1}`, out of which the Koszul complex
`K(𝒪, f_1^{n+1}, …, f_r^{n+1})` is built, and
`AlgebraicGeometry.RingedSite.awayLocalizationFunctor`, the system `S ↦ 𝒪_{f_S}` out of which
the extended alternating Čech complex is built. This file constructs the comparison of the
first with the second — at the subset `S` the canonical map `𝒪 ⟶ 𝒪_{f_S}` divided by
`f_S^{n+1}` — and proves that it exhibits the Čech system as the colimit of the Koszul systems
along the maps between successive powers.

This is the system-level half of [Stacks, Tag 0913] for sheaves on a site.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulEnd`: multiplication by a monomial `∏ᵢ fᵢ^{eᵢ}` in the
  chosen global sections, as an endomorphism of the identity functor of `Mod(𝒪)`, of which
  `AlgebraicGeometry.RingedSite.koszulScalar` is the component at `𝒪`.
* `AlgebraicGeometry.RingedSite.koszulIndicator`: the exponent vector which is `k` on a subset
  and `0` off it, so that `koszulEnd` of it is multiplication by `f_S^k`.
* `AlgebraicGeometry.RingedSite.koszulCechTrans`: the comparison
  `K(𝒪, f^{n+1}) ⟶ (S ↦ 𝒪_{f_S})` of systems, dividing by `f_S^{n+1}` in the factor `S`.
* `AlgebraicGeometry.RingedSite.koszulPowerFunctorSystem`: the sequential diagram of the
  systems `koszulPowerFunctor` and the maps `koszulPowerTrans` between successive powers.
* `AlgebraicGeometry.RingedSite.koszulPowerFunctorCocone`: the cocone on the Čech system over
  that sequential diagram, whose legs are the comparisons.

## Main results

* `AlgebraicGeometry.RingedSite.awaySmul_pow_app_eq_of_subset`: for `S ⊆ T` multiplication by
  `f_T^n` factors as multiplication by `f_{T ∖ S}^n` followed by multiplication by `f_S^n`.
  This is the one computation the comparison needs.
* `AlgebraicGeometry.RingedSite.isColimitKoszulPowerFunctorCocone`: **the Čech system is the
  colimit of the Koszul systems.** Colimits in a category of functors are computed pointwise,
  and at the subset `S` the statement is that `𝒪_{f_S}` is the colimit of
  `𝒪 --f_S--> 𝒪 --f_S--> ⋯`, which is
  `AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone`.

## Implementation notes

The comparison is *not* constructed by naming a section of `𝒪_{f_S}`: the sheaf `𝒪_{f_S}` is a
sheafification and the element `1/f_S^{n+1}` has no name. It is the canonical map `𝒪 ⟶ 𝒪_{f_S}`
composed with the inverse of multiplication by `f_S^{n+1}`, which is invertible on `𝒪_{f_S}` by
`AlgebraicGeometry.RingedSite.isIso_awaySmul_pow_awayModule`; that is
`AlgebraicGeometry.RingedSite.awayModuleCoconeι`, the leg of the colimit cocone of
`AwayColimit.lean`, at the exponent `n + 1`.

Its naturality in `S` is proved by cancelling the monomorphism given by multiplication by
`f_T^{n+1}` on `𝒪_{f_T}`, after which no inverse of a multiplication operator is left in the
statement and the three inputs are: the factorisation
`awaySmul_pow_app_eq_of_subset` of multiplication by `f_T^{n+1}`, the naturality of the
multiplication operators — they are endomorphisms of the *identity functor*, so they commute
with every morphism of sheaves of modules, in particular with each other and with the
transition maps — and `AlgebraicGeometry.RingedSite.unitToAwayModule_comp_awayModuleTransition`,
that the canonical maps `𝒪 ⟶ 𝒪_{f_S}` are compatible with the transition maps.

Multiplication by a monomial is recorded here as an endomorphism `koszulEnd` of the identity
functor rather than only as the endomorphism `koszulScalar` of `𝒪`, because the naturality
argument needs its component at `𝒪_{f_S}` as well as at `𝒪`; the two spellings agree by
`AlgebraicGeometry.RingedSite.koszulEnd_app_unit`, which holds by definition.

The colimit property is proved by exhibiting the descent, its defining property and its
uniqueness directly, rather than through
`CategoryTheory.evaluationJointlyReflectsColimits`. The reason is that
`CategoryTheory.Functor.ofSequence` builds the morphism attached to a general `i ≤ j` by
recursion on `j - i`, so the evaluation at `S` of the sequential diagram of systems is *not*
the sequential diagram `𝒪 --f_S--> 𝒪 --f_S--> ⋯` of `AwayColimit.lean` as a term, only after an
induction; what a cocone over the latter needs is a family of legs with the compatibility at
`n ⟶ n + 1` only, which `CategoryTheory.NatTrans.ofSequence` supplies and which
`AlgebraicGeometry.RingedSite.koszulCechDescCocone` reads off a cocone over the former.

The legs of the cocone of `AwayColimit.lean` divide by `f^n`, whereas the comparison at the
index `n` must divide by `f_S^{n+1}`, the Koszul complex at the index `n` being the one on the
`(n+1)`-st powers; `AlgebraicGeometry.RingedSite.isColimitAwayModuleShiftCocone` is that
reindexing, which is a colimit cocone because the two differ by the automorphism of `𝒪_f`
given by multiplication by `f`.

The universes are the diagonal `RingedSite.{u, u, u}` with coefficient universe `u`, as in
`AwayColimit.lean` and `KoszulDerivedCompletion.lean`: `𝒪_f` is available only there.

The passage from the system-level statement proved here to the colimit presentation of the
extended alternating Čech complex by the Koszul complexes is the interchange of the sequential
colimit with the finite products `CategoryTheory.AlternatingCech.term` out of which both
complexes are built; it is `AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone` of
`KoszulCechColimit.lean`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-! ## Multiplication by a monomial on an arbitrary sheaf of modules -/

/-- **Multiplication by the monomial `∏ᵢ fᵢ^{eᵢ}`**, as an endomorphism of the identity functor
of the category of sheaves of `𝒪`-modules. Its component at `𝒪` is
`AlgebraicGeometry.RingedSite.koszulScalar`. -/
def koszulEnd (e : Fin r → ℕ) :
    End (𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (koszulFamily X f e)

/-- On local sections, multiplication by a monomial is multiplication by its value there. -/
theorem koszulEnd_app_apply (e : Fin r → ℕ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (U : X.Cᵒᵖ) (x : M.val.obj U) :
    ((koszulEnd X f e).asHom.app M).val.app U x = koszulRingValue X f e U • x := rfl

/-- The component at `𝒪` of multiplication by a monomial is
`AlgebraicGeometry.RingedSite.koszulScalar`. -/
theorem koszulEnd_app_unit (e : Fin r → ℕ) :
    (koszulEnd X f e).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      koszulScalar X f e := rfl

/-- **Composing multiplications by monomials adds exponents.** -/
theorem koszulEnd_comp (e e' : Fin r → ℕ) :
    (koszulEnd X f e).asHom ≫ (koszulEnd X f e').asHom = (koszulEnd X f (e + e')).asHom := by
  ext M U x
  show koszulRingValue X f e' U • (koszulRingValue X f e U • x) =
    koszulRingValue X f (e + e') U • x
  rw [← mul_smul]
  exact congrArg (fun c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U => c • x)
    (koszulValue_mul_comm X f e e' U)

/-- Multiplication by a monomial depends on the exponent vector only through its values. -/
theorem koszulEnd_congr {e e' : Fin r → ℕ} (h : ∀ i, e i = e' i) :
    koszulEnd X f e = koszulEnd X f e' := by
  rw [funext h]

/-- The exponent vector which is `k` at the indices of a subset `S` and `0` elsewhere, so that
the corresponding monomial is `f_S^k`. -/
def koszulIndicator (S : Finset (Fin r)) (k : ℕ) : Fin r → ℕ :=
  fun i => if i ∈ S then k else 0

/-- The monomial attached to `AlgebraicGeometry.RingedSite.koszulIndicator` is the `k`-th power
of the subproduct `f_S`: the factors outside `S` contribute an empty power. -/
theorem koszulValue_koszulIndicator (S : Finset (Fin r)) (k : ℕ) (U : X.Cᵒᵖ) :
    koszulValue X f (koszulIndicator S k) U =
      globalSectionVal (prodGlobalSection f S) U ^ k := by
  calc koszulValue X f (koszulIndicator S k) U
      = ∏ i : Fin r, globalSectionVal (f i) U ^ koszulIndicator S k i := rfl
    _ = ∏ i ∈ S, globalSectionVal (f i) U ^ koszulIndicator S k i :=
        (Finset.prod_subset (Finset.subset_univ S) fun i _ hiS => by
          simp [koszulIndicator, hiS]).symm
    _ = ∏ i ∈ S, globalSectionVal (f i) U ^ k :=
        Finset.prod_congr rfl fun i hiS => by simp [koszulIndicator, hiS]
    _ = (∏ i ∈ S, globalSectionVal (f i) U) ^ k := Finset.prod_pow _ _ _
    _ = globalSectionVal (prodGlobalSection f S) U ^ k := by
        rw [globalSectionVal_prodGlobalSection]

/-- For `S ⊆ T` the indicator exponents add: `f_T^k = f_{T ∖ S}^k · f_S^k`. -/
theorem koszulIndicator_sdiff_add (S T : Finset (Fin r)) (hST : S ⊆ T) (k : ℕ) (i : Fin r) :
    (koszulIndicator (T \ S) k + koszulIndicator S k) i = koszulIndicator T k i := by
  by_cases hiT : i ∈ T
  · by_cases hiS : i ∈ S <;> simp [koszulIndicator, hiT, hiS, Finset.mem_sdiff]
  · simp [koszulIndicator, hiT, Finset.mem_sdiff,
      show i ∉ S from fun hiS => hiT (hST hiS)]

/-- Multiplication by the monomial `f_S` acts on local sections by multiplication by the value
of the global section `f_S`, which is the hypothesis under which `AwayColimit.lean` identifies
an endomorphism of `𝒪` with multiplication by a global section. -/
theorem koszulScalar_koszulIndicator_one_app_apply (S : Finset (Fin r)) (U : X.Cᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U) :
    ((koszulScalar X f (koszulIndicator S 1)).val.app U) x =
      globalSectionVal (prodGlobalSection f S) U • x := by
  rw [koszulScalar_app]
  refine congrArg (fun c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U => c • x) ?_
  exact (koszulValue_koszulIndicator X f S 1 U).trans (pow_one _)

/-- Multiplication by `f_S^k` is multiplication by the monomial with exponent `k` on `S`. -/
theorem awaySmul_pow_eq_koszulEnd (S : Finset (Fin r)) (k : ℕ) :
    (awaySmul X (prodGlobalSection f S)) ^ k = koszulEnd X f (koszulIndicator S k) := by
  ext M U x
  rw [awaySmul_pow_app_apply, koszulEnd_app_apply]
  exact (congrArg (fun c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U => c • x)
    (koszulValue_koszulIndicator X f S k U)).symm

/-- **For `S ⊆ T`, multiplication by `f_T^k` is multiplication by `f_{T ∖ S}^k` followed by
multiplication by `f_S^k`**, on every sheaf of `𝒪`-modules. This is the computation that makes
the comparison with the Čech system natural. -/
theorem awaySmul_pow_app_eq_of_subset {S T : Finset (Fin r)} (hST : S ⊆ T) (k : ℕ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((awaySmul X (prodGlobalSection f T)) ^ k).asHom.app M =
      (koszulEnd X f (koszulIndicator (T \ S) k)).asHom.app M ≫
        ((awaySmul X (prodGlobalSection f S)) ^ k).asHom.app M := by
  rw [awaySmul_pow_eq_koszulEnd, awaySmul_pow_eq_koszulEnd, ← NatTrans.comp_app, koszulEnd_comp]
  exact congrArg
    (fun α : End (𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) =>
      α.asHom.app M)
    (koszulEnd_congr X f fun i => (koszulIndicator_sdiff_add S T hST k i).symm)

variable [HasWeakSheafify X.J CommRingCat.{u}]

/-! ## The comparison with the Čech system -/

/-- An abstract cancellation lemma. Let `a`, `b` be invertible endomorphisms of `A` and `B`,
let `u : Z ⟶ A`, `v : Z ⟶ B` and `t : A ⟶ B`, and let `k`, `k'` be endomorphisms of `A` and
`Z`. If `t` intertwines `b` with an endomorphism `b'` of `A` which factors as `k` followed by
`a`, if `k` commutes with `a`, if `u` intertwines `k'` with `k`, and if `u ≫ t = v`, then
"dividing `v` by `b`" after `k'` is "dividing `u` by `a`" followed by `t`.

With `a`, `b` the multiplications by `f_S^{n+1}` and `f_T^{n+1}` on `𝒪_{f_S}` and `𝒪_{f_T}`,
`u`, `v` the canonical maps out of `𝒪`, `t` the transition map and `k`, `k'` the multiplication
by `f_{T ∖ S}^{n+1}`, this is the naturality of the comparison of
`AlgebraicGeometry.RingedSite.koszulCechTrans`. It is stated for abstract morphisms of an
abstract category, so that no object of a category of sheaves of modules occurs in it. -/
private theorem comp_inv_comm {C : Type*} [Category C] {Z A B : C}
    {a : A ⟶ A} {b : B ⟶ B} {b' : A ⟶ A} {k : A ⟶ A} {k' : Z ⟶ Z}
    (u : Z ⟶ A) (v : Z ⟶ B) (t : A ⟶ B) [IsIso a] [IsIso b]
    (hnat : t ≫ b = b' ≫ t) (hfac : b' = k ≫ a) (hcomm : a ≫ k = k ≫ a)
    (hku : u ≫ k = k' ≫ u) (hut : u ≫ t = v) :
    k' ≫ v ≫ inv b = (u ≫ inv a) ≫ t := by
  rw [← cancel_mono b]
  have h1 : (k' ≫ v ≫ inv b) ≫ b = k' ≫ v := by
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have h2 : ((u ≫ inv a) ≫ t) ≫ b = k' ≫ v := by
    simp only [Category.assoc]
    rw [hnat, hfac]
    simp only [Category.assoc]
    rw [← Category.assoc k a t, ← hcomm]
    simp only [Category.assoc]
    rw [IsIso.inv_hom_id_assoc, ← Category.assoc, hku, Category.assoc, hut]
  rw [h1, h2]

/-- For `S ⊆ T`, multiplying by `f_{T ∖ S}^{n+1}` and then dividing by `f_T^{n+1}` is dividing
by `f_S^{n+1}` and then mapping into `𝒪_{f_T}`. -/
theorem koszulScalar_comp_awayModuleCoconeι {S T : Finset (Fin r)} (hST : S ⊆ T) (n : ℕ) :
    koszulScalar X f (koszulIndicator (T \ S) (n + 1)) ≫
        awayModuleCoconeι X (prodGlobalSection f T) (n + 1) =
      awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ awayModuleTransition X f hST :=
  comp_inv_comm (unitToAwayModule X (prodGlobalSection f S))
    (unitToAwayModule X (prodGlobalSection f T)) (awayModuleTransition X f hST)
    (((awaySmul X (prodGlobalSection f T)) ^ (n + 1)).asHom.naturality
      (awayModuleTransition X f hST))
    (awaySmul_pow_app_eq_of_subset X f hST (n + 1) (awayModule X (prodGlobalSection f S)))
    ((koszulEnd X f (koszulIndicator (T \ S) (n + 1))).asHom.naturality
      (((awaySmul X (prodGlobalSection f S)) ^ (n + 1)).asHom.app
        (awayModule X (prodGlobalSection f S))))
    ((koszulEnd X f (koszulIndicator (T \ S) (n + 1))).asHom.naturality
      (unitToAwayModule X (prodGlobalSection f S)))
    (unitToAwayModule_comp_awayModuleTransition X f hST)

/-- **The comparison of the Koszul system on the `(n+1)`-st powers of `f_1, …, f_r` with the
system `S ↦ 𝒪_{f_S}` of localizations**: at the subset `S` it is the canonical map
`𝒪 ⟶ 𝒪_{f_S}` divided by `f_S^{n+1}`. -/
def koszulCechTrans (n : ℕ) : koszulPowerFunctor X f n ⟶ awayLocalizationFunctor X f where
  app S := awayModuleCoconeι X (prodGlobalSection f S) (n + 1)
  naturality _ _ g := koszulScalar_comp_awayModuleCoconeι X f (leOfHom g) n

/-- The component at the subset `S` of the comparison is the canonical map `𝒪 ⟶ 𝒪_{f_S}`
divided by `f_S^{n+1}`. -/
@[simp]
theorem koszulCechTrans_app (n : ℕ) (S : Finset (Fin r)) :
    (koszulCechTrans X f n).app S = awayModuleCoconeι X (prodGlobalSection f S) (n + 1) :=
  rfl

/-! ## The colimit of the Koszul systems -/

section Shift

variable (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- Reindexing a cocone over `𝒪 --f--> 𝒪 --f--> ⋯` by one step: the leg at the index `n` is
the old leg at `n` preceded by the multiplication. -/
def awaySequenceShiftCocone (c : Cocone (awaySequence X a)) : Cocone (awaySequence X a) where
  pt := c.pt
  ι := NatTrans.ofSequence (fun n => a ≫ c.ι.app n) (fun n => by
    have hw := c.w (homOfLE (n.le_add_right 1))
    rw [awaySequence_map_succ] at hw
    rw [awaySequence_map_succ]
    exact (congrArg (fun k => a ≫ k) hw).trans (Category.comp_id _).symm)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The leg at `n` of the reindexed cocone is the old leg at `n` preceded by `a`. -/
@[simp]
theorem awaySequenceShiftCocone_ι_app (c : Cocone (awaySequence X a)) (n : ℕ) :
    (awaySequenceShiftCocone X a c).ι.app n = a ≫ c.ι.app n :=
  rfl

variable (ha : ∀ (U : X.Cᵒᵖ) (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U),
    (a.val.app U).hom x = globalSectionVal h U • x)

/-- **The cocone on `𝒪_f` whose `n`-th leg divides by `f^{n+1}`.** This is the reindexing of
`AlgebraicGeometry.RingedSite.awayModuleCocone` that the Koszul systems map to: the transition
map of the Koszul system between the `(n+1)`-st and the `(n+2)`-nd powers is multiplication by
`f_S` in the factor `S`, so the leg at the index `n` must divide by `f_S^{n+1}`. -/
def awayModuleShiftCocone : Cocone (awaySequence X a) where
  pt := awayModule X h
  ι := NatTrans.ofSequence (fun n => awayModuleCoconeι X h (n + 1)) (fun n => by
    rw [awaySequence_map_succ]
    exact (comp_awayModuleCoconeι_succ X h a ha (n + 1)).trans (Category.comp_id _).symm)

/-- The leg at `n` of the reindexed cocone on `𝒪_f` divides by `f^{n+1}`. -/
@[simp]
theorem awayModuleShiftCocone_ι_app (n : ℕ) :
    (awayModuleShiftCocone X h a ha).ι.app n = awayModuleCoconeι X h (n + 1) :=
  rfl

include ha in
/-- **The reindexed cocone is still a colimit cocone.** Its leg at `n` is the leg at `n + 1` of
the colimit cocone of `AwayColimit.lean`, so the descent of a cocone `c` out of it is the
descent of the once-reindexed cocone `AlgebraicGeometry.RingedSite.awaySequenceShiftCocone` out
of that one: the defining property at `n + 1` then reads
`𝒪_f ∋ 1/f^{n+1} ↦ f · c_{n+1} = c_n`. -/
def isColimitAwayModuleShiftCocone : IsColimit (awayModuleShiftCocone X h a ha) where
  desc c := (isColimitAwayModuleCocone X h a ha).desc (awaySequenceShiftCocone X a c)
  fac c n := by
    refine ((isColimitAwayModuleCocone X h a ha).fac
      (awaySequenceShiftCocone X a c) (n + 1)).trans ?_
    have hw := c.w (homOfLE (n.le_add_right 1))
    rw [awaySequence_map_succ] at hw
    exact hw
  uniq c m hm := by
    have key : ∀ m' : awayModule X h ⟶ c.pt,
        (∀ n, awayModuleCoconeι X h (n + 1) ≫ m' = c.ι.app n) →
          m' = (isColimitAwayModuleCocone X h a ha).desc (awaySequenceShiftCocone X a c) := by
      intro m' hm'
      refine (isColimitAwayModuleCocone X h a ha).uniq
        (awaySequenceShiftCocone X a c) m' fun n => ?_
      change awayModuleCoconeι X h n ≫ m' = a ≫ c.ι.app n
      rw [← comp_awayModuleCoconeι_succ X h a ha n, Category.assoc, hm' n]
    exact key m hm

end Shift

/-- **The sequential diagram of the systems underlying the Koszul complexes** on the positive
powers of `f_1, …, f_r`, with the maps of
`AlgebraicGeometry.RingedSite.koszulPowerTrans` between successive powers. -/
def koszulPowerFunctorSystem :
    ℕ ⥤ (Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Functor.ofSequence (koszulPowerTrans X f)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The map from the index `n` to the index `n + 1` of the sequential diagram of Koszul systems
is `AlgebraicGeometry.RingedSite.koszulPowerTrans`. -/
@[simp]
theorem koszulPowerFunctorSystem_map_succ (n : ℕ) :
    (koszulPowerFunctorSystem X f).map (homOfLE (n.le_add_right 1)) =
      koszulPowerTrans X f n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The maps between successive powers followed by the comparison with the Čech system are the
comparison with the Čech system: multiplying by `f_S` and then dividing by `f_S^{n+2}` is
dividing by `f_S^{n+1}`. -/
theorem koszulPowerTrans_comp_koszulCechTrans (n : ℕ) :
    koszulPowerTrans X f n ≫ koszulCechTrans X f (n + 1) = koszulCechTrans X f n := by
  refine NatTrans.ext (funext fun S => ?_)
  show koszulScalar X f (koszulIndicator S 1) ≫
      awayModuleCoconeι X (prodGlobalSection f S) (n + 1 + 1) =
    awayModuleCoconeι X (prodGlobalSection f S) (n + 1)
  exact comp_awayModuleCoconeι_succ X (prodGlobalSection f S)
    (koszulScalar X f (koszulIndicator S 1))
    (koszulScalar_koszulIndicator_one_app_apply X f S) (n + 1)

/-- **The cocone on the system `S ↦ 𝒪_{f_S}` over the sequential diagram of Koszul systems**,
whose leg at the index `n` is the comparison `AlgebraicGeometry.RingedSite.koszulCechTrans`. -/
def koszulPowerFunctorCocone : Cocone (koszulPowerFunctorSystem X f) where
  pt := awayLocalizationFunctor X f
  ι := NatTrans.ofSequence (koszulCechTrans X f) (fun n => by
    rw [koszulPowerFunctorSystem_map_succ]
    exact (koszulPowerTrans_comp_koszulCechTrans X f n).trans (Category.comp_id _).symm)

/-- The leg at `n` of the cocone on `S ↦ 𝒪_{f_S}` is the comparison
`AlgebraicGeometry.RingedSite.koszulCechTrans`. -/
@[simp]
theorem koszulPowerFunctorCocone_ι_app (n : ℕ) :
    (koszulPowerFunctorCocone X f).ι.app n = koszulCechTrans X f n :=
  rfl

section Descent

variable (c : Cocone (koszulPowerFunctorSystem X f))

/-- The cocone over the sequence `𝒪 --f_S--> 𝒪 --f_S--> ⋯` induced at the subset `S` by a
cocone over the sequential diagram of Koszul systems: its legs are the components at `S` of
the legs of that cocone. -/
def koszulCechDescCocone (S : Finset (Fin r)) :
    Cocone (awaySequence X (koszulScalar X f (koszulIndicator S 1))) where
  pt := c.pt.obj S
  ι := NatTrans.ofSequence (fun n => (c.ι.app n).app S) (fun n => by
    have hw := NatTrans.congr_app (c.w (homOfLE (n.le_add_right 1))) S
    rw [NatTrans.comp_app, koszulPowerFunctorSystem_map_succ] at hw
    rw [awaySequence_map_succ]
    exact hw.trans (Category.comp_id _).symm)

/-- The descent of a cocone over the sequential diagram of Koszul systems through the
comparison with the Čech system, subset by subset. -/
def koszulCechDescApp (S : Finset (Fin r)) :
    awayModule X (prodGlobalSection f S) ⟶ c.pt.obj S :=
  (isColimitAwayModuleShiftCocone X (prodGlobalSection f S)
      (koszulScalar X f (koszulIndicator S 1))
      (koszulScalar_koszulIndicator_one_app_apply X f S)).desc
    (koszulCechDescCocone X f c S)

/-- Dividing by `f_S^{n+1}` and then applying the descent at `S` is the component at `S` of the
leg at `n` of the cocone. -/
theorem awayModuleCoconeι_comp_koszulCechDescApp (S : Finset (Fin r)) (n : ℕ) :
    awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ koszulCechDescApp X f c S =
      (c.ι.app n).app S :=
  (isColimitAwayModuleShiftCocone X (prodGlobalSection f S)
      (koszulScalar X f (koszulIndicator S 1))
      (koszulScalar_koszulIndicator_one_app_apply X f S)).fac
    (koszulCechDescCocone X f c S) n

/-- Two maps out of `𝒪_{f_S}` agree as soon as they agree after dividing by every `f_S^{n+1}`. -/
theorem awayModule_hom_ext (S : Finset (Fin r))
    {Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {φ ψ : awayModule X (prodGlobalSection f S) ⟶ Z}
    (hφψ : ∀ n, awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ φ =
      awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ ψ) : φ = ψ :=
  (isColimitAwayModuleShiftCocone X (prodGlobalSection f S)
      (koszulScalar X f (koszulIndicator S 1))
      (koszulScalar_koszulIndicator_one_app_apply X f S)).hom_ext hφψ

/-- The subsetwise descents are natural in the subset, so they assemble into a map of systems
out of the Čech system. -/
def koszulCechDesc : awayLocalizationFunctor X f ⟶ c.pt where
  app S := koszulCechDescApp X f c S
  naturality S T g := by
    refine awayModule_hom_ext X f S fun n => ?_
    have hnat : koszulScalar X f (koszulIndicator (T \ S) (n + 1)) ≫ (c.ι.app n).app T =
        (c.ι.app n).app S ≫ c.pt.map g := NatTrans.naturality (c.ι.app n) g
    have h1 : awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫
        awayModuleTransition X f (leOfHom g) ≫ koszulCechDescApp X f c T =
          koszulScalar X f (koszulIndicator (T \ S) (n + 1)) ≫ (c.ι.app n).app T := by
      rw [← Category.assoc, ← koszulScalar_comp_awayModuleCoconeι X f (leOfHom g) n,
        Category.assoc, awayModuleCoconeι_comp_koszulCechDescApp]
    have h2 : awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫
        koszulCechDescApp X f c S ≫ c.pt.map g = (c.ι.app n).app S ≫ c.pt.map g := by
      rw [← Category.assoc, awayModuleCoconeι_comp_koszulCechDescApp]
      rfl
    change awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫
        awayModuleTransition X f (leOfHom g) ≫ koszulCechDescApp X f c T =
      awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫
        koszulCechDescApp X f c S ≫ c.pt.map g
    rw [h1, h2]
    exact hnat

end Descent

/-- **The system `S ↦ 𝒪_{f_S}` of localizations is the colimit of the systems underlying the
Koszul complexes on the positive powers of `f_1, …, f_r`.**

This is the system-level half of [Stacks, Tag 0913] for sheaves on a site: colimits in a
category of functors are computed subset by subset, and at the subset `S` the statement is that
`𝒪_{f_S}` is the colimit of `𝒪 --f_S--> 𝒪 --f_S--> ⋯`, which is
`AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone` reindexed by
`AlgebraicGeometry.RingedSite.isColimitAwayModuleShiftCocone`. -/
def isColimitKoszulPowerFunctorCocone : IsColimit (koszulPowerFunctorCocone X f) where
  desc c := koszulCechDesc X f c
  fac c n := by
    refine NatTrans.ext (funext fun S => ?_)
    change awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ koszulCechDescApp X f c S =
      (c.ι.app n).app S
    exact awayModuleCoconeι_comp_koszulCechDescApp X f c S n
  uniq c m hm := by
    refine NatTrans.ext (funext fun S => ?_)
    refine awayModule_hom_ext X f S fun n => ?_
    change awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ m.app S =
      awayModuleCoconeι X (prodGlobalSection f S) (n + 1) ≫ koszulCechDescApp X f c S
    rw [awayModuleCoconeι_comp_koszulCechDescApp]
    exact NatTrans.congr_app (hm n) S

end AlgebraicGeometry.RingedSite

end
