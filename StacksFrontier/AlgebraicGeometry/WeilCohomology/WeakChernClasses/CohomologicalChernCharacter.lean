module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacterConstructed
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.ChernCharacterExistence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.TotalChernClass

/-!
# The cohomological Chern character of a Weil cohomology theory, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacter`, stated
for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation
of Stacks Section 45.12 in which the projective bundle formula, condition (4), is only asked to be
injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments are those of the original module, which use condition
(4) only through these two properties.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### The target of the cohomological Chern character -/

/-- **`∏_{i ≥ 0} A^i(X)` inside `A(X)[[t]]`**: the power series whose `n`-th coefficient lies in
`A^n(X)`. The product of the graded pieces, whose multiplication is the convolution, is exactly
this subgroup of the power series ring. -/
def gradedPowerSeries (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C) :
    AddSubgroup (PowerSeries (𝔚.A X)) where
  carrier := {φ | ∀ n : ℕ, PowerSeries.coeff n φ ∈ 𝔚.grade X n}
  add_mem' hφ hψ n := by simpa using add_mem (hφ n) (hψ n)
  zero_mem' n := by simp
  neg_mem' hφ n := by simpa using neg_mem (hφ n)

/-- A power series lies in `gradedPowerSeries 𝔚 X` iff its `n`-th coefficient lies in `A^n(X)`
for every `n`. -/
@[simp] theorem mem_gradedPowerSeries {𝔚 : ChernSetup.{u, v, v₁, w} C S} {X : C}
    {φ : PowerSeries (𝔚.A X)} :
    φ ∈ gradedPowerSeries 𝔚 X ↔ ∀ n : ℕ, PowerSeries.coeff n φ ∈ 𝔚.grade X n :=
  Iff.rfl

/-- **`exp(c_1^H(ℒ))`**, the value Tag 0FIE prescribes for the cohomological Chern character of
an invertible module: the power series whose `n`-th coefficient is `(1/n!) · c_1^H(ℒ)^n`. This
is where `A(X)` being a `𝐐`-algebra, that is `F` having characteristic zero, is used. -/
def expFirstChernClass (𝔚 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔚.A X)] (X : C)
    (L : (S.obj X).picardGroup) : PowerSeries (𝔚.A X) :=
  PowerSeries.mk fun n => algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) * 𝔚.c₁ X L ^ n

/-- The `n`-th coefficient of `expFirstChernClass 𝔚 X L` is `(1/n!) · c_1^H(ℒ)^n`. -/
@[simp] theorem coeff_expFirstChernClass {𝔚 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔚.A X)] (X : C) (L : (S.obj X).picardGroup) (n : ℕ) :
    PowerSeries.coeff n (expFirstChernClass 𝔚 X L) =
      algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) * 𝔚.c₁ X L ^ n := by
  simp [expFirstChernClass]

/-! ### Two auxiliary facts -/

/-! ### The rule of Tag 0FIE -/

section

/-- A module of constant rank is finite locally free in the sense of `Stacks.FiniteLocallyFree`. -/
private theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank {X : C} {E : (S.obj X).Modules}
    {r : ℕ} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
    hE.isFiniteLocallyFree

variable (𝔚 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔚.A X)]
  (κ : ∀ {X Y : C}, (X ⟶ Y) → (VectorBundleKZero (S.obj Y) →+* VectorBundleKZero (S.obj X)))

/-- The degree-`n` part of the pullback of a cohomological Chern character along the morphism the
splitting principle produces, computed from the filtration: the class of `p^*ℰ` is the sum of the
classes of the invertible successive quotients, so the character of `p^*ℰ` is the sum of their
exponentials.

The pullback homomorphism `κ` of `K₀(Vect(-))` is a hypothesis here, with `hκ` its value on the
class of a module; `pull_coeff_eq_sum'` is this statement with `κ` taken to be the constructed
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`. -/
private theorem pull_coeff_eq_sum
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (κ f α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    {X P : C} (p : P ⟶ X) {E : (S.obj X).Modules}
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E) {k : ℕ}
    (L : Fin k → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj E) =
      ∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) (n : ℕ) :
    𝔚.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E))) =
      ∑ j, algebraMap ℚ (𝔚.A P) ((n.factorial : ℚ)⁻¹) *
        𝔚.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n := by
  calc 𝔚.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E)))
      = PowerSeries.coeff n
          (PowerSeries.map (𝔚.pull p) (ch X (VectorBundleKZero.classOf (S.obj X) E))) := by
        simp
    _ = ∑ j, PowerSeries.coeff n (ch P (VectorBundleKZero.classOf (S.obj P) (L j))) := by
        rw [hpull p _, hκ p E hE, hsum, map_sum]
        simp
    _ = ∑ j, algebraMap ℚ (𝔚.A P) ((n.factorial : ℚ)⁻¹) *
          𝔚.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n :=
        Finset.sum_congr rfl fun j _ => by rw [hinv P (L j) (hL j), coeff_expFirstChernClass]

/-- **The uniqueness half of Stacks Tag 0FIE.** Two rules assigning to every object `X` of `𝒞` a
ring homomorphism `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`, compatible with pullbacks and taking
the value `exp(c_1^H(ℒ))` on every invertible module, agree on the class of every finite locally
free module of constant rank.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the prescribed value
determine the character; compatibility with pullbacks identifies the result with
`p^*ch^H([ℰ])`, and `p^*` is injective.

The pullback homomorphism `κ` of `K₀(Vect(-))` is a hypothesis here, with `hκ` its value on the
class of a module; `eq_of_cohomologicalChernCharacter'` is this statement with `κ` taken to be
the constructed `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, and with the constant rank
removed. -/
theorem eq_of_cohomologicalChernCharacter
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (κ f α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch' Y α) = ch' X (κ f α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) := by
  classical
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔚.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  have hEflf := isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank hE
  refine PowerSeries.ext fun n => hinj ?_
  rw [pull_coeff_eq_sum 𝔚 κ hκ hpull hinv p hEflf L hL hsum n,
    pull_coeff_eq_sum 𝔚 κ hκ hpull' hinv' p hEflf L hL hsum n]

/-- **The existence half of Stacks Tag 0FIE.** The cohomological Chern character of a single
finite locally free module extends to a ring homomorphism
`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)` for every object `X` of `𝒞`, which is graded,
compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on an invertible module.

The extension is Tag 0FEM's universal property of the Grothendieck ring, applied to the given
additive, multiplicative and unital assignment; the grading and the compatibility with pullbacks
pass from the generators to all of `K₀(Vect(X))` because the graded series form a subgroup and
because both sides of the pullback equation are additive.

The pullback homomorphism `κ` of `K₀(Vect(-))` is a hypothesis here, with `hκ` its value on the
class of a module and `hflf` the stability of finite local freeness it needs;
`exists_cohomologicalChernCharacter'` is this statement with `κ` taken to be the constructed
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, which discharges all three. -/
theorem exists_cohomologicalChernCharacter
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    (chM : ∀ X : C, (S.obj X).Modules → PowerSeries (𝔚.A X))
    (hzero : ∀ (X : C) (M : (S.obj X).Modules),
      ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M → chM X M = 0)
    (hadd : ∀ (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} F →
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} G →
            Mono f → Epi g → (ShortComplex.mk f g w).Exact →
              chM X F = chM X E + chM X G)
    (hmul : ∀ (X : C) (M N : (S.obj X).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N →
          chM X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) = chM X M * chM X N)
    (hone : ∀ X : C, chM X (SheafOfModules.unit (S.obj X).ringCatSheaf) = 1)
    (hgrade : ∀ (X : C) (M : (S.obj X).Modules), chM X M ∈ gradedPowerSeries 𝔚 X)
    (hinvM : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      chM X L = expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (hpullM : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        PowerSeries.map (𝔚.pull f) (chM Y E) =
          chM X ((Scheme.Modules.pullback (S.map f)).obj E))
    (hflf : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
          ((Scheme.Modules.pullback (S.map f)).obj E)) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) = chM X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔚 X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (κ f α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL) := by
  classical
  choose ch hch _hchuniq using fun X : C =>
    AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative
      (S.obj X) (chM X) (hzero X) (fun f g w => hadd X f g w) (hmul X) (hone X)
  refine ⟨ch, hch, fun X α => ?_, fun {X Y} f α => ?_, fun X L hL => ?_⟩
  · suffices hG : (QuotientAddGroup.mk' (gradedPowerSeries 𝔚 X)).comp
        (ch X).toAddMonoidHom = 0 by
      simpa [QuotientAddGroup.eq_zero_iff] using DFunLike.congr_fun hG α
    refine VectorBundleKZero.addHom_ext fun M hM => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
      AddMonoidHom.zero_apply, QuotientAddGroup.eq_zero_iff]
    change ch X (VectorBundleKZero.classOf (S.obj X) M) ∈ gradedPowerSeries 𝔚 X
    rw [hch X M hM]
    exact hgrade X M
  · refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
      (φ := (PowerSeries.map (𝔚.pull f)).toAddMonoidHom.comp (ch Y).toAddMonoidHom)
      (ψ := (ch X).toAddMonoidHom.comp (κ f).toAddMonoidHom) fun E hE => ?_) α
    change PowerSeries.map (𝔚.pull f) (ch Y (VectorBundleKZero.classOf (S.obj Y) E)) =
      ch X (κ f (VectorBundleKZero.classOf (S.obj Y) E))
    rw [hch Y E hE, hκ f E hE, hch X _ (hflf f E hE), hpullM f E hE]
  · have := hL
    rw [hch X L (isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (r := 1) inferInstance),
      hinvM X L hL]

/-- The degree-`n` part of the pullback of a cohomological Chern character along the morphism the
splitting principle produces, computed from the filtration: the class of `p^*ℰ` is the sum of the
classes of the invertible successive quotients, so the character of `p^*ℰ` is the sum of their
exponentials. -/
private theorem pull_coeff_eq_sum'
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    {X P : C} (p : P ⟶ X) {E : (S.obj X).Modules}
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E) {k : ℕ}
    (L : Fin k → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj E) =
      ∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) (n : ℕ) :
    𝔚.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E))) =
      ∑ j, algebraMap ℚ (𝔚.A P) ((n.factorial : ℚ)⁻¹) *
        𝔚.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n :=
  pull_coeff_eq_sum 𝔚 (fun {_ _} f => VectorBundleKZero.pullbackRingHom (S.map f))
    (fun f E hE => VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE)
    hpull hinv p hE L hL hsum n

/-- The uniqueness of Tag 0FIE on the class of a module of **constant** rank, which is the case
the splitting principle reaches directly.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the prescribed value
determine the character; compatibility with pullbacks identifies the result with
`p^*ch^H([ℰ])`, and `p^*` is injective. -/
private theorem eq_classOf_of_isFiniteLocallyFreeOfRank
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch' Y α) = ch' X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) :=
  eq_of_cohomologicalChernCharacter 𝔚 (fun {_ _} f => VectorBundleKZero.pullbackRingHom (S.map f))
    (fun f E hE => VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE)
    hpull hpull' hinv hinv' X E r hE

/-- **The uniqueness half of Stacks Tag 0FIE.** Two rules assigning to every object `X` of `𝒞` a
ring homomorphism `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`, compatible with pullbacks and taking
the value `exp(c_1^H(ℒ))` on every invertible module, are equal: they agree on every class of
`K₀(Vect(X))`, for every object `X` of `𝒞`.

Both rules are additive, so it is enough that they agree on the classes `[ℰ]` of finite locally
free modules, which generate `K₀(Vect(X))`. For `ℰ` of constant rank that is
`eq_classOf_of_isFiniteLocallyFreeOfRank`, read off the splitting principle. An arbitrary `ℰ` is
reduced to that case by `Stacks.WeilCohomology.Weak.ChernSetup.exists_clopenRankPieces`:
restriction to the finitely many loci where the rank of `ℰ` is constant is injective on `A(X)` by
condition (2) of the situation, and both rules commute with those restrictions. -/
theorem eq_of_cohomologicalChernCharacter'
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔚.pull f) (ch' Y α) = ch' X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (X : C) (α : VectorBundleKZero (S.obj X)) :
    ch X α = ch' X α := by
  classical
  refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := (ch X).toAddMonoidHom) (ψ := (ch' X).toAddMonoidHom) fun E hE => ?_) α
  change ch X (VectorBundleKZero.classOf (S.obj X) E) =
    ch' X (VectorBundleKZero.classOf (S.obj X) E)
  obtain ⟨ι, -, P, p, r, -, hrank, hinj⟩ := 𝔚.exists_clopenRankPieces X E
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE)
  refine PowerSeries.ext fun n => hinj (funext fun i => ?_)
  have key : PowerSeries.map (𝔚.pull (p i)) (ch X (VectorBundleKZero.classOf (S.obj X) E)) =
      PowerSeries.map (𝔚.pull (p i)) (ch' X (VectorBundleKZero.classOf (S.obj X) E)) := by
    rw [hpull (p i) _, hpull' (p i) _, VectorBundleKZero.pullbackRingHom_classOf (S.map (p i)) E hE]
    exact eq_classOf_of_isFiniteLocallyFreeOfRank 𝔚 hpull hpull' hinv hinv' (P i) _ (r i)
      (hrank i)
  simpa using congrArg (PowerSeries.coeff n) key

/-- **The existence half of Stacks Tag 0FIE.** The cohomological Chern character of a single
finite locally free module extends to a ring homomorphism
`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)` for every object `X` of `𝒞`, which is graded,
compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on an invertible module.

The extension is Tag 0FEM's universal property of the Grothendieck ring, applied to the given
additive, multiplicative and unital assignment; the grading and the compatibility with pullbacks
pass from the generators to all of `K₀(Vect(X))` because the graded series form a subgroup and
because both sides of the pullback equation are additive.

This statement takes the Chern character of a single module as data, so it does not
carry the tag. `Stacks.WeilCohomology.exists_cohomologicalChernCharacter_of_source`
is where [Stacks, Tag 0FIE]'s existence half sits: there the per-module character is
`Stacks.WeilCohomology.chernCharacterOfModule` and nothing is assumed beyond the data
and conditions of Sections 45.12 and 45.14. -/
theorem exists_cohomologicalChernCharacter'
    (chM : ∀ X : C, (S.obj X).Modules → PowerSeries (𝔚.A X))
    (hzero : ∀ (X : C) (M : (S.obj X).Modules),
      ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M → chM X M = 0)
    (hadd : ∀ (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} F →
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} G →
            Mono f → Epi g → (ShortComplex.mk f g w).Exact →
              chM X F = chM X E + chM X G)
    (hmul : ∀ (X : C) (M N : (S.obj X).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N →
          chM X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) = chM X M * chM X N)
    (hone : ∀ X : C, chM X (SheafOfModules.unit (S.obj X).ringCatSheaf) = 1)
    (hgrade : ∀ (X : C) (M : (S.obj X).Modules), chM X M ∈ gradedPowerSeries 𝔚 X)
    (hinvM : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      chM X L = expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL))
    (hpullM : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        PowerSeries.map (𝔚.pull f) (chM Y E) =
          chM X ((Scheme.Modules.pullback (S.map f)).obj E)) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) = chM X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔚 X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔚.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL) :=
  exists_cohomologicalChernCharacter 𝔚 (fun {_ _} f => VectorBundleKZero.pullbackRingHom (S.map f))
    (fun f E hE => VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE)
    chM hzero hadd hmul hone hgrade hinvM hpullM fun f E hE =>
      (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).mpr
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E
          ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE))

end

/-! ### The `𝐐`-structure of `A` read off (D1) -/

section

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **(D1) read for `A`**: the graded pieces of `A(X)` are `𝐐`-subspaces, that is, `A` takes its
values in *graded* `𝐐`-algebras.

This is what data (D0) and (D1) of Section 45.14 say about `A(X) = ⨁_{i ≥ 0} H^{2i}(X)(i)`: by
(D1) the functor `H^*` lands in graded commutative `F`-algebras, so each graded piece of
`H^*(X)` is an `F`-submodule, and by (D0) the field `F` has characteristic zero, so `𝐐` maps to
`F` and each graded piece is in particular a `𝐐`-subspace.

It is *equivalent*, over a `Stacks.WeilCohomology.Weak.ChernSetup`, to the one-degree assertion
that the rationals lie in `A^0(X)`:
`Stacks.WeilCohomology.Weak.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded` and
`Stacks.WeilCohomology.Weak.ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero` prove the
two implications, the first from `one_mem` and the second from `mul_mem`. -/
def ChernSetup.IsRationallyGraded (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔚.A X)] : Prop :=
  ∀ (X : C) (i : ℕ) (q : ℚ) {a : 𝔚.A X}, a ∈ 𝔚.grade X i → q • a ∈ 𝔚.grade X i

/-- **The rationals lie in `A^0(X)`, derived from (D1) rather than assumed.** `algebraMap ℚ q` is
`q • 1`, the unit lies in `A^0(X)` by the field `Stacks.WeilCohomology.Weak.ChernSetup.one_mem`,
and `A^0(X)` is a `𝐐`-subspace by (D1). -/
theorem ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded
    (𝔚 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔚.A X)]
    (hgr : 𝔚.IsRationallyGraded) (X : C) (q : ℚ) :
    algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact hgr X 0 q (𝔚.one_mem X)

/-- **The converse**: the rationals lying in `A^0(X)` makes every graded piece a `𝐐`-subspace,
because `q • a` is `algebraMap ℚ q * a` and multiplication adds degrees. So the field
`Stacks.WeilCohomology.Weak.RationalChernSituation.algebraMap_mem_grade_zero` is not an assumption
beyond (D0) and (D1): it is exactly their content for `A`. -/
theorem ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero
    (𝔚 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔚.A X)]
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0) :
    𝔚.IsRationallyGraded := fun X i q {_a} ha => by
  rw [Algebra.smul_def]
  simpa using 𝔚.mul_mem X 0 i (hq X q) ha

/-! ### The existence half with the Chern character of a module discharged -/

/-- **The existence half of Stacks Tag 0FIE with the `𝐐`-structure of `A` taken from (D1).**

This is `Stacks.WeilCohomology.Weak.RationalChernSituation.exists_cohomologicalChernCharacter` with
the field `algebraMap_mem_grade_zero` of that situation replaced by
`Stacks.WeilCohomology.Weak.ChernSetup.IsRationallyGraded`, the assertion of data (D0) and (D1) of
Section 45.14 that `A` takes its values in graded `𝐐`-algebras. The field is *derived* from it
here, by `Stacks.WeilCohomology.Weak.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded`,
rather than assumed; the two are equivalent over a `ChernSetup`, so nothing is lost and nothing
beyond (D0) and (D1) is asked of the `𝐐`-structure. -/
theorem ChernSituation.exists_cohomologicalChernCharacter
    (𝔗 : ChernSituation.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔗.A X)]
    (hgr : 𝔗.toChernSetup.IsRationallyGraded) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔗.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule 𝔗.isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)),
            ch X α ∈ gradedPowerSeries 𝔗.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔗.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔗.toChernSetup X (picardClassOf (S.obj X) L hL) :=
  Stacks.WeilCohomology.Weak.exists_cohomologicalChernCharacter' 𝔗.toChernSetup
    (chernCharacterOfModule 𝔗.isTotalChernClass_totalChernClass)
    (fun X M h => chernCharacterOfModule_eq_zero _ X M h)
    (fun X {E F G} f g w hE _hF hG hmono hepi hex =>
      chernCharacterOfModule_add_of_shortExact (E := E) (F := F) (G := G) _ X f g w hE hG
        hmono hepi hex)
    (fun X M N hM hN => chernCharacterOfModule_mul _ X M N hM hN)
    (fun X => chernCharacterOfModule_unit _ X)
    (fun X M => mem_gradedPowerSeries.2 fun n =>
      coeff_chernCharacterOfModule_mem_grade
        (𝔗.toChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded hgr) _ X M n)
    (fun X L hL => PowerSeries.ext fun n => by
      rw [chernCharacterOfModule_invertible _ X L hL n, coeff_expFirstChernClass])
    (fun {_X _Y} f E hE => PowerSeries.ext fun n => by
      rw [PowerSeries.coeff_map, pull_coeff_chernCharacterOfModule _ f E
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE) n])

/-- **The existence half of Stacks Tag 0FIE in the standing situation of Section 45.12**, with
the Chern character of a single module no longer assumed.

`Stacks.WeilCohomology.exists_cohomologicalChernCharacter` takes the per-module character `chM`
and its seven properties as hypotheses, because the source's proof of this tag cites the
existence half of Tag 0FI9 for them. In the standing situation
`Stacks.WeilCohomology.Weak.RationalChernSituation` that citation is a theorem of this repository:
`Stacks.WeilCohomology.chernCharacterOfModule` is the source's formula
`ch^A(ℰ) = r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`, and its seven properties are

* `chernCharacterOfModule_eq_zero` — vanishing off the finite locally free modules;
* `chernCharacterOfModule_add_of_shortExact` — additivity along a short exact sequence;
* `chernCharacterOfModule_mul` — multiplicativity on a tensor product;
* `chernCharacterOfModule_unit` — the value `1` on `𝒪_X`;
* `coeff_chernCharacterOfModule_mem_grade` — the grading;
* `chernCharacterOfModule_invertible` — the value `exp(c₁^A(ℒ))` on an invertible module;
* `pull_coeff_chernCharacterOfModule` — compatibility with pullback.

The last three are stated coefficientwise and are read as statements about the power series by
`PowerSeries.ext`. The total Chern class those depend on is Tag 0FI5 in the same situation, and
Tag 0FI9's `𝐐`-algebra condition on `A(X)`, read with the grading, is the field
`Stacks.WeilCohomology.Weak.RationalChernSituation.algebraMap_mem_grade_zero` of the situation this
is stated over. The pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, and the field is itself data (D0) and (D1)
read for `A`, so this is
`Stacks.WeilCohomology.Weak.ChernSituation.exists_cohomologicalChernCharacter` with that field fed
into `Stacks.WeilCohomology.Weak.ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero`. -/
theorem RationalChernSituation.exists_cohomologicalChernCharacter
    (𝔗 : RationalChernSituation.{u, v, v₁, w} C S) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔗.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule 𝔗.isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)),
            ch X α ∈ gradedPowerSeries 𝔗.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔗.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔗.toChernSetup X (picardClassOf (S.obj X) L hL) :=
  𝔗.toChernSituation.exists_cohomologicalChernCharacter
    (𝔗.toChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero
      𝔗.algebraMap_mem_grade_zero)

/-! ### Tag 0FIE in the source's own situation -/

/-- **Stacks Project, Tag 0FIE, existence half.** In the standing situation of Section 45.12,
read with the `𝐐`-structure data (D0) and (D1) of Section 45.14 give, there is a rule assigning
to every object `X` of `𝒞` a ring homomorphism

`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`

which is graded, is compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on every
invertible module. With `Stacks.WeilCohomology.eq_of_cohomologicalChernCharacter'` for
uniqueness this is the tag.

**What the situation is.** `Stacks.WeilCohomology.Weak.ChernSetup` is the source's own standing
situation — the data the source fixes, with clause (1), clause (2), clause (3)(a), condition
(1), condition (2), condition (4) and the grading `A(X) = ⨁_{i ≥ 0} A^i(X)`; in particular
`Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum` is a definition and not a field. The section's
three remaining conditions, each in the source's own form, are the arguments `hpull`,
`hcompare` and `hdivisor` (`Stacks.WeilCohomology.PullbackFirstChernCondition`,
`Stacks.WeilCohomology.BundleCompareClause`, `Stacks.WeilCohomology.DivisorDatumClause`), and
the `𝐐`-structure is the `ℚ`-algebra structure on the `A X` together with
`Stacks.WeilCohomology.Weak.ChernSetup.IsRationallyGraded`, which is data (D0) and (D1) of Section
45.14 read for `A`. The `Stacks.WeilCohomology.Weak.ChernSituation` the development is written over
is assembled from those three by `Stacks.WeilCohomology.chernSituationOfSource` inside the
proof, so it is not an argument of this statement, and no
`Stacks.WeilCohomology.Weak.RationalChernSituation` occurs: condition (5), together with clause
(3)(c), is the argument `hdivisor` rather than a field, and the one-degree form of the
`𝐐`-structure is derived by
`Stacks.WeilCohomology.Weak.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded`.

**All three conditions are in the source's own form.** In particular
`Stacks.WeilCohomology.BundleCompareClause` is clause (3)(b) at `f^*ℰ` itself, and not at every
`ℰ'` carrying an isomorphism `f^*ℰ ≅ ℰ'` — that reading would be a closure property clauses (1),
(2) and (3) do not give, since at `f = 𝟙 X` it is the closure of `𝒞` under the `𝐏(ℰ') ⟶ 𝐏(ℰ)`
induced by an arbitrary `ℰ ≅ ℰ'`. The invariance of the total Chern class under an isomorphism of
modules, which `K₀(Vect(X))` forces on any rule out of it, and the pseudofunctoriality coherence
isomorphism `h^*(g^*ℰ) ≅ (h ∘ g)^*ℰ`, which the source has for free, are both theorems:
`Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_eq_of_iso` and
`Stacks.WeilCohomology.Weak.ChernSituation.pull_chernSeries_coeff_of_iso`.

Nothing is assumed beyond that data and those conditions. The
cohomological Chern character of
a single finite locally free module, which the source's proof of this tag cites from the
existence half of Tag 0FI9 and which
`Stacks.WeilCohomology.exists_cohomologicalChernCharacter` leaves open as `chM` with seven
properties, is `Stacks.WeilCohomology.chernCharacterOfModule` with its seven lemmas; the total
Chern classes of Tag 0FI5 those rest on are
`Stacks.WeilCohomology.Weak.ChernSituation.isTotalChernClass_totalChernClass` at the constructed
situation; the rank class `r^A` is `Stacks.WeilCohomology.Weak.ChernSetup.rankClass`, built from
condition (2); and the pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`. -/
theorem exists_cohomologicalChernCharacter_of_source (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔚.A X)] (hgr : 𝔚.IsRationallyGraded)
    (hpull : PullbackFirstChernCondition 𝔚) (hcompare : BundleCompareClause 𝔚)
    (hdivisor : DivisorDatumClause 𝔚) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔚.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule (𝔚 := 𝔚) (chernSituationOfSource 𝔚 hpull hcompare
              hdivisor).isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔚 X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔚.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔚 X (picardClassOf (S.obj X) L hL) :=
  let : ∀ X : C, Algebra ℚ ((chernSituationOfSource 𝔚 hpull hcompare hdivisor).A X) :=
    fun X => (inferInstance : Algebra ℚ (𝔚.A X))
  (chernSituationOfSource 𝔚 hpull hcompare hdivisor).exists_cohomologicalChernCharacter hgr

end

end Stacks.WeilCohomology.Weak

end
