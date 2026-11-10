module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductInstance
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness

/-!
# Exactness of `i_!` for the small crystalline site

Let `(S, I, γ)` be a divided power scheme over `ℤ_{(p)}` and `X` a scheme over `S₀ = V(I)` with
`p` locally nilpotent on `X`.  The inclusion `i : Cris(X/S) ⥤ CRIS(X/S)` of the small crystalline
site into the big one is continuous, cocontinuous and fully faithful, so restriction along it has
a left adjoint `i_!`, and [Stacks, Tag 07IJ] asserts that `i_!` is exact — which is what makes the
retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` a morphism of topoi.

This module supplies the geometric input to that assertion.  The source reduces exactness of
`i_!` to exhibiting objects of `Cris(X/S)` whose representable sheaves cover the final sheaf of
`(X/S)_CRIS`, proves that in the affine case from [Stacks, Tag 07HP], and *omits the proof in
general*.  The omitted covering statement is proved here, in general:
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.coversTop_ι`.

## The covering argument

Let `(U, T, δ)` be an object of `CRIS(X/S)`.  Every point of `T` has an affine open neighbourhood
`W ⊆ T` whose part of `U` maps into an affine open `V ⊆ X`, so the restrictions `(U ∩ W, W, δ|_W)`
form a Zariski covering of `(U, T, δ)` in `CRIS(X/S)`.  Each of those admits a morphism to an
object of `Cris(X/S)`: push out

```
U ∩ W ⟶ W
  |
  v
  V
```

along the thickening `U ∩ W ⟶ W` and the affine morphism `U ∩ W ⟶ V`, [Stacks, Tag 07RT].  The
pushout `P = V ⨿_{U ∩ W} W` is a thickening of `V`, its defining ideal carries a divided power
structure because its sections are a fibre product of the sections of `W` and of `V` over those
of `U ∩ W`, and the resulting object of `CRIS(X/S)` has structure map `V ↪ X` an *open immersion*
— so it already lies in `Cris(X/S)`.  No divided power envelope is needed, and in particular
[Stacks, Tag 07HP] is not used: the argument is uniform in `X`.

## What is and is not proved

* The covering statement `coversTop_ι` is proved unconditionally.  This is the step
  [Stacks, Tag 07IJ] omits.
* Exactness of `i_!`, `preservesFiniteLimits_lowerShriek`, is proved unconditionally.  Its other
  input is the products-of-pairs half of [Stacks, Tag 07IJ]'s own cited result
  [Stacks, Tag 07I9] — "the category `CRIS(X/S)` has all finite nonempty limits, in particular
  products of pairs and fibre products" — and both halves of that are available as global
  instances: `Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening` and
  `Crystalline.GlobalCrystallineSituation.instHasPullbacksThickening`.  Products of pairs are
  what the criterion
  `Stacks.Sites.LowerShriek.sheafPullback_preservesFiniteLimits_of_coversTop` needs in order to
  know that the index category of the pointwise left Kan extension is filtered; the Stacks proof
  uses them for exactly the same purpose ("hint: use that `Cris(X/S)` has products and that the
  functor `Cris(X/S) ⟶ CRIS(X/S)` commutes with them").
* Consequently nothing downstream carries left exactness of `i_!` as a hypothesis: the retraction
  `Crystalline.GlobalCrystallineSituation.CrystallineThickening.retractionMorphism` and the
  morphism of small crystalline topoi
  `Crystalline.GlobalCrystallineSituation.crisMorphism` are unconditional.

## Main results

* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.exists_crystalline_hom_of_affine`
  — an object of `CRIS(X/S)` whose thickened scheme maps affinely to an open of `X` admits a
  morphism to an object of `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.coversTop_ι` — the representable
  sheaves of `Cris(X/S)` cover the final sheaf of `(X/S)_CRIS`.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`
  — `i_!` is exact.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace CrystallineThickening

/-! ### The defining ideal of a closed immersion -/

/-- Over any open, the defining ideal is the kernel of the map on sections. -/
private theorem definingIdeal_obj_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (definingIdeal f).obj (op V) = RingHom.ker (f.app V).hom := rfl

/-- Two ideal subsheaves of the structure sheaf comparable on every affine open are comparable:
membership is a local condition and the affine opens form a basis. -/
private theorem submodule_le_of_le_on_affines {X : Scheme.{u}}
    (I J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (h : ∀ U : X.affineOpens, I.obj (op U.1) ≤ J.obj (op U.1)) : I ≤ J := by
  intro V s hs
  apply J.isSheaf s
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.unop.2
  refine ⟨W, homOfLE hWV, ?_, hxW⟩
  exact h ⟨W, hW⟩ (I.toSubmodule.map_mem (homOfLE hWV).op hs)

/-- The divided power ideal of a thickening is the defining ideal of its closed immersion, on
every open and not only on the affine ones. -/
private theorem ideal_eq_definingIdeal (D : SchemeThickening.{u}) :
    D.target.ideal = definingIdeal D.immersion := by
  have h (U : D.target.scheme.affineOpens) :
      D.target.ideal.obj (op U.1) = (definingIdeal D.immersion).obj (op U.1) :=
    (D.ideal_eq_ker U).trans (definingIdeal_obj D.immersion U).symm
  exact le_antisymm (submodule_le_of_le_on_affines _ _ fun U ↦ (h U).le)
    (submodule_le_of_le_on_affines _ _ fun U ↦ (h U).ge)

/-! ### Divided powers on a fibre product of rings -/

/-- **Divided powers descend to a ring mapping jointly injectively into two divided power
rings.**  Given `f : A → B` and `g : A → C` which are jointly injective, an ideal `I` of `A`
mapping into divided power ideals of `B` and of `C`, and the ability to lift each divided power
of the image of an element of `I` back to `A` simultaneously on both sides, the lifts are a
divided power structure on `I` and both maps are divided power morphisms.

Joint injectivity makes each divided power axiom for the lift provable from the corresponding
axioms downstairs, both sides of the required equation having the same images. -/
private theorem exists_dividedPowers_of_jointly_injective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C)
    (hinj : ∀ {x y}, f x = f y → g x = g y → x = y)
    (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (δ : DividedPowers J) (ε : DividedPowers K)
    (hf : I.map f ≤ J) (hg : I.map g ≤ K)
    (hlift : ∀ n x, x ∈ I → ∃ y, (n ≠ 0 → y ∈ I) ∧
      f y = δ.dpow n (f x) ∧ g y = ε.dpow n (g x)) :
    ∃ γ : DividedPowers I, γ.IsDPMorphism δ f ∧ γ.IsDPMorphism ε g := by
  classical
  let d : ℕ → A → A := fun n x ↦ if hx : x ∈ I then (hlift n x hx).choose else 0
  have hd {n x} (hx : x ∈ I) :
      (n ≠ 0 → d n x ∈ I) ∧ f (d n x) = δ.dpow n (f x) ∧
        g (d n x) = ε.dpow n (g x) := by
    simpa only [d, dite_eq_left hx] using (hlift n x hx).choose_spec
  have hf' {x} (hx : x ∈ I) : f x ∈ J := hf (Ideal.mem_map_of_mem f hx)
  have hg' {x} (hx : x ∈ I) : g x ∈ K := hg (Ideal.mem_map_of_mem g hx)
  let γ : DividedPowers I :=
    { dpow := d
      dpow_null := fun hx ↦ by simp [d, hx]
      dpow_zero := by
        intro x hx
        apply hinj
        · rw [(hd hx).2.1, δ.dpow_zero (hf' hx), map_one]
        · rw [(hd hx).2.2, ε.dpow_zero (hg' hx), map_one]
      dpow_one := by
        intro x hx
        exact hinj ((hd hx).2.1.trans (δ.dpow_one (hf' hx)))
          ((hd hx).2.2.trans (ε.dpow_one (hg' hx)))
      dpow_mem := fun hn hx ↦ (hd hx).1 hn
      dpow_add := by
        intro n x y hx hy
        apply hinj
        · simpa only [(hd (I.add_mem hx hy)).2.1, map_add, map_sum, map_mul,
            (hd hx).2.1, (hd hy).2.1] using δ.dpow_add (n := n) (hf' hx) (hf' hy)
        · simpa only [(hd (I.add_mem hx hy)).2.2, map_add, map_sum, map_mul,
            (hd hx).2.2, (hd hy).2.2] using ε.dpow_add (n := n) (hg' hx) (hg' hy)
      dpow_mul := by
        intro n a x hx
        apply hinj
        · simpa only [(hd (I.mul_mem_left a hx)).2.1, map_mul, map_pow,
            (hd hx).2.1] using δ.dpow_mul (n := n) (a := f a) (hf' hx)
        · simpa only [(hd (I.mul_mem_left a hx)).2.2, map_mul, map_pow,
            (hd hx).2.2] using ε.dpow_mul (n := n) (a := g a) (hg' hx)
      mul_dpow := by
        intro m n x hx
        apply hinj
        · simpa only [map_mul, map_natCast, (hd hx).2.1] using
            δ.mul_dpow (m := m) (n := n) (hf' hx)
        · simpa only [map_mul, map_natCast, (hd hx).2.2] using
            ε.mul_dpow (m := m) (n := n) (hg' hx)
      dpow_comp := by
        intro m n x hn hx
        apply hinj
        · simpa only [(hd ((hd hx).1 hn)).2.1, (hd hx).2.1, map_mul, map_natCast]
            using δ.dpow_comp (m := m) hn (hf' hx)
        · simpa only [(hd ((hd hx).1 hn)).2.2, (hd hx).2.2, map_mul, map_natCast]
            using ε.dpow_comp (m := m) hn (hg' hx) }
  exact ⟨γ, ⟨hf, fun x hx ↦ (hd hx).2.1.symm⟩, ⟨hg, fun x hx ↦ (hd hx).2.2.symm⟩⟩

/-- **The kernel of one leg of a fibre product of rings inherits divided powers from the divided
power ideal of the opposite vertex.**  In a pullback square of commutative rings with `g`
surjective enough that its kernel carries `δ`, the kernel of `a` carries divided powers for which
`b` is a divided power morphism: the two legs out of the pullback are jointly injective, and a
divided power of an element of `ker a` is lifted by pairing the trivial divided power upstairs
with `δ` downstairs. -/
private theorem exists_dividedPowers_of_isPullback
    {P A B C : CommRingCat} {a : P ⟶ A} {b : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback a b f g)
    {I : Ideal B} (δ : DividedPowers I) (hI : I = RingHom.ker g.hom) :
    ∃ γ : DividedPowers (RingHom.ker a.hom), γ.IsDPMorphism δ b.hom := by
  subst I
  have ht := h.map (CategoryTheory.forget CommRingCat)
  have hb {x : P} (hx : x ∈ RingHom.ker a.hom) : b x ∈ RingHom.ker g.hom := by
    have he := ConcreteCategory.congr_hom h.w x
    change f (a x) = g (b x) at he
    rw [RingHom.mem_ker.mp hx, map_zero] at he
    exact he.symm
  obtain ⟨γ, _, hγ⟩ := exists_dividedPowers_of_jointly_injective a.hom b.hom
    (Types.ext_of_isPullback ht) (RingHom.ker a.hom) ⊥ (RingHom.ker g.hom)
    (dividedPowersBot A) δ
    (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ hx)
    (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ hb hx) (by
      intro n x hx
      obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback ht
        ((dividedPowersBot A).dpow n (a x)) (δ.dpow n (b x)) (by
          change f.hom ((dividedPowersBot A).dpow n (a x)) = g.hom (δ.dpow n (b x))
          obtain rfl | hn := eq_or_ne n 0
          · rw [DividedPowers.dpow_zero _ (show a x ∈ (⊥ : Ideal A) from hx),
              δ.dpow_zero (hb hx), map_one, map_one]
          · rw [show (dividedPowersBot A).dpow n (a x) = 0 from
                (dividedPowersBot A).dpow_mem hn (show a x ∈ (⊥ : Ideal A) from hx),
              map_zero]
            exact (RingHom.mem_ker.mp (δ.dpow_mem hn (hb hx))).symm)
      refine ⟨y, fun hn ↦ ?_, hy₁, hy₂⟩
      change a y = 0
      exact hy₁.trans ((dividedPowersBot A).dpow_mem hn
        (show a x ∈ (⊥ : Ideal A) from hx)))
  exact ⟨γ, hγ⟩

/-- **A divided power morphism can be cancelled on the right against an injective one.**  If
`g ∘ f` is a divided power morphism and `g` is one which is injective on the middle divided power
ideal, then `f` is a divided power morphism. -/
private theorem isDPMorphism_of_comp_of_injOn
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (δ : DividedPowers I) (ε : DividedPowers J) (ζ : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (hf : I.map f ≤ J)
    (hg : ε.IsDPMorphism ζ g) (hgf : δ.IsDPMorphism ζ (g.comp f))
    (hinj : Set.InjOn g J) : δ.IsDPMorphism ε f := by
  refine ⟨hf, ?_⟩
  intro n x hx
  have hfx : f x ∈ J := hf (Ideal.mem_map_of_mem f hx)
  obtain rfl | hn := eq_or_ne n 0
  · rw [ε.dpow_zero hfx, δ.dpow_zero hx, map_one]
  exact hinj (ε.dpow_mem hn hfx) (hf (Ideal.mem_map_of_mem f (δ.dpow_mem hn hx)))
    ((hg.map_dpow hfx).trans (hgf.dpow_comp x hx))

/-! ### The divided power structure on the pushout -/

/-- On sections over any open, the first leg of the pushout of a thickening along an affine
morphism is injective on the defining ideal of the second leg, [Stacks, Tag 07RT]. -/
private theorem injOn_pushout_inl_app (D : SchemeThickening.{u}) {Y : Scheme.{u}}
    (f : D.source ⟶ Y) [IsAffineHom f] [HasPushout D.immersion f]
    (U : (pushout D.immersion f).Opens) :
    Set.InjOn ((pushout.inl D.immersion f).app U).hom
      (Crystalline.sectionIdeal (pushout D.immersion f).sheaf
        (definingIdeal (pushout.inr D.immersion f)) (op U) :
          Set ((pushout D.immersion f).sheaf.obj.obj (op U))) := by
  intro x hx y hy he
  exact Types.ext_of_isPullback
    ((Stacks.Pushout.pushout_structureSheaf_isPullback
      Stacks.Thickenings.forall_isAffine_of_isThickening D.immersion f D.isThickening
      U).map (CategoryTheory.forget CommRingCat))
    (show (pushout.inr D.immersion f |>.app U) x = (pushout.inr D.immersion f |>.app U) y from
      hx.trans hy.symm) he

/-- **The pushout of a thickening along an affine morphism carries a divided power structure on
its defining ideal, for which the map from the thickened scheme is a divided power morphism.**

On each open of the pushout the ring of sections is a fibre product of the sections of the two
vertices over those of the source, [Stacks, Tag 07RT], and `exists_dividedPowers_of_isPullback`
transports the divided powers of the thickening across that fibre product.  Naturality holds
because the two legs of the fibre product are jointly injective, so it suffices to check the
divided power compatibility after composing with one of them. -/
theorem exists_pushout_dividedPowerStructure
    (D : SchemeThickening.{u}) {Y : Scheme.{u}}
    (f : D.source ⟶ Y) [IsAffineHom f] [HasPushout D.immersion f] :
    ∃ γ : DividedPowerStructure.{u, u, u} (pushout D.immersion f).sheaf
        (definingIdeal (pushout.inr D.immersion f)),
      ∀ U, (γ.dividedPowers (op U)).IsDPMorphism
        (D.target.dividedPowers.dividedPowers (op ((pushout.inl D.immersion f) ⁻¹ᵁ U)))
        ((pushout.inl D.immersion f).app U).hom := by
  have H := Stacks.Thickenings.forall_isAffine_of_isThickening
  set a := pushout.inl D.immersion f with ha
  set b := pushout.inr D.immersion f with hb
  have hγ (U : (pushout D.immersion f).Opens) :
      ∃ γ : DividedPowers ((definingIdeal b).obj (op U)), γ.IsDPMorphism
        (D.target.dividedPowers.dividedPowers (op (a ⁻¹ᵁ U))) (a.app U).hom := by
    have e : D.immersion ⁻¹ᵁ (a ⁻¹ᵁ U) = f ⁻¹ᵁ (b ⁻¹ᵁ U) :=
      congrArg (fun g : D.source ⟶ pushout D.immersion f ↦ g ⁻¹ᵁ U) pushout.condition
    set g := D.immersion.app (a ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V ↦ Γ(D.source, V)) e) with hg
    have h : IsPullback (b.app U) (a.app U) (f.app (b ⁻¹ᵁ U)) g :=
      Stacks.Pushout.pushout_structureSheaf_isPullback H D.immersion f D.isThickening U
    have hk : D.target.ideal.obj (op (a ⁻¹ᵁ U)) = RingHom.ker g.hom := by
      rw [ideal_eq_definingIdeal D, definingIdeal_obj_eq_ker, hg]
      exact (RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso
        (eqToHom (congrArg (fun V ↦ Γ(D.source, V)) e))).injective).symm
    exact exists_dividedPowers_of_isPullback h
      (D.target.dividedPowers.dividedPowers (op (a ⁻¹ᵁ U))) hk
  choose γ hγ using hγ
  refine ⟨{ dividedPowers := fun U ↦ γ U.unop, naturality := ?_ }, hγ⟩
  intro U V q
  have hm : (Crystalline.sectionIdeal (pushout D.immersion f).sheaf (definingIdeal b) U).map
      ((pushout D.immersion f).sheaf.obj.map q).hom ≤
      Crystalline.sectionIdeal (pushout D.immersion f).sheaf (definingIdeal b) V :=
    Ideal.map_le_iff_le_comap.mpr fun x hx ↦ (definingIdeal b).toSubmodule.map_mem q hx
  apply isDPMorphism_of_comp_of_injOn (γ U.unop) (γ V.unop)
    (D.target.dividedPowers.dividedPowers (op (a ⁻¹ᵁ V.unop)))
    ((pushout D.immersion f).sheaf.obj.map q).hom (a.app V.unop).hom hm (hγ V.unop)
  · refine Crystalline.isDPMorphism_of_eq ?_
      (DividedPowers.IsDPMorphism.comp _ (D.target.dividedPowers.naturality
        ((TopologicalSpace.Opens.map a.base).map q.unop).op) (hγ U.unop))
    exact (congrArg CommRingCat.Hom.hom (a.naturality q)).symm
  · exact injOn_pushout_inl_app D f V.unop

/-! ### The pushout of a divided power thickening, as an object of the site -/

/-- **The pushout of a divided power thickening along an affine morphism exists**,
[Stacks, Tag 07RT]. -/
instance hasPushout_immersion (D : SchemeThickening.{u}) {Y : Scheme.{u}} (g : D.source ⟶ Y)
    [IsAffineHom g] : HasPushout D.immersion g :=
  Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom
    Stacks.Thickenings.forall_isAffine_of_isThickening D.immersion g D.isThickening

section Pushout

variable (D : SchemeThickening.{u}) {Y : Scheme.{u}} (g : D.source ⟶ Y) [IsAffineHom g]

/-- The second leg of the pushout of a divided power thickening along an affine morphism is again
a thickening, [Stacks, Tag 07RT]. -/
theorem isThickening_pushout_inr :
    Stacks.Thickenings.IsThickening (pushout.inr D.immersion g) :=
  Stacks.Pushout.pushout_inr_isThickening Stacks.Thickenings.forall_isAffine_of_isThickening
    D.immersion g D.isThickening

/-- The second leg of the pushout of a divided power thickening along an affine morphism is a
closed immersion, being a thickening. -/
instance isClosedImmersion_pushout_inr :
    IsClosedImmersion (pushout.inr D.immersion g) :=
  (isThickening_pushout_inr D g).1

/-- **The pushout of a divided power thickening along an affine morphism, as a divided power
thickening.**  The thickened scheme is the pushout `T ⊔_U Y` of [Stacks, Tag 07RT], its defining
ideal is the one of the second leg, and the divided power structure is the one transported across
the fibre product of sections by `exists_pushout_dividedPowerStructure`. -/
@[implicit_reducible]
noncomputable def pushoutSchemeThickening : SchemeThickening.{u} where
  source := Y
  target :=
    { scheme := pushout D.immersion g
      ideal := definingIdeal (pushout.inr D.immersion g)
      isQuasicoherent := definingIdeal_isQuasicoherent _
      dividedPowers := (exists_pushout_dividedPowerStructure D g).choose }
  immersion := pushout.inr D.immersion g
  isThickening := isThickening_pushout_inr D g
  ideal_eq_ker := definingIdeal_obj _

/-- **The first leg of the pushout square, as a divided power morphism.**  That it is one is the
conclusion of `exists_pushout_dividedPowerStructure`. -/
@[implicit_reducible]
noncomputable def pushoutInl : D.target ⟶ (pushoutSchemeThickening D g).target where
  hom := pushout.inl D.immersion g
  compatible := (exists_pushout_dividedPowerStructure D g).choose_spec

/-- **A morphism out of the pushout is a divided power morphism** as soon as its restriction along
the first leg is one and its restriction along the second kills the divided power ideal of the
target.

The sections of the pushout over an open are a fibre product of those of the two vertices over
those of the source, [Stacks, Tag 07RT], so the first leg is injective on the divided power ideal
of the pushout — the second leg kills it — and `isDPMorphism_of_comp_of_injOn` cancels it. -/
theorem isDPMorphism_pushout_desc (Z : DividedPowerScheme.{u})
    (w : pushout D.immersion g ⟶ Z.scheme)
    (h₁ : ∀ U : Z.scheme.Opens, (Z.dividedPowers.dividedPowers (op U)).IsDPMorphism
      (D.target.dividedPowers.dividedPowers (op ((pushout.inl D.immersion g ≫ w) ⁻¹ᵁ U)))
      (((pushout.inl D.immersion g ≫ w).app U).hom))
    (h₂ : ∀ (U : Z.scheme.Opens) (x : Γ(Z.scheme, U)),
      x ∈ Crystalline.sectionIdeal Z.scheme.sheaf Z.ideal (op U) →
      ((pushout.inr D.immersion g ≫ w).app U).hom x = 0)
    (U : Z.scheme.Opens) :
    (Z.dividedPowers.dividedPowers (op U)).IsDPMorphism
      ((pushoutSchemeThickening D g).target.dividedPowers.dividedPowers (op (w ⁻¹ᵁ U)))
      ((w.app U).hom) := by
  have hideal : (Crystalline.sectionIdeal Z.scheme.sheaf Z.ideal (op U)).map (w.app U).hom ≤
      Crystalline.sectionIdeal (pushout D.immersion g).sheaf
        (definingIdeal (pushout.inr D.immersion g)) (op (w ⁻¹ᵁ U)) := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    change ((pushout.inr D.immersion g ≫ w).app U).hom x = 0
    exact h₂ U x hx
  change (Z.dividedPowers.dividedPowers (op U)).IsDPMorphism
    ((exists_pushout_dividedPowerStructure D g).choose.dividedPowers (op (w ⁻¹ᵁ U)))
    ((w.app U).hom)
  refine isDPMorphism_of_comp_of_injOn _ _
    (D.target.dividedPowers.dividedPowers (op (pushout.inl D.immersion g ⁻¹ᵁ (w ⁻¹ᵁ U))))
    (w.app U).hom (pushout.inl D.immersion g |>.app (w ⁻¹ᵁ U)).hom hideal
    ((exists_pushout_dividedPowerStructure D g).choose_spec (w ⁻¹ᵁ U)) (h₁ U) ?_
  exact injOn_pushout_inl_app D g (w ⁻¹ᵁ U)

/-- **The morphism out of the pushout determined by its two legs**, as a divided power morphism:
`pushout.desc`, which is a divided power morphism by `isDPMorphism_pushout_desc`. -/
noncomputable def pushoutDesc (Z : DividedPowerScheme.{u}) (w₁ : D.target ⟶ Z)
    (s : Y ⟶ Z.scheme) (hw : D.immersion ≫ w₁.hom = g ≫ s)
    (hs : ∀ (U : Z.scheme.Opens) (x : Γ(Z.scheme, U)),
      x ∈ Crystalline.sectionIdeal Z.scheme.sheaf Z.ideal (op U) → ((s.app U).hom) x = 0) :
    (pushoutSchemeThickening D g).target ⟶ Z where
  hom := pushout.desc w₁.hom s hw
  compatible := isDPMorphism_pushout_desc D g Z _
    (fun U ↦ by rw [pushout.inl_desc]; exact w₁.compatible U)
    (fun U x hx ↦ by rw [pushout.inr_desc]; exact hs U x hx)

/-- The morphism of schemes underlying `pushoutDesc` is `pushout.desc`. -/
@[simp]
theorem pushoutDesc_hom (Z : DividedPowerScheme.{u}) (w₁ : D.target ⟶ Z) (s : Y ⟶ Z.scheme)
    (hw : D.immersion ≫ w₁.hom = g ≫ s)
    (hs : ∀ (U : Z.scheme.Opens) (x : Γ(Z.scheme, U)),
      x ∈ Crystalline.sectionIdeal Z.scheme.sheaf Z.ideal (op U) → ((s.app U).hom) x = 0) :
    (pushoutDesc D g Z w₁ s hw hs).hom = pushout.desc w₁.hom s hw :=
  rfl

/-- **The morphism out of the pushout into the thickened scheme of another divided power
thickening**, determined by a divided power morphism from the ambient scheme and a morphism to the
thickened scheme.  The divided power ideal of the target is killed because the map factors through
the immersion, `Crystalline.SchemeThickening.immersion_app_eq_zero_of_mem`. -/
noncomputable def pushoutDescThickening (E : SchemeThickening.{u}) (w₁ : D.target ⟶ E.target)
    (s : Y ⟶ E.source) (hw : D.immersion ≫ w₁.hom = g ≫ s ≫ E.immersion) :
    (pushoutSchemeThickening D g).target ⟶ E.target :=
  pushoutDesc D g E.target w₁ (s ≫ E.immersion) hw (fun U x hx ↦
    comp_app_eq_zero s E.immersion U x (E.immersion_app_eq_zero_of_mem U x hx))

/-- The morphism of schemes underlying `pushoutDescThickening` is `pushout.desc`. -/
@[simp]
theorem pushoutDescThickening_hom (E : SchemeThickening.{u}) (w₁ : D.target ⟶ E.target)
    (s : Y ⟶ E.source) (hw : D.immersion ≫ w₁.hom = g ≫ s ≫ E.immersion) :
    (pushoutDescThickening D g E w₁ s hw).hom = pushout.desc w₁.hom (s ≫ E.immersion) hw :=
  rfl

/-- The morphism out of the pushout determined by two legs restricts along the first leg to the
first of them. -/
@[simp]
theorem pushoutInl_comp_pushoutDescThickening (E : SchemeThickening.{u})
    (w₁ : D.target ⟶ E.target) (s : Y ⟶ E.source)
    (hw : D.immersion ≫ w₁.hom = g ≫ s ≫ E.immersion) :
    pushoutInl D g ≫ pushoutDescThickening D g E w₁ s hw = w₁ :=
  DividedPowerScheme.Hom.ext (pushout.inl_desc _ _ _)

/-- The morphism out of the pushout determined by two legs restricts along the second leg to the
second of them. -/
@[simp]
theorem immersion_comp_pushoutDescThickening (E : SchemeThickening.{u})
    (w₁ : D.target ⟶ E.target) (s : Y ⟶ E.source)
    (hw : D.immersion ≫ w₁.hom = g ≫ s ≫ E.immersion) :
    (pushoutSchemeThickening D g).immersion ≫ (pushoutDescThickening D g E w₁ s hw).hom =
      s ≫ E.immersion :=
  pushout.inr_desc (f := D.immersion) (g := g) _ _ _

/-- **Two divided power morphisms out of the ambient scheme of the pushout agree as soon as they
agree after the two legs of the pushout square.**  This is `pushout.hom_ext`, a divided power
morphism being determined by the underlying morphism of schemes. -/
theorem pushout_dividedPowerHom_ext {Z : DividedPowerScheme.{u}}
    {p q : (pushoutSchemeThickening D g).target ⟶ Z}
    (h₁ : pushoutInl D g ≫ p = pushoutInl D g ≫ q)
    (h₂ : (pushoutSchemeThickening D g).immersion ≫ p.hom =
      (pushoutSchemeThickening D g).immersion ≫ q.hom) :
    p = q :=
  DividedPowerScheme.Hom.ext
    (pushout.hom_ext (congrArg DividedPowerScheme.Hom.hom h₁) h₂)

end Pushout

section CrystallinePushout

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S) (V : S.X.Opens)
  (f : A.thickening.source ⟶ (V : Scheme.{u})) [IsAffineHom f] (hf : f ≫ V.ι = A.toX)

/-- **The object of `Cris(X/S)` produced by pushing out a thickening along an affine map to an
open of `X`**, [Stacks, Tag 07RT]: the open `V` of `X`, thickened by `T ⊔_U V`.  Its structure map
to `X` is the open immersion `V ↪ X`, so it does lie in the small site, and its structure morphism
to the divided power base is the one induced by `T ⟶ S` and by `V ↪ X ⟶ S`, the latter killing the
divided power ideal of `S` because it factors through the closed fibre. -/
@[implicit_reducible]
noncomputable def crystallinePushoutObj : Thickening S where
  thickening := pushoutSchemeThickening A.thickening f
  toBase := pushoutDesc A.thickening f S.S A.toBase (V.ι ≫ sourceToBase S)
    (by rw [← Category.assoc, hf]; exact A.over_base)
    (fun U x hx ↦ sourceToBase_app_eq_zero S V.ι U x hx)
  toX := V.ι
  over_base := by exact pushout.inr_desc (f := A.thickening.immersion) (g := f) _ _ _

/-- **The object of `Cris(X/S)` produced by the pushout**, `crystallinePushoutObj` together with
the open immersion `V ↪ X` which places it in the small site. -/
@[implicit_reducible]
noncomputable def crystallinePushout : CrystallineThickening S :=
  ⟨crystallinePushoutObj S A V f hf, inferInstanceAs (IsOpenImmersion V.ι)⟩

/-- **The morphism of `CRIS(X/S)` from a thickening to the object `crystallinePushout` produced
from it.**  On thickened schemes it is the affine map `U ⟶ V`, and on ambient schemes the first leg
of the pushout square. -/
@[implicit_reducible]
noncomputable def crystallinePushoutHom :
    A ⟶ (CrystallineThickening.ι S).obj (crystallinePushout S A V f hf) where
  sourceHom := f
  targetHom := pushoutInl A.thickening f
  immersion_naturality := pushout.condition
  base_naturality := DividedPowerScheme.Hom.ext (pushout.inl_desc _ _ _)
  toX_naturality := hf

/-- The structure map to `X` of the object produced by a pushout is the open immersion of `V`. -/
@[simp]
theorem crystallinePushout_toX :
    (crystallinePushout S A V f hf).obj.toX = V.ι :=
  rfl

/-- On thickened schemes, the morphism to the object produced by a pushout is the affine map that
was pushed out. -/
@[simp]
theorem crystallinePushoutHom_sourceHom :
    (crystallinePushoutHom S A V f hf).sourceHom = f :=
  rfl

/-- On ambient schemes, the morphism to the object produced by a pushout is the first leg of the
pushout square. -/
@[simp]
theorem crystallinePushoutHom_targetHom_hom :
    (crystallinePushoutHom S A V f hf).targetHom.hom = pushout.inl A.thickening.immersion f :=
  rfl

/-- On ambient schemes, the morphism to the object produced by a pushout is the first leg of the
pushout square, as a divided power morphism. -/
@[simp]
theorem crystallinePushoutHom_targetHom_targetHom :
    (crystallinePushoutHom S A V f hf).targetHom = pushoutInl A.thickening f :=
  rfl

/-- The immersion of the object produced by a pushout is the second leg of the pushout square. -/
@[simp]
theorem crystallinePushout_immersion :
    (crystallinePushout S A V f hf).obj.thickening.immersion =
      pushout.inr A.thickening.immersion f :=
  rfl

/-- **Two morphisms out of the ambient scheme of the object produced by a pushout agree as soon as
they agree after the two legs of the pushout square**, which are the ambient part of
`crystallinePushoutHom` and the immersion of the produced object.  This is `pushout.hom_ext`, and
it is what makes a morphism out of the produced object unique once its restriction to the
thickening it came from and its value on `V` are prescribed. -/
theorem crystallinePushout_target_hom_ext {Z : Scheme.{u}}
    {p q : (crystallinePushout S A V f hf).obj.thickening.target.scheme ⟶ Z}
    (h₁ : (crystallinePushoutHom S A V f hf).targetHom.hom ≫ p =
      (crystallinePushoutHom S A V f hf).targetHom.hom ≫ q)
    (h₂ : (crystallinePushout S A V f hf).obj.thickening.immersion ≫ p =
      (crystallinePushout S A V f hf).obj.thickening.immersion ≫ q) :
    p = q :=
  pushout.hom_ext h₁ h₂

/-- **Two divided power morphisms out of the ambient scheme of the object produced by a pushout
agree as soon as they agree after the morphism from `A` and after the immersion of the produced
object**, those being the two legs of the pushout square. -/
theorem crystallinePushout_dividedPowerHom_ext {Z : DividedPowerScheme.{u}}
    {p q : (crystallinePushout S A V f hf).obj.thickening.target ⟶ Z}
    (h₁ : (crystallinePushoutHom S A V f hf).targetHom ≫ p =
      (crystallinePushoutHom S A V f hf).targetHom ≫ q)
    (h₂ : (crystallinePushout S A V f hf).obj.thickening.immersion ≫ p.hom =
      (crystallinePushout S A V f hf).obj.thickening.immersion ≫ q.hom) :
    p = q :=
  pushout_dividedPowerHom_ext A.thickening f h₁ h₂

/-- The morphism out of the object produced by a pushout determined by two legs restricts along
the morphism from `A` to the first of them. -/
@[simp]
theorem crystallinePushoutHom_targetHom_comp_pushoutDescThickening (E : SchemeThickening.{u})
    (w₁ : A.thickening.target ⟶ E.target) (s : (V : Scheme.{u}) ⟶ E.source)
    (hw : A.thickening.immersion ≫ w₁.hom = f ≫ s ≫ E.immersion) :
    (crystallinePushoutHom S A V f hf).targetHom ≫
        pushoutDescThickening A.thickening f E w₁ s hw = w₁ :=
  pushoutInl_comp_pushoutDescThickening A.thickening f E w₁ s hw

/-- The morphism out of the object produced by a pushout determined by two legs restricts along
the immersion of that object to the second of them. -/
@[simp]
theorem crystallinePushout_immersion_comp_pushoutDescThickening (E : SchemeThickening.{u})
    (w₁ : A.thickening.target ⟶ E.target) (s : (V : Scheme.{u}) ⟶ E.source)
    (hw : A.thickening.immersion ≫ w₁.hom = f ≫ s ≫ E.immersion) :
    (crystallinePushout S A V f hf).obj.thickening.immersion ≫
        (pushoutDescThickening A.thickening f E w₁ s hw).hom = s ≫ E.immersion :=
  immersion_comp_pushoutDescThickening A.thickening f E w₁ s hw

end CrystallinePushout

/-! ### From an affine factorization to an object of the small site -/

/-- **An object of `CRIS(X/S)` whose thickened scheme maps affinely into an open of `X` admits a
morphism to an object of `Cris(X/S)`.**

Push out the thickening `U ⟶ T` of `A` along the affine morphism `U ⟶ V`, [Stacks, Tag 07RT].
The pushout `P` is a thickening of `V`, its defining ideal carries a divided power structure by
`exists_pushout_dividedPowerStructure`, and `P ⟶ S` is the map induced by `T ⟶ S` and by
`V ↪ X ⟶ S`, the latter killing the divided power ideal of `S` because it factors through the
closed fibre.  The resulting object has structure map `V ↪ X`, an open immersion, so it lies in
`Cris(X/S)`.

The open of `X` the produced object lies over is `V` itself, and that is recorded: the conclusion
says that the image of its structure map is contained in the image of `V`.  Consumers which have
to keep the produced object inside a prescribed open of `X` — the relative covering statement
`Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve_mem` of
`SmallSite/CrisZariskiSquareCovering.lean` — need exactly that. -/
theorem exists_crystalline_hom_of_affine (S : GlobalCrystallineSituation.{u})
    (A : Thickening S) (V : S.X.Opens)
    (f : A.thickening.source ⟶ (V : Scheme.{u})) [IsAffineHom f]
    (hf : f ≫ V.ι = A.toX) :
    ∃ B : CrystallineThickening S,
      Set.range B.obj.toX.base ⊆ Set.range V.ι.base ∧ Nonempty (A ⟶ (ι S).obj B) :=
  ⟨crystallinePushout S A V f hf, subset_rfl, ⟨crystallinePushoutHom S A V f hf⟩⟩

/-! ### The covering of the big site by the small one -/

/-- **Every point of the thickened scheme of an object of `CRIS(X/S)` has an affine open
neighbourhood whose part of `U` maps into an affine open of `X`.**  The thickening is a
homeomorphism on points, so the preimage of an affine neighbourhood of the image point in `X` is
an open of `U`, whose image is open in `T`; shrink it to an affine open. -/
private theorem exists_affine_neighbourhood_toX (S : GlobalCrystallineSituation.{u})
    (A : Thickening S) (x : A.thickening.target.scheme) :
    ∃ (W : A.thickening.target.scheme.affineOpens) (V : S.X.affineOpens),
      x ∈ W.1 ∧ A.thickening.immersion ⁻¹ᵁ W.1 ≤ A.toX ⁻¹ᵁ V.1 := by
  obtain ⟨z, rfl⟩ := A.thickening.isThickening.2 x
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show A.toX z ∈ (⊤ : S.X.Opens) from trivial)
  have ho := (A.thickening.immersion.isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective
    A.thickening.isThickening.2).isOpenMap
  set O : A.thickening.target.scheme.Opens :=
    ⟨A.thickening.immersion '' (A.toX ⁻¹ᵁ V), ho _ (A.toX ⁻¹ᵁ V).2⟩
  obtain ⟨W, hW, hzW, hWO⟩ := exists_isAffineOpen_mem_and_subset
    (show A.thickening.immersion z ∈ O from ⟨z, hzV, rfl⟩)
  refine ⟨⟨W, hW⟩, ⟨V, hV⟩, hzW, fun y hy ↦ ?_⟩
  obtain ⟨y', hy', he⟩ := hWO hy
  exact A.thickening.immersion.isClosedEmbedding.injective he ▸ hy'

/-- **Stacks Project, Tag 07IJ, clause (6), the covering step.**  The representable sheaves of the
objects of `Cris(X/S)` cover the final sheaf of `(X/S)_CRIS`: every object of `CRIS(X/S)` has a
Zariski covering each member of which admits a morphism to an object of `Cris(X/S)`.

This is the step the source omits in general.  Cover the thickened scheme of `A` by the affine
opens `W` supplied by `exists_affine_neighbourhood_toX`; the restriction of `A` to `W` has
thickened scheme `W` and its part of `U` maps into an affine open `V` of `X`, hence affinely,
so `exists_crystalline_hom_of_affine` applies to it. -/
@[stacks 07IJ "clause (6), the covering step: the representables of Cris(X/S) cover the final \
sheaf of (X/S)_CRIS, which the source omits in general"]
theorem coversTop_ι (S : GlobalCrystallineSituation.{u}) :
    (topology S).CoversTop (ι S).obj := by
  intro A
  choose W V hxW hWV using exists_affine_neighbourhood_toX S A
  set Wfam : ULift.{u + 1} A.thickening.target.scheme → A.thickening.target.scheme.Opens :=
    fun i ↦ (W i.down).1
  have hcov : Thickening.IsZariskiCovering (A.restrictOpenCover Wfam) :=
    A.isZariskiCovering_restrictOpenCover Wfam fun x ↦ ⟨⟨x⟩, hxW x⟩
  apply (topology S).superset_covering _
    (zariskiCovering_mem_topology S (A.restrictOpenCover Wfam) hcov)
  rw [Sieve.generate_le_iff]
  intro B g hg
  cases hg with
  | mk i =>
    have : IsAffine ((W i.down).1 : Scheme.{u}) := (W i.down).property
    have : IsAffine ((V i.down).1 : Scheme.{u}) := (V i.down).property
    have : IsAffine (A.restrictOpen (W i.down).1).thickening.target.scheme :=
      inferInstanceAs (IsAffine ((W i.down).1 : Scheme.{u}))
    have : IsAffine (A.restrictOpen (W i.down).1).thickening.source :=
      isAffine_of_isAffineHom (A.restrictOpen (W i.down).1).thickening.immersion
    have hrange : Set.range (A.restrictOpen (W i.down).1).toX ⊆
        Set.range (V i.down).1.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, hWV i.down z.property⟩, rfl⟩
    set lift := IsOpenImmersion.lift (V i.down).1.ι
      (A.restrictOpen (W i.down).1).toX hrange
    obtain ⟨Bsmall, -, hne⟩ := exists_crystalline_hom_of_affine S
      (A.restrictOpen (W i.down).1) (V i.down).1 lift
      (IsOpenImmersion.lift_fac _ _ _)
    exact ⟨Bsmall, hne⟩

/-! ### Exactness of `i_!` -/

/-- **Stacks Project, Tag 07IJ, clause (6): the lower shriek `i_!` along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` is exact.**

Lower shriek is right exact, being a left adjoint, and preserves fibre products because the index
category of the pointwise left Kan extension along `i` is filtered.  What remains is the final
sheaf, and that is `coversTop_ι`: the representables of `Cris(X/S)` cover it.  Both halves are
`Stacks.Sites.LowerShriek.sheafPullback_preservesFiniteLimits_of_coversTop`.

What makes that index category filtered is products of pairs in `CRIS(X/S)`, the first half of
[Stacks, Tag 07I9], which [Stacks, Tag 07IJ] cites; it is the global instance
`Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening`, and the Stacks proof of
this clause invokes products of `Cris(X/S)` for the same reason. -/
@[stacks 07IJ "clause (6): i_! is exact, whose covering step -- the part the source omits in \
general -- is coversTop_ι"]
theorem preservesFiniteLimits_lowerShriek (S : GlobalCrystallineSituation.{u}) :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback (ι S)
      (Type (u + 1)) (smallTopology S) (topology S)) := by
  have : HasBinaryProducts (CrystallineThickening S) := inferInstance
  have : PreservesLimitsOfShape (Discrete WalkingPair) (ι S) := inferInstance
  have := Stacks.Sites.LowerShriek.sheafPullback_preservesFiniteLimits_of_coversTop
    (ι S) (smallTopology S) (topology S) (coversTop_ι S)
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (ι S) (Type (u + 1))
      (smallTopology S) (topology S))

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation

end
