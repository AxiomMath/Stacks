module

public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Cartesian squares over van Kampen coproducts

Consequences of the van Kampen property, and of universality, of a coproduct `G = ∐ Gᵢ`.

## Main definitions

* `CategoryTheory.IsUniversalColimit.isColimitCofanPullback`: for `a : X ⟶ G` with `G` a
  universal coproduct, `X` is the coproduct of the `X ×_G Gᵢ`.

## Main results

* `CategoryTheory.IsVanKampenColimit.isPullback_inj`: if `A = ∐ Aᵢ` is a coproduct and
  `F : A ⟶ G` restricts to `fᵢ : Aᵢ ⟶ Gᵢ` on the summands, then each square
  `Aᵢ ⟶ A`, `Gᵢ ⟶ G` is cartesian.
* `CategoryTheory.IsUniversalColimit.isPullback_of_forall_isPullback`: a commutative square
  `k ≫ b = a ≫ c` with `a : X ⟶ G` is cartesian as soon as its restriction to every summand
  `X ×_G Gᵢ` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] {I : Type w}

/-- **A coproduct of morphisms is cartesian over the coproduct inclusions**, when the target
coproduct is van Kampen. -/
theorem IsVanKampenColimit.isPullback_inj {A G : I → C} {cA : Cofan A} {cG : Cofan G}
    (hA : IsColimit cA) (hG : IsVanKampenColimit cG) (f : ∀ i, A i ⟶ G i) (F : cA.pt ⟶ cG.pt)
    (hF : ∀ i, cA.inj i ≫ F = f i ≫ cG.inj i) (i : I) :
    IsPullback (cA.inj i) (f i) F (cG.inj i) :=
  (hG cA (Discrete.natTrans fun k => f k.as) F (by ext ⟨m⟩; exact (hF m).symm)
    (.of_discrete _)).mp ⟨hA⟩ ⟨i⟩

variable [HasPullbacks C]

/-- **Universality of a coproduct decomposes an object over it.** For `a : X ⟶ G` with
`G = ∐ Gᵢ` universal, `X` is the coproduct of the `X ×_G Gᵢ`. -/
noncomputable def IsUniversalColimit.isColimitCofanPullback {G : I → C} {cG : Cofan G}
    (hG : IsUniversalColimit cG) {X : C} (a : X ⟶ cG.pt) :
    IsColimit (Cofan.mk X fun i => pullback.fst a (cG.inj i)) := by
  refine Classical.choice (hG (Cofan.mk X fun i => pullback.fst a (cG.inj i))
    (Discrete.natTrans fun k => pullback.snd a (cG.inj k.as)) a ?_ (.of_discrete _) ?_)
  · ext ⟨m⟩
    exact pullback.condition.symm
  · rintro ⟨m⟩
    exact IsPullback.of_hasPullback a (cG.inj m)

/-- **A square over a universal coproduct is cartesian if it is so summand by summand.** -/
theorem IsUniversalColimit.isPullback_of_forall_isPullback {G : I → C} {cG : Cofan G}
    (hG : IsUniversalColimit cG) {X Z H : C} (k : X ⟶ Z) (a : X ⟶ cG.pt) (b : Z ⟶ H)
    (c : cG.pt ⟶ H) (w : k ≫ b = a ≫ c)
    (hi : ∀ i, IsPullback (pullback.fst a (cG.inj i) ≫ k) (pullback.snd a (cG.inj i)) b
      (cG.inj i ≫ c)) :
    IsPullback k a b c := by
  let t : pullback b c ⟶ cG.pt := pullback.snd b c
  let m : X ⟶ pullback b c := pullback.lift k a w
  have hX := hG.isColimitCofanPullback a
  have hP := hG.isColimitCofanPullback t
  have hPi : ∀ i, IsPullback (pullback.fst t (cG.inj i) ≫ pullback.fst b c)
      (pullback.snd t (cG.inj i)) b (cG.inj i ≫ c) := fun i =>
    (IsPullback.of_hasPullback t (cG.inj i)).paste_horiz (IsPullback.of_hasPullback b c)
  let e : ∀ i, pullback a (cG.inj i) ≅ pullback t (cG.inj i) := fun i =>
    (hi i).isoIsPullback _ _ (hPi i)
  have hcompat : ∀ i, pullback.fst a (cG.inj i) ≫ m = (e i).hom ≫ pullback.fst t (cG.inj i) :=
    fun i => pullback.hom_ext (by simp [m, e, pullback.lift_fst])
      (by simp [m, e, t, pullback.lift_snd, pullback.condition])
  let inv : pullback b c ⟶ X :=
    Cofan.IsColimit.desc hP fun i => (e i).inv ≫ pullback.fst a (cG.inj i)
  have hfac : ∀ i, pullback.fst t (cG.inj i) ≫ inv = (e i).inv ≫ pullback.fst a (cG.inj i) :=
    Cofan.IsColimit.fac hP _
  have h1 : m ≫ inv = 𝟙 X := Cofan.IsColimit.hom_ext hX _ _ fun i => by
    simp [reassoc_of% hcompat i, hfac]
  have h2 : inv ≫ m = 𝟙 (pullback b c) := Cofan.IsColimit.hom_ext hP _ _ fun i => by
    simp [reassoc_of% hfac i, hcompat]
  exact IsPullback.of_iso_pullback ⟨w⟩ ⟨m, inv, h1, h2⟩ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end CategoryTheory
