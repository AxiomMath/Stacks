module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Amalgamating a family locally

Let `P` be a presheaf of sets on a category `C`, let `R` be a sieve on `X` and let `x` be a
compatible family of elements of `P` on `R`. The arrows `h : Y ⟶ X` over which `x` has an
amalgamation, meaning a section of `P` over `Y` restricting to `x` along every arrow of the
pulled back sieve, form a sieve on `X`.

If `P` is a sheaf for a topology `J`, and if `P` is separated for the pullbacks of `R`, then `x`
has an amalgamation as soon as this sieve is `J`-covering: the local amalgamations are unique,
hence compatible, and they glue to an amalgamation of `x`. This is the usual way of proving
that a sheaf for a coarse topology satisfies the sheaf condition for a finer one: separation is
proved first, and then gluing is checked locally for the coarse topology.

## Main definitions

* `CategoryTheory.Presieve.FamilyOfElements.amalgamationSieve`: the sieve of arrows over which a
  family of elements has an amalgamation.

## Main results

* `CategoryTheory.Presieve.FamilyOfElements.congr_arrow`: the value of a family at an arrow only
  depends on the arrow, not on the proof that it belongs to the sieve.
* `CategoryTheory.Presieve.FamilyOfElements.amalgamationSieve_pullback`: the sieve attached to
  a pulled back family contains the pullback of the sieve attached to the family.
* `CategoryTheory.Presieve.FamilyOfElements.exists_isAmalgamation_of_amalgamationSieve_mem`:
  a compatible family whose amalgamation sieve is covering has an amalgamation.
* `CategoryTheory.GrothendieckTopology.mem_of_pullback_mem_of_generate`: a sieve is covering as
  soon as its pullbacks along the members of a family generating a covering sieve are.

## References

* [Stacks Project, Tag 00Z9](https://stacks.math.columbia.edu/tag/00Z9)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Presieve.FamilyOfElements

variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type w} {X : C} {R : Sieve X}

/-- The value of a family of elements at an arrow only depends on the arrow. -/
lemma congr_arrow (x : FamilyOfElements P R.arrows) {Y : C} {f f' : Y ⟶ X} (e : f = f')
    (hf : R f) (hf' : R f') : x f hf = x f' hf' := by
  subst e
  rfl

/-- The sieve of arrows `h : Y ⟶ X` over which the family `x` has an amalgamation: a section of
`P` over `Y` restricting to `x (g ≫ h)` along every `g` with `g ≫ h` in `R`. -/
def amalgamationSieve (x : FamilyOfElements P R.arrows) : Sieve X where
  arrows Y h := ∃ y : P.obj (op Y), ∀ ⦃Z : C⦄ (g : Z ⟶ Y) (hg : R (g ≫ h)),
    P.map g.op y = x (g ≫ h) hg
  downward_closed := by
    rintro Y W h ⟨y, hy⟩ k
    refine ⟨P.map k.op y, fun Z g hg ↦ ?_⟩
    rw [← FunctorToTypes.map_comp_apply, ← op_comp,
      hy (g ≫ k) (by simpa only [Category.assoc] using hg)]
    exact congr_arrow x (Category.assoc _ _ _) _ _

/-- The sieve attached to a pulled back family contains the pullback of the sieve attached to the
family. -/
lemma amalgamationSieve_pullback (x : FamilyOfElements P R.arrows) {Y : C} (f : Y ⟶ X) :
    (x.pullback f).amalgamationSieve ≤ x.amalgamationSieve.pullback f := by
  rintro W h ⟨y, hy⟩
  refine ⟨y, fun Z g hg ↦ ?_⟩
  rw [hy g (by simpa only [Sieve.pullback_apply, Category.assoc] using hg)]
  exact congr_arrow x (Category.assoc _ _ _) _ _

/-- **Local amalgamation.** Let `P` be a sheaf for `J` which is separated for the pullbacks of a
sieve `R`. A compatible family on `R` whose amalgamation sieve is `J`-covering has an
amalgamation. -/
theorem exists_isAmalgamation_of_amalgamationSieve_mem (J : GrothendieckTopology C)
    (hP : Presieve.IsSheaf J P)
    (hsep : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor P (R.pullback f).arrows)
    (x : FamilyOfElements P R.arrows) (hx : x.Compatible) (hA : x.amalgamationSieve ∈ J X) :
    ∃ t, x.IsAmalgamation t := by
  let A := x.amalgamationSieve
  have huniq : ∀ ⦃Y : C⦄ (h : Y ⟶ X) (y y' : P.obj (op Y)),
      (∀ ⦃Z : C⦄ (g : Z ⟶ Y) (hg : R (g ≫ h)), P.map g.op y = x (g ≫ h) hg) →
      (∀ ⦃Z : C⦄ (g : Z ⟶ Y) (hg : R (g ≫ h)), P.map g.op y' = x (g ≫ h) hg) → y = y' :=
    fun Y h y y' hy hy' ↦ hsep h (x.pullback h) y y' hy hy'
  choose y hy using fun (Y : C) (h : Y ⟶ X) (hh : A.arrows h) ↦ hh
  let yF : FamilyOfElements P A.arrows := fun Y h hh ↦ y Y h hh
  have hycomp : yF.Compatible := by
    rw [compatible_iff_sieveCompatible]
    intro Y W h k hh
    refine (huniq (k ≫ h) _ _ (fun Z g hg ↦ ?_) (hy _ _ _)).symm
    rw [← FunctorToTypes.map_comp_apply, ← op_comp,
      hy _ h hh (g ≫ k) (by simpa only [Category.assoc] using hg)]
    exact congr_arrow x (Category.assoc _ _ _) _ _
  obtain ⟨s, hs, -⟩ := hP A hA yF hycomp
  refine ⟨s, fun Y g hg ↦ ?_⟩
  refine (hP.isSeparated _ (J.pullback_stable g hA)).ext fun W k hk ↦ ?_
  have e1 : P.map k.op (P.map g.op s) = y W (k ≫ g) hk := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    exact hs (k ≫ g) hk
  have e3 : y W (k ≫ g) hk = x (k ≫ g) (R.downward_closed hg k) := by
    have := hy W (k ≫ g) hk (𝟙 W) (by simpa using R.downward_closed hg k)
    rw [op_id, FunctorToTypes.map_id_apply] at this
    rw [this]
    exact congr_arrow x (Category.id_comp _) _ _
  rw [e1, e3, hx.to_sieveCompatible g k hg]

/-- A sieve is covering as soon as its pullback along every member of a family generating a
covering sieve is covering. -/
theorem _root_.CategoryTheory.GrothendieckTopology.mem_of_pullback_mem_of_generate
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {X : C} {R : Presieve X}
    (hR : Sieve.generate R ∈ J X) (D : Sieve X)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → D.pullback f ∈ J Y) : D ∈ J X := by
  refine J.transitive hR _ ?_
  rintro Y f ⟨Z, e, g, hg, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable e (h g hg)

end CategoryTheory.Presieve.FamilyOfElements

end
