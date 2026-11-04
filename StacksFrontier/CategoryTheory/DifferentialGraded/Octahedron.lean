module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeMorphism
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituationIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.GradedSplitTransport
public import StacksFrontier.CategoryTheory.DifferentialGraded.ShiftRoundTripCoherence

/-!
# The octahedron axiom for admissible monomorphisms

Two composable admissible monomorphisms in a differential graded category satisfying the
direct-sum, shift and cone axioms can be completed to four admissible short exact sequences whose
associated triangles in the homotopy category form an octahedral diagram. This is axiom TR4 for
the homotopy category.

## Main results

* `DGCategory.admissibleMonomorphisms_octahedronIso`: the third and fourth admissible sequences,
  together with the commutativity and connecting-map identities of TR4, over
  `DGCategory.ConeSituationIso` — axioms (A), (B) and (C) with the shift additive on objects only
  up to isomorphism — granted the round-trip coherence
  `DGCategory.ShiftAxiomBIso.RoundTripCoherent`.
* `DGCategory.admissibleMonomorphisms_octahedron`: the same over the strict
  `DGCategory.ConeSituation`, where the coherence is automatic
  (`DGCategory.ShiftAxiomB.roundTripCoherent`).

## Implementation notes

The sequence for the composite has the direct sum of the first two quotients as its middle term
(axiom (A)); its projection is assembled from the two given projections. The fourth sequence is
the one on the three quotients; it is produced on `q₃[-1][1]` and moved to `q₃` along the
round-trip isomorphism by `DGCategory.GradedSplitShortExact.transportQuotient`.

Degree-zero composition is `DGCategory.comp0`, abbreviated by the local notation `≫₀`.

## References

* [Stacks Project, Tag 09QX](https://stacks.math.columbia.edu/tag/09QX)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

local infixr:80 " ≫₀ " => comp0

private lemma functor_map_eq_transport {C : Type u} [Category C]
    {F G : C ⥤ C} (h : F = G) {x y : C} (f : x ⟶ y) :
    F.map f = eqToHom (congrArg (fun H : C ⥤ C => H.obj x) h) ≫
      G.map f ≫ eqToHom (congrArg (fun H : C ⥤ C => H.obj y) h).symm := by
  cases h
  simp

private lemma category_assoc_generic {C : Type u} [Category C]
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h

private lemma cancel_shift_iso {C : Type u} [Category C]
    {X B C' D E : C} (f : X ⟶ C') (h : B = C')
    (g : C' ⟶ D) (k : D ⟶ E) :
    (f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g ≫ k) =
      (f ≫ g) ≫ k := by
  calc
    (f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g ≫ k) =
        f ≫ ((eqToHom h.symm ≫ eqToHom h) ≫ (g ≫ k)) := by
      simp only [Category.assoc]
    _ = f ≫ (𝟙 C' ≫ (g ≫ k)) := by
          have hcancel : eqToHom h.symm ≫ eqToHom h = 𝟙 C' := by
            cases h
            simp
          rw [hcancel]
    _ = (f ≫ g) ≫ k := by
          rw [Category.id_comp, Category.assoc]

private alias dg_comp_neg_left := DGCategory.comp_neg_left

private alias dg_comp_neg_right := DGCategory.comp_neg_right

/-- The differential commutes with negation. -/
private theorem d_neg_eq {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : A.d (-f) = -A.d f := by
  rw [← neg_one_smul R f, A.d_smul, neg_one_smul]

private theorem connectingHom_natural_raw
    {x y z x' y' z' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (E' : GradedSplitShortExact (A := A) x' y' z')
    (u : A.Cocycle x x') (v : A.Cocycle y y') (w : A.Cocycle z z')
    (hu : A.comp (by omega : (0 : ℤ) + 0 = 0) v.1 E.a.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) E'.a.1 u.1)
    (hw : A.comp (by omega : (0 : ℤ) + 0 = 0) E'.b.1 v.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) w.1 E.b.1) :
    A.comp (by omega : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E') w.1 -
      A.comp (by omega : (0 : ℤ) + 1 = 1) u.1
        (GradedSplitShortExact.connectingHom E) =
      A.d (-(A.comp (by omega : (0 : ℤ) + 0 = 0)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E'.π v.1) E.s)) := by
  have hπa' : E'.a.1 ≫₀ E'.π = A.id x' := E'.π_a
  have hbs : E.s ≫₀ E.b.1 = A.id z := E.b_s
  have hsplit : E.π ≫₀ E.a.1 + E.b.1 ≫₀ E.s = A.id y := E.a_π_add_s_b
  have hproj : v.1 ≫₀ E'.π = E.π ≫₀ u.1 +
      E.b.1 ≫₀ (E.s ≫₀ (v.1 ≫₀ E'.π)) := by
    have h := congrArg (fun t : A.Hom y y 0 => t ≫₀ (v.1 ≫₀ E'.π)) hsplit
    rw [add_comp0, id_comp0] at h
    have hu' : E.a.1 ≫₀ v.1 = u.1 ≫₀ E'.a.1 := by
      simpa [comp0] using hu
    have hfirst : (E.π ≫₀ E.a.1) ≫₀ (v.1 ≫₀ E'.π) =
        E.π ≫₀ u.1 := by
      calc
        (E.π ≫₀ E.a.1) ≫₀ (v.1 ≫₀ E'.π) =
            E.π ≫₀ (E.a.1 ≫₀ (v.1 ≫₀ E'.π)) := comp0_assoc _ _ _
        _ = E.π ≫₀ ((E.a.1 ≫₀ v.1) ≫₀ E'.π) := by
          rw [(comp0_assoc E.a.1 v.1 E'.π).symm]
        _ = E.π ≫₀ ((u.1 ≫₀ E'.a.1) ≫₀ E'.π) := by rw [hu']
        _ = E.π ≫₀ u.1 := by rw [comp0_assoc, hπa', comp0_id]
    have hsecond : (E.b.1 ≫₀ E.s) ≫₀ (v.1 ≫₀ E'.π) =
        E.b.1 ≫₀ (E.s ≫₀ (v.1 ≫₀ E'.π)) := comp0_assoc _ _ _
    simpa only [hfirst, hsecond] using h.symm
  have hws : w.1 = (E.s ≫₀ v.1) ≫₀ E'.b.1 := by
    have hw' : v.1 ≫₀ E'.b.1 = E.b.1 ≫₀ w.1 := by
      simpa [comp0] using hw
    calc
      w.1 = A.id z ≫₀ w.1 := (id_comp0 w.1).symm
      _ = (E.s ≫₀ E.b.1) ≫₀ w.1 := by rw [hbs]
      _ = E.s ≫₀ (E.b.1 ≫₀ w.1) := comp0_assoc E.s E.b.1 w.1
      _ = E.s ≫₀ (v.1 ≫₀ E'.b.1) := by
        rw [← hw']
      _ = (E.s ≫₀ v.1) ≫₀ E'.b.1 := (comp0_assoc E.s v.1 E'.b.1).symm
  have hbd : A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d E.s) = 0 := by
    have h := congrArg A.d hbs
    rw [A.d_id] at h
    change A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 E.s) = 0 at h
    rw [A.leibniz (by lia : (0 : ℤ) + 0 = 0) E.b.1 E.s,
      E.b.2, A.comp_zero_left] at h
    simpa [Int.natAbs] using h
  have hprojD :
      A.comp (by lia : (0 : ℤ) + 1 = 1) (A.comp (by lia : (0 : ℤ) + 0 = 0)
        E'.π v.1) (A.d E.s) =
      A.comp (by lia : (0 : ℤ) + 1 = 1)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) u.1 E.π) (A.d E.s) := by
    have h := congrArg (fun f : A.Hom y x' 0 =>
      A.comp (by lia : (0 : ℤ) + 1 = 1) f (A.d E.s)) hproj
    rw [A.comp_add_left] at h
    have hkill : A.comp (by lia : (0 : ℤ) + 1 = 1)
        (E.b.1 ≫₀ (E.s ≫₀ (v.1 ≫₀ E'.π))) (A.d E.s) = 0 := by
      show A.comp (by lia : (0 : ℤ) + 1 = 1)
          (A.comp (by lia : (0 : ℤ) + 0 = 0)
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s) E.b.1)
          (A.d E.s) = 0
      calc
        A.comp (by lia : (0 : ℤ) + 1 = 1)
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0)
                (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s)
              E.b.1)
            (A.d E.s) = A.comp (by lia : (0 : ℤ) + 1 = 1)
              (A.comp (by lia : (0 : ℤ) + 0 = 0)
                (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s)
              (A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d E.s)) :=
              (A.assoc (by lia : (0 : ℤ) + 1 = 1)
                (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 0 = 0)
                (by lia : (0 : ℤ) + 1 = 1)
                (A.comp (by lia : (0 : ℤ) + 0 = 0)
                  (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s)
                E.b.1 (A.d E.s)).symm
        _ = 0 := by rw [hbd, A.comp_zero_right]
    rw [hkill, add_zero] at h
    simpa only [comp0] using h
  have hdeltaW :
      A.comp (by lia : (1 : ℤ) + 0 = 1)
          (GradedSplitShortExact.connectingHom E') w.1 =
        A.comp (by lia : (1 : ℤ) + 0 = 1)
          (A.d (-E'.π)) (A.comp (by lia : (0 : ℤ) + 0 = 0) v.1 E.s) := by
    rw [hws]
    show A.comp (by lia : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E')
        (A.comp (by lia : (0 : ℤ) + 0 = 0)
          E'.b.1 (A.comp (by lia : (0 : ℤ) + 0 = 0) v.1 E.s)) = _
    rw [A.assoc (by lia : (0 : ℤ) + 0 = 0)
      (by lia : (1 : ℤ) + 0 = 1) (by lia : (1 : ℤ) + 0 = 1)
      (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E') E'.b.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) v.1 E.s),
      ← GradedSplitShortExact.connectingHom_comp E']
  have hder : A.d (A.comp (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s) =
      A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d E'.π)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) v.1 E.s) +
        A.comp (by lia : (0 : ℤ) + 1 = 1)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) (A.d E.s) := by
    rw [A.leibniz (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s,
      A.leibniz (by lia : (0 : ℤ) + 0 = 0) E'.π v.1,
      v.2, A.comp_zero_right]
    simp only [Int.natAbs, pow_zero, one_smul, add_zero]
    rw [(A.assoc (by lia : (0 : ℤ) + 0 = 0)
      (by lia : (1 : ℤ) + 0 = 1) (by lia : (1 : ℤ) + 0 = 1)
      (by lia : (1 : ℤ) + 0 = 1) (A.d E'.π) v.1 E.s).symm]
  have hconnAssoc :
      A.comp (by lia : (0 : ℤ) + 1 = 1) u.1
          (GradedSplitShortExact.connectingHom E) =
        A.comp (by lia : (0 : ℤ) + 1 = 1)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) u.1 E.π) (A.d E.s) := by
    show A.comp (by lia : (0 : ℤ) + 1 = 1) u.1
        (A.comp (by lia : (0 : ℤ) + (0 + 1) = 1) E.π (A.d E.s)) = _
    exact A.assoc (by lia : (0 : ℤ) + 1 = 1)
      (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 0 = 0)
      (by lia : (0 : ℤ) + 1 = 1) u.1 E.π (A.d E.s)
  rw [hdeltaW, d_neg_eq, d_neg_eq, hder, dg_comp_neg_left, hprojD, hconnAssoc]
  abel_nf

private theorem connectingHom_natural_classes
    (S : ShiftAxiomBIso A)
    {x y z x' y' z' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (E' : GradedSplitShortExact (A := A) x' y' z')
    (u : A.Cocycle x x') (v : A.Cocycle y y') (w : A.Cocycle z z')
    (hu : A.comp (by omega : (0 : ℤ) + 0 = 0) v.1 E.a.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) E'.a.1 u.1)
    (hw : A.comp (by omega : (0 : ℤ) + 0 = 0) E'.b.1 v.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) w.1 E.b.1) :
    Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x'))
        (A.compCocycle (S.connectingCocycle E') w) =
      Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x'))
        (A.compCocycle ((S.shiftFunctor 1).mapCocycle u)
          (S.connectingCocycle E)) := by
  let t : A.Hom z x' 0 :=
    A.comp (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E'.π v.1) E.s
  let t' : A.Hom z x' (-1 + 1) := by simpa using t
  let h : A.Hom z ((S.shiftFunctor 1).obj x') (-1) :=
    S.toShift 1 z x' (-1) t'
  have hraw := connectingHom_natural_raw E E' u v w hu hw
  have hmap := congrArg (S.toShift 1 z x' 0) hraw
  rw [map_sub] at hmap
  have hshiftL :
      S.toShift 1 z x' 0
          (A.comp (by lia : (1 : ℤ) + 0 = 1)
            (GradedSplitShortExact.connectingHom E') w.1) =
        A.comp (by lia : (0 : ℤ) + 0 = 0)
          (S.connectingCocycle E').1 w.1 := by
    exact S.toShift_comp_right (n := 1) (m := 0) (l := 0)
      (GradedSplitShortExact.connectingHom E') w.1
  have hshiftR :
      S.toShift 1 z x' 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1) u.1
            (GradedSplitShortExact.connectingHom E)) =
        A.comp (by lia : (0 : ℤ) + 0 = 0)
          ((S.shiftFunctor 1).map u.1)
          (S.connectingCocycle E).1 := by
    show S.toShift 1 z x' 0
        (A.comp (by lia : (0 : ℤ) + 1 = 1) u.1
          (GradedSplitShortExact.connectingHom E)) =
      A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map u.1)
        (S.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E))
    simpa [Int.natAbs] using
      (S.toShift_comp_left (n := 1) (m := 0) (l := 0)
        u.1 (GradedSplitShortExact.connectingHom E))
  have hshiftD :
      S.toShift 1 z x' 0 (A.d (-t)) = A.d h := by
    have ht := S.toShift_d 1 z x' (-1) (-t')
    have hmapNeg : S.toShift 1 z x' (-1) (-t') = -h := by
      simp [h, t']
    calc
      S.toShift 1 z x' 0 (A.d (-t)) =
          -A.d (S.toShift 1 z x' (-1) (-t')) := by
            simpa [t', Int.natAbs, DGCategory.d'] using ht
      _ = -A.d (-h) := by rw [hmapNeg]
      _ = A.d h := by rw [d_neg_eq, neg_neg]
  rw [hshiftD] at hmap
  have hhomotopic : A.Homotopic
      (A.compCocycle (S.connectingCocycle E') w)
      (A.compCocycle ((S.shiftFunctor 1).mapCocycle u)
        (S.connectingCocycle E)) := by
    refine ⟨h, ?_⟩
    show A.comp (by lia : (0 : ℤ) + 0 = 0)
        (S.connectingCocycle E').1 w.1 -
      A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map u.1) (S.connectingCocycle E).1 =
      A.d h
    rw [← hshiftL, ← hshiftR]
    exact hmap
  exact Quotient.sound hhomotopic

private theorem compositeProjection_closed
    {x y z q₁ q₂ q₃ : A.Obj}
    (E₁ : GradedSplitShortExact (A := A) x y q₁)
    (E₃ : GradedSplitShortExact (A := A) y z q₃)
    (E₄ : GradedSplitShortExact (A := A) q₁ q₂ q₃)
    (hδ : GradedSplitShortExact.connectingHom E₄ =
      A.comp (by omega : (0 : ℤ) + 1 = 1) E₁.b.1
        (GradedSplitShortExact.connectingHom E₃)) :
    A.d (E₃.π ≫₀ (E₁.b.1 ≫₀ E₄.a.1) + E₃.b.1 ≫₀ E₄.s) = 0 := by
  have hpi : A.d E₃.π =
      -A.comp (by lia : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E₃) E₃.b.1 := by
    have heq := GradedSplitShortExact.connectingHom_comp E₃
    rw [d_neg_eq] at heq
    rw [heq, neg_neg]
  have hmid : A.d
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1) = 0 := by
    rw [A.leibniz (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1,
      E₄.a.2, E₁.b.2]
    simp
  have hfirst :
      A.d (A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1) E₃.π) =
      A.comp (by lia : (0 : ℤ) + 1 = 1)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1) (A.d E₃.π) := by
    rw [A.leibniz (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1) E₃.π,
      hmid]
    simp
  have hsecond :
      A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.s E₃.b.1) =
      A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d E₄.s) E₃.b.1 := by
    simp [A.leibniz, E₃.b.2, pow_zero, A.comp_zero_right]
  rw [A.d_add]
  show A.d (A.comp (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1) E₃.π) +
    A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.s E₃.b.1) = 0
  rw [hfirst, hsecond, hpi, ← GradedSplitShortExact.comp_connectingHom E₄, hδ]
  simp only [dg_comp_neg_right]
  have h₁ := A.assoc (by lia : (0 : ℤ) + 1 = 1)
    (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 0 = 0)
    (by lia : (0 : ℤ) + 1 = 1) E₄.a.1 E₁.b.1
      (GradedSplitShortExact.connectingHom E₃)
  have h₂ := A.assoc (by lia : (1 : ℤ) + 0 = 1)
    (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 1 = 1)
    (by lia : (1 : ℤ) + 0 = 1)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1)
      (GradedSplitShortExact.connectingHom E₃) E₃.b.1
  rw [h₁, ← h₂]
  abel

/-- Compose two graded-split sequences once an extension of the two quotients
has been supplied. -/
private theorem composeGradedSplitShortExact
    {x y z q₁ q₂ q₃ : A.Obj}
    (E₁ : GradedSplitShortExact (A := A) x y q₁)
    (E₃ : GradedSplitShortExact (A := A) y z q₃)
    (E₄ : GradedSplitShortExact (A := A) q₁ q₂ q₃)
    (hclosed : A.d
      (E₃.π ≫₀ (E₁.b.1 ≫₀ E₄.a.1) + E₃.b.1 ≫₀ E₄.s) = 0) :
    ∃ E₂ : GradedSplitShortExact (A := A) x z q₂,
      E₂.a.1 = A.comp (by rfl : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1 ∧
      E₁.b.1 ≫₀ E₄.a.1 = E₃.a.1 ≫₀ E₂.b.1 ∧
      E₂.b.1 ≫₀ E₄.b.1 = E₃.b.1 := by
  have hπa₁ : E₁.a.1 ≫₀ E₁.π = A.id x := E₁.π_a
  have hbs₁ : E₁.s ≫₀ E₁.b.1 = A.id q₁ := E₁.b_s
  have hπs₁ : E₁.s ≫₀ E₁.π = 0 := E₁.π_s
  have hsplit₁ : E₁.π ≫₀ E₁.a.1 + E₁.b.1 ≫₀ E₁.s = A.id y := E₁.a_π_add_s_b
  have hπa₃ : E₃.a.1 ≫₀ E₃.π = A.id y := E₃.π_a
  have hbs₃ : E₃.s ≫₀ E₃.b.1 = A.id q₃ := E₃.b_s
  have hπs₃ : E₃.s ≫₀ E₃.π = 0 := E₃.π_s
  have hsplit₃ : E₃.π ≫₀ E₃.a.1 + E₃.b.1 ≫₀ E₃.s = A.id z := E₃.a_π_add_s_b
  have hπa₄ : E₄.a.1 ≫₀ E₄.π = A.id q₁ := E₄.π_a
  have hbs₄ : E₄.s ≫₀ E₄.b.1 = A.id q₃ := E₄.b_s
  have hπs₄ : E₄.s ≫₀ E₄.π = 0 := E₄.π_s
  have hsplit₄ : E₄.π ≫₀ E₄.a.1 + E₄.b.1 ≫₀ E₄.s = A.id q₂ := E₄.a_π_add_s_b
  have hab₁ : E₁.a.1 ≫₀ E₁.b.1 = 0 := by
    simpa [comp0] using GradedSplitShortExact.comp_zero E₁
  have hab₃ : E₃.a.1 ≫₀ E₃.b.1 = 0 := by
    simpa [comp0] using GradedSplitShortExact.comp_zero E₃
  have hab₄ : E₄.a.1 ≫₀ E₄.b.1 = 0 := by
    simpa [comp0] using GradedSplitShortExact.comp_zero E₄
  have hcancel₁ : ∀ {t : A.Obj} (f : A.Hom t q₁ 0),
      (f ≫₀ E₁.s) ≫₀ E₁.b.1 = f :=
    fun f => comp0_cancel f E₁.s E₁.b.1 hbs₁
  have hzero₁ : ∀ {t : A.Obj} (f : A.Hom t q₁ 0),
      (f ≫₀ E₁.s) ≫₀ E₁.π = 0 :=
    fun f => comp0_cancel_zero f E₁.s E₁.π hπs₁
  have hcancel₃ : ∀ {t : A.Obj} (f : A.Hom t y 0),
      (f ≫₀ E₃.a.1) ≫₀ E₃.π = f :=
    fun f => comp0_cancel f E₃.a.1 E₃.π hπa₃
  have hzero₃ : ∀ {t : A.Obj} (f : A.Hom t y 0),
      (f ≫₀ E₃.a.1) ≫₀ E₃.b.1 = 0 :=
    fun f => comp0_cancel_zero f E₃.a.1 E₃.b.1 hab₃
  have hzero₃' : ∀ {t : A.Obj} (f : A.Hom t q₃ 0),
      (f ≫₀ E₃.s) ≫₀ E₃.π = 0 :=
    fun f => comp0_cancel_zero f E₃.s E₃.π hπs₃
  have hcancel₃' : ∀ {t : A.Obj} (f : A.Hom t q₃ 0),
      (f ≫₀ E₃.s) ≫₀ E₃.b.1 = f :=
    fun f => comp0_cancel f E₃.s E₃.b.1 hbs₃
  have hzero₄ : ∀ {t : A.Obj} (f : A.Hom t q₁ 0),
      (f ≫₀ E₄.a.1) ≫₀ E₄.b.1 = 0 :=
    fun f => comp0_cancel_zero f E₄.a.1 E₄.b.1 hab₄
  have hcancel₄ : ∀ {t : A.Obj} (f : A.Hom t q₃ 0),
      (f ≫₀ E₄.s) ≫₀ E₄.b.1 = f :=
    fun f => comp0_cancel f E₄.s E₄.b.1 hbs₄
  have hcancelA₄ : ∀ {t : A.Obj} (f : A.Hom t q₁ 0),
      (f ≫₀ E₄.a.1) ≫₀ E₄.π = f :=
    fun f => comp0_cancel f E₄.a.1 E₄.π hπa₄
  have hzeroPi₄ : ∀ {t : A.Obj} (f : A.Hom t q₃ 0),
      (f ≫₀ E₄.s) ≫₀ E₄.π = 0 :=
    fun f => comp0_cancel_zero f E₄.s E₄.π hπs₄
  let a₂ := A.compCocycle E₃.a E₁.a
  let b₂ : A.Hom z q₂ 0 :=
    E₃.π ≫₀ (E₁.b.1 ≫₀ E₄.a.1) + E₃.b.1 ≫₀ E₄.s
  let π₂ : A.Hom z x 0 := E₃.π ≫₀ E₁.π
  let s₂ : A.Hom q₂ z 0 :=
    E₄.π ≫₀ (E₁.s ≫₀ E₃.a.1) + E₄.b.1 ≫₀ E₃.s
  have hb₂s₂ : b₂ ≫₀ s₂ =
      (E₃.π ≫₀ E₁.b.1 ≫₀ E₁.s) ≫₀ E₃.a.1 + E₃.b.1 ≫₀ E₃.s := by
    simp [b₂, s₂, ← comp0_assoc, comp0_add, add_comp0,
      hcancelA₄, hzeroPi₄, hzero₄, hcancel₄]
  let E₂ : GradedSplitShortExact (A := A) x z q₂ := {
    a := a₂
    b := ⟨b₂, hclosed⟩
    π := π₂
    s := s₂
    π_a := by
      show (E₁.a.1 ≫₀ E₃.a.1) ≫₀ (E₃.π ≫₀ E₁.π) = A.id x
      calc
        (E₁.a.1 ≫₀ E₃.a.1) ≫₀ (E₃.π ≫₀ E₁.π) =
            E₁.a.1 ≫₀ (E₃.a.1 ≫₀ (E₃.π ≫₀ E₁.π)) := by
              rw [comp0_assoc]
        _ = E₁.a.1 ≫₀ ((E₃.a.1 ≫₀ E₃.π) ≫₀ E₁.π) := by
              congr 1
              exact (comp0_assoc E₃.a.1 E₃.π E₁.π).symm
        _ = A.id x := by rw [hπa₃, id_comp0, hπa₁]
    b_s := by
      show s₂ ≫₀ b₂ = A.id q₂
      simp [b₂, s₂, ← comp0_assoc, comp0_add, add_comp0,
        hcancel₁, hcancel₃, hzero₃, hzero₃', hcancel₃', hsplit₄]
    π_s := by
      show s₂ ≫₀ π₂ = 0
      simp [π₂, s₂, ← comp0_assoc, add_comp0,
        hcancel₃, hzero₁, hzero₃']
    a_π_add_s_b := by
      show (π₂ ≫₀ a₂.1) + (b₂ ≫₀ s₂) = A.id z
      rw [hb₂s₂]
      have hfirst : π₂ ≫₀ a₂.1 =
          E₃.π ≫₀ (E₁.π ≫₀ E₁.a.1) ≫₀ E₃.a.1 := by
        show (E₃.π ≫₀ E₁.π) ≫₀ (E₁.a.1 ≫₀ E₃.a.1) = _
        simp only [comp0_assoc]
      rw [hfirst]
      have hfac :
          E₃.π ≫₀ ((E₁.π ≫₀ E₁.a.1) + (E₁.b.1 ≫₀ E₁.s)) ≫₀ E₃.a.1 =
            E₃.π ≫₀ E₃.a.1 := by
        have h := congrArg (fun f : A.Hom y y 0 =>
          (E₃.π ≫₀ f) ≫₀ E₃.a.1) hsplit₁
        simpa [comp0_assoc, comp0_add, add_comp0,
          comp0_id] using h
      have hdistrib :
          (E₃.π ≫₀ (E₁.π ≫₀ E₁.a.1) ≫₀ E₃.a.1) +
            ((E₃.π ≫₀ E₁.b.1 ≫₀ E₁.s) ≫₀ E₃.a.1) =
          E₃.π ≫₀ ((E₁.π ≫₀ E₁.a.1) + (E₁.b.1 ≫₀ E₁.s)) ≫₀ E₃.a.1 := by
        simp [comp0_assoc, comp0_add, add_comp0]
      calc
        E₃.π ≫₀ (E₁.π ≫₀ E₁.a.1) ≫₀ E₃.a.1 +
            ((E₃.π ≫₀ E₁.b.1 ≫₀ E₁.s) ≫₀ E₃.a.1 + E₃.b.1 ≫₀ E₃.s) =
            (E₃.π ≫₀ (E₁.π ≫₀ E₁.a.1) ≫₀ E₃.a.1 +
              (E₃.π ≫₀ E₁.b.1 ≫₀ E₁.s) ≫₀ E₃.a.1) + E₃.b.1 ≫₀ E₃.s := by
                rw [add_assoc]
        _ = (E₃.π ≫₀
              ((E₁.π ≫₀ E₁.a.1) + (E₁.b.1 ≫₀ E₁.s)) ≫₀ E₃.a.1) +
              E₃.b.1 ≫₀ E₃.s := by rw [hdistrib]
        _ = E₃.π ≫₀ E₃.a.1 + E₃.b.1 ≫₀ E₃.s := by rw [hfac]
        _ = A.id z := hsplit₃
  }
  refine ⟨E₂, ?_, ?_, ?_⟩
  · rfl
  · dsimp only [E₂, b₂]
    rw [comp0_add]
    symm
    calc
      E₃.a.1 ≫₀ (E₃.π ≫₀ (E₁.b.1 ≫₀ E₄.a.1)) +
          E₃.a.1 ≫₀ (E₃.b.1 ≫₀ E₄.s) =
        (E₃.a.1 ≫₀ E₃.π) ≫₀ (E₁.b.1 ≫₀ E₄.a.1) +
          (E₃.a.1 ≫₀ E₃.b.1) ≫₀ E₄.s := by
            rw [← comp0_assoc E₃.a.1 E₃.π (E₁.b.1 ≫₀ E₄.a.1),
              comp0_assoc E₃.a.1 E₃.b.1 E₄.s]
      _ = E₁.b.1 ≫₀ E₄.a.1 := by
        rw [hπa₃, hab₃, id_comp0]
        show E₁.b.1 ≫₀ E₄.a.1 + A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.s 0 = _
        rw [A.comp_zero_right, add_zero]
  · simp [E₂, b₂, ← comp0_assoc, add_comp0,
      hzero₄, hcancel₄]

/-- **The octahedral diagram associated to two composable admissible monomorphisms, over an
axiom (B) additive on objects only up to isomorphism.** The input exact sequences witness
admissibility and fix the two quotient objects. -/
theorem admissibleMonomorphisms_octahedronIso
    (S : ConeSituationIso A) (hS : S.shift.RoundTripCoherent)
    {x y z q₁ q₃ : A.Obj}
    (E₁ : GradedSplitShortExact (A := A) x y q₁)
    (E₃ : GradedSplitShortExact (A := A) y z q₃) :
    letI : HasShift A.K ℤ := S.shift.kShift
    let T₁ := S.shift.associatedKTriangle E₁
    let T₃ := S.shift.associatedKTriangle E₃
    ∃ (q₂ : A.Obj)
      (E₂ : GradedSplitShortExact (A := A) x z q₂)
      (E₄ : GradedSplitShortExact (A := A) q₁ q₂ q₃),
      let T₂ := S.shift.associatedKTriangle E₂
      let T₄ := S.shift.associatedKTriangle E₄
      (E₂.a.1 = A.comp (by rfl : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1) ∧
      (T₁.mor₁ ≫ T₃.mor₁ = T₂.mor₁) ∧
      (T₁.mor₂ ≫ T₄.mor₁ = T₃.mor₁ ≫ T₂.mor₂) ∧
      (T₄.mor₁ ≫ T₂.mor₃ = T₁.mor₃) ∧
      (T₂.mor₂ ≫ T₄.mor₂ = T₃.mor₂) ∧
      (T₂.mor₃ ≫ T₁.mor₁⟦1⟧' = T₄.mor₂ ≫ T₃.mor₃) ∧
      (T₄.mor₃ = T₃.mor₃ ≫ T₁.mor₂⟦1⟧') := by
  classical
  let α := A.compCocycle E₃.a E₁.a
  have hα : A.d α.1 = 0 := α.2
  let c := S.cone α
  let Ec := S.coneSequence α
  let F := S.shift.shiftFunctor 1
  let Fm := S.shift.shiftFunctor (-1)
  let f : A.Cocycle ((S.shift.shiftFunctor (-1)).obj q₃) q₁ :=
    A.compCocycle E₁.b (S.shift.shiftedConnecting E₃)
  let e := S.shift.reshiftIso q₃
  let q₂ := S.cone f
  let Ec₄ := S.coneSequence f
  let E₄ : GradedSplitShortExact (A := A) q₁ q₂ q₃ := Ec₄.transportQuotient e
  have hinv0 : e.inv.1 ≫₀ e.hom.1 = A.id q₃ := inv_hom_comp0 e
  have hround : F.map (S.shift.shiftedConnecting E₃).1 =
      e.hom.1 ≫₀ (S.shift.connectingCocycle E₃).1 :=
    congrArg Subtype.val (S.shift.shift_shiftedConnecting hS E₃)
  have hcone : S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj
        ((S.shift.shiftFunctor (-1)).obj q₃)) q₁ 0
      (GradedSplitShortExact.connectingHom Ec₄) = F.map f.1 :=
    congrArg Subtype.val (S.cone_connecting f)
  have hmapcomp : F.map f.1 =
      F.map (S.shift.shiftedConnecting E₃).1 ≫₀ F.map E₁.b.1 := by
    show F.map (A.comp (by lia : (0 : ℤ) + 0 = 0) E₁.b.1
        (S.shift.shiftedConnecting E₃).1) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map E₁.b.1)
        (F.map (S.shift.shiftedConnecting E₃).1)
    rw [F.map_comp]
  have hcollapse : A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map f.1) e.inv.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map E₁.b.1)
        (S.shift.connectingCocycle E₃).1 := by
    show e.inv.1 ≫₀ F.map f.1 = (S.shift.connectingCocycle E₃).1 ≫₀ F.map E₁.b.1
    rw [hmapcomp, hround, ← comp0_assoc, ← comp0_assoc, hinv0, id_comp0]
  have htrans : GradedSplitShortExact.connectingHom E₄ =
      A.comp (by lia : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom Ec₄) e.inv.1 :=
    GradedSplitShortExact.connectingHom_transportQuotient Ec₄ e
  have hcomp : S.shift.toShift 1 q₃ q₁ 0
        (A.comp (by lia : (1 : ℤ) + 0 = 1)
          (GradedSplitShortExact.connectingHom Ec₄) e.inv.1) =
      A.comp (by lia : (0 : ℤ) + 0 = 0)
        (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj
          ((S.shift.shiftFunctor (-1)).obj q₃)) q₁ 0
          (GradedSplitShortExact.connectingHom Ec₄)) e.inv.1 := by
    simpa using S.shift.toShift_comp_right (n := 1) (x := q₃)
      (y := (S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj q₃))
      (z := q₁) (l := 0) (m := 0) (GradedSplitShortExact.connectingHom Ec₄) e.inv.1
  have hδ : GradedSplitShortExact.connectingHom E₄ =
      A.comp (by lia : (0 : ℤ) + 1 = 1) E₁.b.1
        (GradedSplitShortExact.connectingHom E₃) := by
    apply (S.shift.toShift 1 q₃ q₁ 0).injective
    calc
      S.shift.toShift 1 q₃ q₁ 0 (GradedSplitShortExact.connectingHom E₄) =
          A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map f.1) e.inv.1 := by
            rw [htrans, hcomp, hcone]
      _ = A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map E₁.b.1)
            (S.shift.connectingCocycle E₃).1 := hcollapse
      _ = S.shift.toShift 1 q₃ q₁ 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1) E₁.b.1
            (GradedSplitShortExact.connectingHom E₃)) := by
              show A.comp (by lia : (0 : ℤ) + 0 = 0) (F.map E₁.b.1)
                  (S.shift.toShift 1 q₃ y 0 (GradedSplitShortExact.connectingHom E₃)) = _
              simpa [pow_zero, one_smul, Int.natAbs] using
                (S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
                  E₁.b.1 (GradedSplitShortExact.connectingHom E₃)).symm
  have hclosed := compositeProjection_closed E₁ E₃ E₄ hδ
  obtain ⟨E₂, h₂a, h₂b₁, h₂b₂⟩ :=
    composeGradedSplitShortExact E₁ E₃ E₄ hclosed
  let _ : HasShift A.K ℤ := S.shift.kShift
  have hShiftF : CategoryTheory.shiftFunctor A.K (1 : ℤ) =
      (S.shift.shiftFunctor 1).onK := S.shift.kShift_functor 1
  have hKx : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
      (S.shift.shiftFunctor 1).obj x :=
    congrArg (fun G : A.K ⥤ A.K => G.obj x) hShiftF
  have hKy : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj y =
      (S.shift.shiftFunctor 1).obj y :=
    congrArg (fun G : A.K ⥤ A.K => G.obj y) hShiftF
  have hKq₁ : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj q₁ =
      (S.shift.shiftFunctor 1).obj q₁ :=
    congrArg (fun G : A.K ⥤ A.K => G.obj q₁) hShiftF
  let idX : A.Cocycle x x := ⟨A.id x, A.d_id x⟩
  let idZ : A.Cocycle z z := ⟨A.id z, A.d_id z⟩
  let idQ₃ : A.Cocycle q₃ q₃ := ⟨A.id q₃, A.d_id q₃⟩
  have hu₁ : A.comp (by lia : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E₂.a.1 idX.1 := by
    show A.comp (by lia : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E₂.a.1 (A.id x)
    rw [A.comp_id]
    exact h₂a.symm
  have hn₁ := connectingHom_natural_classes S.shift E₁ E₂ idX E₃.a E₄.a hu₁
    (by simpa [comp0] using h₂b₁.symm)
  have hid₁ :
      Quotient.mk (A.homotopySetoid q₁ ((S.shift.shiftFunctor 1).obj x))
          (A.compCocycle ((S.shift.shiftFunctor 1).mapCocycle idX)
            (S.shift.connectingCocycle E₁)) =
      Quotient.mk (A.homotopySetoid q₁ ((S.shift.shiftFunctor 1).obj x))
          (S.shift.connectingCocycle E₁) := by
    apply congrArg (Quotient.mk (A.homotopySetoid q₁
      ((S.shift.shiftFunctor 1).obj x)))
    apply Subtype.ext
    show A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.shift.shiftFunctor 1).map (A.id x))
        (S.shift.connectingCocycle E₁).1 =
      (S.shift.connectingCocycle E₁).1
    rw [(S.shift.shiftFunctor 1).map_id, A.id_comp]
  have hn₁' := hn₁.trans hid₁
  have hu₂ : A.comp (by lia : (0 : ℤ) + 0 = 0) idZ.1 E₂.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1 := by
    show A.comp (by lia : (0 : ℤ) + 0 = 0) (A.id z) E₂.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1
    rw [A.id_comp, h₂a]
  have hn₂ := connectingHom_natural_classes S.shift E₂ E₃ E₁.a idZ E₄.b
    hu₂ (by
      show A.comp (by lia : (0 : ℤ) + 0 = 0) E₃.b.1 (A.id z) =
        A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.b.1 E₂.b.1
      rw [A.comp_id]
      exact h₂b₂.symm)
  have hu₃ : A.comp (by lia : (0 : ℤ) + 0 = 0) E₂.b.1 E₃.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.a.1 E₁.b.1 := by
    simpa [comp0] using h₂b₁.symm
  have hn₃ := connectingHom_natural_classes S.shift E₃ E₄ E₁.b E₂.b idQ₃
    hu₃ (by
      show A.comp (by lia : (0 : ℤ) + 0 = 0) E₄.b.1 E₂.b.1 =
        A.comp (by lia : (0 : ℤ) + 0 = 0) (A.id q₃) E₃.b.1
      rw [A.id_comp]
      exact h₂b₂)
  have hid₃ :
      Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj q₁))
          (A.compCocycle (S.shift.connectingCocycle E₄) idQ₃) =
      Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj q₁))
          (S.shift.connectingCocycle E₄) := by
    exact congrArg (Quotient.mk _) (Subtype.ext (A.comp_id _))
  have hn₃' := hid₃.symm.trans hn₃
  have hshiftMap : ∀ {a b : A.K} (g : a ⟶ b),
      (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map g =
        eqToHom (congrArg (fun G : A.K ⥤ A.K => G.obj a) hShiftF) ≫
          (S.shift.shiftFunctor 1).onK.map g ≫
          eqToHom (congrArg (fun G : A.K ⥤ A.K => G.obj b) hShiftF).symm :=
    fun g => functor_map_eq_transport hShiftF g
  have hn₁K :
      A.compK
          (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
            (S.shift.connectingCocycle E₂))
          (Quotient.mk (A.homotopySetoid q₁ q₂) E₄.a) =
        Quotient.mk (A.homotopySetoid q₁ ((S.shift.shiftFunctor 1).obj x))
          (S.shift.connectingCocycle E₁) :=
    hn₁'
  have hn₂K :
      A.compK ((S.shift.shiftFunctor 1).onK.map
          (Quotient.mk (A.homotopySetoid x y) E₁.a))
          (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
            (S.shift.connectingCocycle E₂)) =
        A.compK
          (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
            (S.shift.connectingCocycle E₃))
          (Quotient.mk (A.homotopySetoid q₂ q₃) E₄.b) :=
    hn₂.symm
  have hn₃K :
      A.compK ((S.shift.shiftFunctor 1).onK.map
          (Quotient.mk (A.homotopySetoid y q₁) E₁.b))
          (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
            (S.shift.connectingCocycle E₃)) =
        Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj q₁))
          (S.shift.connectingCocycle E₄) :=
    hn₃'.symm
  refine ⟨q₂, E₂, E₄, ?_⟩
  simp only [ShiftAxiomBIso.associatedKTriangle, Pretriangulated.Triangle.mk]
  refine ⟨h₂a, ?_, ?_, ?_, ?_, ?_⟩
  · show Quotient.mk (A.homotopySetoid x z)
      (A.compCocycle E₃.a E₁.a) = Quotient.mk (A.homotopySetoid x z) E₂.a
    exact congrArg (Quotient.mk (A.homotopySetoid x z)) (Subtype.ext h₂a.symm)
  · show Quotient.mk (A.homotopySetoid y q₂)
      (A.compCocycle E₄.a E₁.b) = Quotient.mk (A.homotopySetoid y q₂)
      (A.compCocycle E₂.b E₃.a)
    exact congrArg (Quotient.mk (A.homotopySetoid y q₂)) (Subtype.ext h₂b₁)
  · show Quotient.mk (A.homotopySetoid q₁ q₂) E₄.a ≫
        (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
          (S.shift.connectingCocycle E₂) ≫ eqToHom hKx.symm) =
      Quotient.mk (A.homotopySetoid q₁ ((S.shift.shiftFunctor 1).obj x))
        (S.shift.connectingCocycle E₁) ≫ eqToHom hKx.symm
    calc
      _ = (Quotient.mk (A.homotopySetoid q₁ q₂) E₄.a ≫
            Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
              (S.shift.connectingCocycle E₂)) ≫ eqToHom hKx.symm :=
          (category_assoc_generic _ _ _).symm
      _ = _ := by
        show A.compK
            (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
              (S.shift.connectingCocycle E₂))
            (Quotient.mk (A.homotopySetoid q₁ q₂) E₄.a) ≫ eqToHom hKx.symm = _
        exact congrArg (fun f => f ≫ eqToHom hKx.symm) hn₁K
  · show Quotient.mk (A.homotopySetoid z q₃)
      (A.compCocycle E₄.b E₂.b) = Quotient.mk (A.homotopySetoid z q₃) E₃.b
    exact congrArg (Quotient.mk (A.homotopySetoid z q₃)) (Subtype.ext h₂b₂)
  · constructor
    · show (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
          (S.shift.connectingCocycle E₂) ≫ eqToHom hKx.symm) ≫
        (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map
          (Quotient.mk (A.homotopySetoid x y) E₁.a) =
      Quotient.mk (A.homotopySetoid q₂ q₃) E₄.b ≫
        (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
          (S.shift.connectingCocycle E₃) ≫ eqToHom hKy.symm)
      calc
        _ = (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
              (S.shift.connectingCocycle E₂) ≫
            (S.shift.shiftFunctor 1).onK.map
              (Quotient.mk (A.homotopySetoid x y) E₁.a)) ≫ eqToHom hKy.symm := by
            erw [hshiftMap]
            exact cancel_shift_iso _ hKx _ _
        _ = (Quotient.mk (A.homotopySetoid q₂ q₃) E₄.b ≫
              Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
                (S.shift.connectingCocycle E₃)) ≫ eqToHom hKy.symm := by
            have hn₂Cat :
                (Quotient.mk (A.homotopySetoid q₂ ((S.shift.shiftFunctor 1).obj x))
                  (S.shift.connectingCocycle E₂)) ≫
                  (S.shift.shiftFunctor 1).onK.map
                    (Quotient.mk (A.homotopySetoid x y) E₁.a) =
                (Quotient.mk (A.homotopySetoid q₂ q₃) E₄.b) ≫
                  Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
                    (S.shift.connectingCocycle E₃) := hn₂K
            exact congrArg (fun f => f ≫ eqToHom hKy.symm) hn₂Cat
        _ = _ := category_assoc_generic _ _ _
    · show Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj q₁))
        (S.shift.connectingCocycle E₄) ≫ eqToHom hKq₁.symm =
      (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
          (S.shift.connectingCocycle E₃) ≫ eqToHom hKy.symm) ≫
        (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map
          (Quotient.mk (A.homotopySetoid y q₁) E₁.b)
      calc
        _ = (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
              (S.shift.connectingCocycle E₃) ≫
            (S.shift.shiftFunctor 1).onK.map
              (Quotient.mk (A.homotopySetoid y q₁) E₁.b)) ≫ eqToHom hKq₁.symm := by
            have hn₃Cat :
                (Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj y))
                  (S.shift.connectingCocycle E₃)) ≫
                  (S.shift.shiftFunctor 1).onK.map
                    (Quotient.mk (A.homotopySetoid y q₁) E₁.b) =
                Quotient.mk (A.homotopySetoid q₃ ((S.shift.shiftFunctor 1).obj q₁))
                  (S.shift.connectingCocycle E₄) := hn₃K
            exact congrArg (fun f => f ≫ eqToHom hKq₁.symm) hn₃Cat.symm
        _ = _ := by
            erw [hshiftMap]
            exact (cancel_shift_iso _ hKy _ _).symm

/-- The octahedral diagram associated to two composable admissible monomorphisms.
The input exact sequences witness admissibility and fix the two quotient objects. -/
@[stacks 09QX]
theorem admissibleMonomorphisms_octahedron
    (S : ConeSituation A)
    {x y z q₁ q₃ : A.Obj}
    (E₁ : GradedSplitShortExact (A := A) x y q₁)
    (E₃ : GradedSplitShortExact (A := A) y z q₃) :
    letI : HasShift A.K ℤ := S.shift.kShift
    let T₁ := GradedSplitShortExact.associatedKTriangle S.shift E₁
    let T₃ := GradedSplitShortExact.associatedKTriangle S.shift E₃
    ∃ (q₂ : A.Obj)
      (E₂ : GradedSplitShortExact (A := A) x z q₂)
      (E₄ : GradedSplitShortExact (A := A) q₁ q₂ q₃),
      let T₂ := GradedSplitShortExact.associatedKTriangle S.shift E₂
      let T₄ := GradedSplitShortExact.associatedKTriangle S.shift E₄
      (E₂.a.1 = A.comp (by rfl : (0 : ℤ) + 0 = 0) E₃.a.1 E₁.a.1) ∧
      (T₁.mor₁ ≫ T₃.mor₁ = T₂.mor₁) ∧
      (T₁.mor₂ ≫ T₄.mor₁ = T₃.mor₁ ≫ T₂.mor₂) ∧
      (T₄.mor₁ ≫ T₂.mor₃ = T₁.mor₃) ∧
      (T₂.mor₂ ≫ T₄.mor₂ = T₃.mor₂) ∧
      (T₂.mor₃ ≫ T₁.mor₁⟦1⟧' = T₄.mor₂ ≫ T₃.mor₃) ∧
      (T₄.mor₃ = T₃.mor₃ ≫ T₁.mor₂⟦1⟧') :=
  admissibleMonomorphisms_octahedronIso S.toConeSituationIso S.shift.roundTripCoherent E₁ E₃

end DGCategory

end
