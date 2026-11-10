module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute

/-!
# Coequalizers of schemes are local for the fpqc topology

A morphism of schemes which coequalizes a pair of parallel morphisms is their coequalizer as
soon as it becomes one after base change to every member of an fpqc covering of its target
and to every pairwise overlap of that covering.

## Main definitions

* `AlgebraicGeometry.baseChangeHom` is the map of fibre products induced by a morphism over
  the base.
* `AlgebraicGeometry.baseChangeCofork` is the cofork obtained by base-changing a pair of
  parallel morphisms and their common composite.

## Main results

* `AlgebraicGeometry.isColimit_cofork_of_fpqc` says that the coequalizer property can be
  checked on an fpqc covering together with its pairwise overlaps.

## Implementation notes

Fibre products are the chosen categorical pullbacks in `Scheme`, so the local coequalizer
hypotheses are stated as colimit witnesses for the canonical base-changed coforks. The
descended morphism is produced by the sheaf condition for the representable presheaf on the
fpqc site, which is subcanonical; the local coequalizer property over each member gives a
compatible family, and the overlap hypothesis gives its compatibility.

## References

* [Stacks Project, Tag 0BMN](https://stacks.math.columbia.edu/tag/0BMN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The map between fibre products induced by a morphism over the base. -/
noncomputable def baseChangeHom {X Y Z S : Scheme.{u}} (a : X ⟶ Y) (d : X ⟶ Z) (c : Y ⟶ Z)
    (s : S ⟶ Z) (ha : a ≫ c = d) : pullback d s ⟶ pullback c s :=
  pullback.lift (pullback.fst d s ≫ a) (pullback.snd d s) (by
    rw [Category.assoc, ha]
    exact pullback.condition)

/-- The cofork obtained after base change from two maps with the same composite. -/
noncomputable def baseChangeCofork {X Y Z S : Scheme.{u}} (a b : X ⟶ Y) (c : Y ⟶ Z)
    (h : a ≫ c = b ≫ c) (s : S ⟶ Z) :
    Cofork (baseChangeHom a (a ≫ c) c s rfl)
      (baseChangeHom b (a ≫ c) c s h.symm) :=
  Cofork.ofπ (pullback.snd c s) (by
    change pullback.lift _ _ _ ≫ pullback.snd c s = pullback.lift _ _ _ ≫ pullback.snd c s
    rw [pullback.lift_snd, pullback.lift_snd])

/-- **Stacks Project, Tag 0BMN.** A coequalizer of schemes can be checked after an fpqc
covering provided it is also a coequalizer on every pairwise overlap. -/
@[stacks 0BMN]
theorem isColimit_cofork_of_fpqc {X Y Z : Scheme.{u}} (a b : X ⟶ Y) (c : Y ⟶ Z)
    (h : a ≫ c = b ≫ c) {I : Type v} (Z' : I → Scheme.{u}) (f : ∀ i, Z' i ⟶ Z)
    (hfpqc : Presieve.ofArrows Z' f ∈ Scheme.fpqcPrecoverage Z)
    (hlocal : ∀ i, Nonempty (IsColimit (baseChangeCofork a b c h (f i))))
    (hoverlap : ∀ i j, Nonempty (IsColimit
      (baseChangeCofork a b c h (pullback.fst (f i) (f j) ≫ f i)))) :
    Nonempty (IsColimit (Cofork.ofπ c h)) := by
  refine ⟨Cofork.IsColimit.mk' (Cofork.ofπ c h) ?_⟩
  · intro T
    let q : Y ⟶ T.pt := T.π
    have hq : a ≫ q = b ≫ q := Cofork.condition T
    have hsheaf : ∀ {W : Scheme.{u}} (R : Presieve W),
        Sieve.generate R ∈ Scheme.fpqcTopology W → Presieve.IsSheafFor (yoneda.obj T.pt) R :=
      fun R hR => (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor R hR
    have hs := hsheaf _ (Precoverage.generate_mem_toGrothendieck hfpqc)
    let κ : ∀ i, Cofork (baseChangeHom a (a ≫ c) c (f i) rfl)
        (baseChangeHom b (a ≫ c) c (f i) h.symm) := fun i =>
      Cofork.ofπ (pullback.fst c (f i) ≫ q) (by
        simp only [baseChangeHom]
        rw [← Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
        exact congrArg (fun x => pullback.fst (a ≫ c) (f i) ≫ x) hq)
    let φ : ∀ i, Z' i ⟶ T.pt := fun i => (Classical.choice (hlocal i)).desc (κ i)
    have hfac : ∀ i, pullback.fst c (f i) ≫ q = pullback.snd c (f i) ≫ φ i := by
      intro i
      have hf := (Classical.choice (hlocal i)).fac (κ i) WalkingParallelPair.one
      simpa [φ, κ, baseChangeCofork, Cofork.π_ofπ, Category.assoc] using hf.symm
    have hφ : ∀ i j, pullback.fst (f i) (f j) ≫ φ i =
        pullback.snd (f i) (f j) ≫ φ j := by
      intro i j
      let r := pullback.fst (f i) (f j) ≫ f i
      let ho := Classical.choice (hoverlap i j)
      have : Epi (baseChangeCofork a b c h r).π := Cofork.IsColimit.epi ho
      let li : pullback c r ⟶ pullback c (f i) := pullback.lift
        (pullback.fst c r) (pullback.snd c r ≫ pullback.fst (f i) (f j)) (by
          simp [r, Category.assoc, pullback.condition])
      let lj : pullback c r ⟶ pullback c (f j) := pullback.lift
        (pullback.fst c r) (pullback.snd c r ≫ pullback.snd (f i) (f j)) (by
          simp [r, Category.assoc, pullback.condition])
      have hi := congrArg (fun t => li ≫ t) (hfac i)
      have hj := congrArg (fun t => lj ≫ t) (hfac j)
      apply (cancel_epi (baseChangeCofork a b c h r).π).1
      have hbridge : li ≫ pullback.fst c (f i) ≫ q =
          lj ≫ pullback.fst c (f j) ≫ q := by
        simp only [li, lj, pullback.lift_fst_assoc]
      change pullback.snd c r ≫ pullback.fst (f i) (f j) ≫ φ i =
        pullback.snd c r ≫ pullback.snd (f i) (f j) ≫ φ j
      simpa only [li, lj, ← Category.assoc, pullback.lift_snd] using
        hi.symm.trans (hbridge.trans hj)
    have hφcomp : Presieve.Arrows.Compatible (yoneda.obj T.pt) f φ := by
      intro i j W gi gj hgij
      simp only [yoneda_obj_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
      rw [← pullback.lift_fst_assoc gi gj hgij (φ i), hφ i j, pullback.lift_snd_assoc]
    have hex := (Presieve.isSheafFor_arrows_iff _ _).mp hs φ hφcomp
    let z : Z ⟶ T.pt := Classical.choose hex
    have hz := (Classical.choose_spec hex).1
    have hzuniq : ∀ y, (∀ i, (ConcreteCategory.hom ((yoneda.obj T.pt).map (f i).op)) y = φ i) →
        y = z := fun y hy => (Classical.choose_spec hex).2 y hy
    have hsY := hsheaf (Sieve.pullback c (Sieve.ofArrows Z' f)).arrows (by
      simpa only [Sieve.generate_sieve] using Scheme.fpqcTopology.pullback_stable c
        (Precoverage.generate_mem_toGrothendieck hfpqc))
    have hEq : c ≫ z = q := by
      apply hsY.isSeparatedFor.ext
      intro W g hg
      change g ≫ c ≫ z = g ≫ q
      rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at hg
      obtain ⟨i, k, hk⟩ := hg
      have hφi : f i ≫ z = φ i := by
        simpa [yoneda_obj_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op] using hz i
      calc
        g ≫ c ≫ z = (pullback.lift g k (by simp [← hk])) ≫
            pullback.fst c (f i) ≫ c ≫ z := by
          rw [pullback.lift_fst_assoc]
        _ = (pullback.lift g k (by simp [← hk])) ≫
            pullback.snd c (f i) ≫ φ i := by
          rw [← hφi, pullback.condition_assoc]
        _ = g ≫ q := by
          rw [← hfac i, pullback.lift_fst_assoc]
    refine ⟨z, ?_, ?_⟩
    · simpa [q, Cofork.π_ofπ] using hEq
    · intro m hm
      apply hzuniq m
      intro i
      have hlocal_i := Classical.choice (hlocal i)
      have : Epi (baseChangeCofork a b c h (f i)).π := Cofork.IsColimit.epi hlocal_i
      apply (cancel_epi (baseChangeCofork a b c h (f i)).π).1
      have hm' : c ≫ m = q := by simpa [Cofork.π_ofπ] using hm
      simp only [baseChangeCofork, Cofork.π_ofπ, yoneda_obj_map, TypeCat.ofHom_apply,
        Quiver.Hom.unop_op]
      change pullback.snd c (f i) ≫ f i ≫ m = pullback.snd c (f i) ≫ φ i
      rw [← Category.assoc, ← pullback.condition, Category.assoc, hm', (hfac i).symm]

end AlgebraicGeometry
