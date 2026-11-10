module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Complex
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Pushforward
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Sections of the relative Čech complex at an object

Let `f : 𝒰 ⥤ 𝒳` be a covering of a category fibred in groupoids over a base `𝒞`, let `x` be an
object of `𝒳` lying over `U : 𝒞`, and let `𝒴 = 𝒞/U` be the slice, mapping to `𝒳` by the
`1`-morphism `(T ⟶ U) ↦ T^*x` which represents `x`. Write `𝒱 = 𝒴 ×_{x, 𝒳} 𝒰` for the base change
of `f` along it, with projections `g : 𝒱 ⥤ 𝒴` and `h : 𝒱 ⥤ 𝒰`. Then the value at `x` of the
relative Čech complex of `f` is the Čech complex of the base-changed covering:

`Γ(x, 𝒦^•(f, ℱ)) = Č^•(𝒱 → 𝒴, x⁻¹ℱ)`.

The `1`-morphism `𝒱_n ⥤ 𝒰_n` of Čech nerves identifies `𝒱_n` with the base change
`𝒴 ×_{x, 𝒳} 𝒰_n`, and the pushforward formula of Stacks 06W6 computes the value at `x` of the
degree `n` term `f_{n,*}f_n⁻¹ℱ` as the global sections of `ℱ` over that 2-fibre product. The
identification is an isomorphism of complexes.

## Main definitions

* `Stacks.RelativeCech.nerveBaseChange`: the comparison `1`-morphism
  `𝒱_n ⥤ 𝒴 ×_{x, 𝒳} 𝒰_n`, and `Stacks.RelativeCech.nerveBaseChangeEquivalence` the equivalence
  it induces.
* `Stacks.RelativeCech.pushforwardCone`: the cone, indexed by the 2-fibre product, presenting
  `f_*ℱ(x)` as global sections; `Stacks.RelativeCech.isLimitPushforwardCone` is the assertion
  that it is a limit cone.
* `Stacks.RelativeCech.termSectionsIso`: the resulting identification in a fixed Čech degree.
* `Stacks.RelativeCech.complexSectionsIso`: the identification of complexes.

## Main results

* `Stacks.RelativeCech.nerveBaseChangeEquivalence_functor_comp_fst`,
  `Stacks.RelativeCech.nerveBaseChangeEquivalence_functor_comp_snd`: under the identification of
  each level of the Čech nerve of the base-changed covering with the base change of that level of
  the Čech nerve, both projections are the evident ones.
* `Stacks.RelativeCech.complexSectionsIso_π` pins the identification down componentwise: on a
  Čech tuple of the base-changed covering it restricts a relative section along the chosen
  pullback comparison and then applies the right-Kan-extension counit.
* `Stacks.RelativeCech.complexSectionsIso_naturality` records naturality in the coefficient
  presheaf.

## Implementation notes

The object `x` is represented by `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`, and the
base change is the 2-fibre product over the base, `CategoryTheory.TwoFibreProductOver`, whose
`2`-cell `ψ` is vertical; the verticality of `ψ⁻¹` needed by `Stacks.Cech.nerveMap` is
`Stacks.RelativeCech.isHomLift_psi_inv`. Evaluation of a complex of presheaves is performed
degreewise, by `CategoryTheory.Functor.mapHomologicalComplex` applied to an evaluation functor.

Stacks 06W6 is available for `Type`-valued presheaves. The abelian-group form used here is
obtained by transporting it along `CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves`
for the forgetful functor, which preserves right Kan extensions, and recognising the resulting
bijection as the comparison map of a cone; that is `isLimitPushforwardCone`. Once the index
category of that cone is replaced by the Čech nerve of the base change, which is legitimate
because the comparison functor is an equivalence and hence initial, the limit is the Čech term.

## References

* [Stacks Project, Tag 06XB](https://stacks.math.columbia.edu/tag/06XB)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 06X5](https://stacks.math.columbia.edu/tag/06X5)
* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

namespace Stacks.RelativeCech

attribute [local implicit_reducible] Functor.Fiber TwoFibreProductOver.fst
  TwoFibreProductOver.snd Cech.nerveMap Cech.cosimplicial Functor.ran Functor.ranCounit
  Functor.ChoiceOfPullbacks.sliceFunctor

section Psi

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- In the 2-fibre product of `F : 𝒳 ⥤ 𝒮` and `G : 𝒴 ⥤ 𝒮` over a base, formed with the
structure functor of `𝒴` equal to `G ⋙ p𝒮`, the inverse of the filling `2`-cell `ψ` lies over
an identity of the base, written at the object `p𝒮 (G y)` of the base. -/
public lemma isHomLift_psi_inv {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    (P : TwoFibreProductOver p𝒳 (G ⋙ p𝒮) p𝒮 F G) :
    p𝒮.IsHomLift (𝟙 (p𝒮.obj (G.obj P.y)))
      ((TwoFibreProductOver.psiIso p𝒳 (G ⋙ p𝒮) p𝒮 F G).symm.hom.app P) := by
  have hb : p𝒮.obj (G.obj P.y) = P.base := P.hy
  rw [hb]
  exact TwoFibreProductOver.psiIso_inv_vertical P

end Psi

universe uC uU uX vC vU vX w

variable {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X]

/-- The comparison `1`-morphism from the degree `n` Čech nerve of the base change of `f` to the
slice over `p(x)` to the base change of the degree `n` Čech nerve of `f`. On objects it keeps the
target of the tuple and sends the tuple to its image under `Stacks.Cech.nerveMap`, with the
identity comparison isomorphism. -/
@[reducible] public def nerveBaseChange (p : X ⥤ C) (f : U ⥤ X) (c : p.ChoiceOfPullbacks)
    {V : C} (x : p.Fiber V) (n : ℕ) :
    Tuple (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n ⥤
      TwoFibreProductOver (Over.forget V) (Tuple.projection p f n ⋙ p) p
        (c.sliceFunctor x) (Tuple.projection p f n) := by
  let e := c.sliceFunctor x
  let g := TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p e f
  let h := TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p e f
  let α := (TwoFibreProductOver.psiIso (Over.forget V) (f ⋙ p) p e f).symm
  let φ : Tuple (Over.forget V) g n ⥤ Tuple p f n :=
    Cech.nerveMap p (Over.forget V) f g h e α (c.sliceFunctor_comp x)
      (isHomLift_psi_inv (Over.forget V) p e f) n
  exact
    { obj z :=
        { base := p.obj (e.obj z.target)
          x := z.target
          y := φ.obj z
          hx := (Functor.congr_obj (c.sliceFunctor_comp x) z.target).symm
          hy := rfl
          iso := Iso.refl _
          vertical := IsHomLift.id (p := p) rfl }
      map {z z'} k :=
        { hbase := p.map (e.map k.target)
          a := k.target
          b := φ.map k
          ha := by
            have hs := Functor.congr_obj (c.sliceFunctor_comp x) z.target
            have ht := Functor.congr_obj (c.sliceFunctor_comp x) z'.target
            have hh := Functor.congr_hom (c.sliceFunctor_comp x) k.target
            simp only [Functor.comp_map] at hh
            apply IsHomLift.of_fac' (Over.forget V) _ k.target hs.symm ht.symm
            have hheq : p.map (e.map k.target) ≍ (Over.forget V).map k.target :=
              (conj_eqToHom_iff_heq (f := p.map (e.map k.target))
                (g := (Over.forget V).map k.target) (h := hs) (h' := ht)).1 hh
            exact (conj_eqToHom_iff_heq (f := (Over.forget V).map k.target)
              (g := p.map (e.map k.target)) (h := hs.symm) (h' := ht.symm)).2 hheq.symm
          hb := IsHomLift.map (p := Tuple.projection p f n ⋙ p) (φ.map k)
          w := by
            dsimp only [Tuple.projection, Functor.comp_obj]
            simp [e, φ, Cech.nerveMap] }
      map_id z := TwoFibreProductOver.Hom.ext' rfl (φ.map_id z)
      map_comp k l := TwoFibreProductOver.Hom.ext' rfl (φ.map_comp k l) }

/-- The comparison `1`-morphism of Čech nerves is an equivalence: a base-changed Čech tuple is
the same data as a Čech tuple of `f` together with a vertical comparison of its target with the
chosen pullback of `x`. -/
public instance isEquivalence_nerveBaseChange (p : X ⥤ C) (f : U ⥤ X)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V) (n : ℕ) :
    (nerveBaseChange p f c x n).IsEquivalence := by
  classical
  let e := c.sliceFunctor x
  let g := TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p e f
  let h := TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p e f
  let α := (TwoFibreProductOver.psiIso (Over.forget V) (f ⋙ p) p e f).symm
  let φ : Tuple (Over.forget V) g n ⥤ Tuple p f n :=
    Cech.nerveMap p (Over.forget V) f g h e α (c.sliceFunctor_comp x)
      (isHomLift_psi_inv (Over.forget V) p e f) n
  let A := Tuple (Over.forget V) g n
  let W := TwoFibreProductOver (Over.forget V) (Tuple.projection p f n ⋙ p) p e
    (Tuple.projection p f n)
  let F := nerveBaseChange p f c x n
  let G : W ⥤ A :=
    { obj P :=
        { target := P.x
          source := fun i =>
            { base := P.base
              x := P.x
              y := P.y.source i
              hx := P.hx
              hy := by
                have := P.y.comparison_lift i
                have hsource := IsHomLift.domain_eq p (𝟙 (p.obj P.y.target))
                  (P.y.comparison i).hom
                have hy : p.obj P.y.target = P.base := P.hy
                exact hsource.trans hy
              iso := P.iso ≪≫ (P.y.comparison i).symm
              vertical := by
                have h₁ := P.vertical
                have := P.y.comparison_lift i
                have hy : p.obj P.y.target = P.base := P.hy
                have hh : p.IsHomLift (𝟙 (p.obj P.y.target)) (P.y.comparison i).inv :=
                  inferInstance
                have h₂ : p.IsHomLift (𝟙 P.base) (P.y.comparison i).inv := by
                  rw [← hy]; exact hh
                have := h₁
                have := h₂
                change p.IsHomLift (𝟙 P.base) (P.iso.hom ≫ (P.y.comparison i).inv)
                infer_instance }
          comparison := fun _ => Iso.refl P.x
          comparison_lift := fun _ => IsHomLift.id (p := Over.forget V) rfl }
      map {P Q} k :=
        { target := k.a
          source := fun i =>
            { hbase := k.hbase
              a := k.a
              b := k.b.source i
              ha := k.ha
              hb := by
                have hP : p.IsHomLift (𝟙 P.base) (P.y.comparison i).hom := by
                  rw [← P.hy]; exact P.y.comparison_lift i
                have hQi : p.IsHomLift (𝟙 (p.obj Q.y.target)) (Q.y.comparison i).inv := by
                  have := Q.y.comparison_lift i
                  infer_instance
                have hQinv : p.IsHomLift (𝟙 Q.base) (Q.y.comparison i).inv := by
                  rw [← Q.hy]; exact hQi
                have hnat := k.b.comparison_naturality i
                have htarget : p.IsHomLift k.hbase k.b.target :=
                  (Functor.isHomLift_comp_iff (Tuple.projection p f n) p
                    k.hbase k.b).1 k.hb
                have := hP
                have := htarget
                have := hQinv
                have hlift : p.IsHomLift k.hbase
                    ((P.y.comparison i).hom ≫ k.b.target ≫ (Q.y.comparison i).inv) :=
                  inferInstance
                have heq : f.map (k.b.source i) =
                    (P.y.comparison i).hom ≫ k.b.target ≫ (Q.y.comparison i).inv := by
                  calc
                    f.map (k.b.source i) =
                        f.map (k.b.source i) ≫ (Q.y.comparison i).hom ≫
                          (Q.y.comparison i).inv := by simp
                    _ = (P.y.comparison i).hom ≫ k.b.target ≫
                          (Q.y.comparison i).inv := by
                      simpa [Category.assoc] using
                        congrArg (fun t => t ≫ (Q.y.comparison i).inv) hnat
                have hsource : p.IsHomLift k.hbase (f.map (k.b.source i)) := by
                  rw [heq]; exact hlift
                exact (Functor.isHomLift_comp_iff f p k.hbase (k.b.source i)).2 hsource
              w := by
                have hnat := k.b.comparison_naturality i
                change e.map k.a ≫ Q.iso.hom ≫ (Q.y.comparison i).symm.hom =
                  (P.iso.hom ≫ (P.y.comparison i).symm.hom) ≫ f.map (k.b.source i)
                have hbt : (P.y.comparison i).inv ≫ f.map (k.b.source i) ≫
                    (Q.y.comparison i).hom = k.b.target := by
                  calc
                    (P.y.comparison i).inv ≫ f.map (k.b.source i) ≫
                        (Q.y.comparison i).hom =
                        (P.y.comparison i).inv ≫
                          (f.map (k.b.source i) ≫ (Q.y.comparison i).hom) := by
                      simp []
                    _ = (P.y.comparison i).inv ≫
                          ((P.y.comparison i).hom ≫ k.b.target) := by
                      simpa [Category.assoc] using
                        congrArg (fun t => (P.y.comparison i).inv ≫ t) hnat
                    _ = k.b.target := by simp []
                have hbt' : k.b.target ≫ (Q.y.comparison i).inv =
                    (P.y.comparison i).inv ≫ f.map (k.b.source i) := by
                  rw [← hbt]; simp [Category.assoc]
                have hkw := congrArg (fun t => t ≫ (Q.y.comparison i).inv) k.w
                have hkw' : e.map k.a ≫ Q.iso.hom ≫ (Q.y.comparison i).inv =
                    P.iso.hom ≫ k.b.target ≫ (Q.y.comparison i).inv := by
                  simpa [Tuple.projection, Category.assoc] using hkw
                calc
                  e.map k.a ≫ Q.iso.hom ≫ (Q.y.comparison i).inv =
                      P.iso.hom ≫ (k.b.target ≫ (Q.y.comparison i).inv) := by
                    simpa [Category.assoc] using hkw'
                  _ = P.iso.hom ≫ ((P.y.comparison i).inv ≫ f.map (k.b.source i)) :=
                    congrArg (fun t => P.iso.hom ≫ t) hbt'
                  _ = (P.iso.hom ≫ (P.y.comparison i).symm.hom) ≫ f.map (k.b.source i) := by
                    rw [Iso.symm_hom]
                    exact (Category.assoc _ _ _).symm }
          comparison_naturality := by
            intro i
            change k.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ k.a
            simp }
      map_id P := by
        apply Cech.tupleHom_ext
        · rfl
        · funext i
          exact TwoFibreProductOver.Hom.ext' rfl rfl
      map_comp k l := by
        apply Cech.tupleHom_ext
        · rfl
        · funext i
          exact TwoFibreProductOver.Hom.ext' rfl rfl }
  have sourceBaseEq : ∀ (z : A) (i : Fin (n + 1)),
      (f ⋙ p).obj (z.source i).y = (Over.forget V).obj z.target := by
    intro z i
    have : (Over.forget V).IsHomLift
        (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom :=
      z.comparison_lift i
    have hdom := IsHomLift.domain_eq (Over.forget V)
      (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom
    calc
      (f ⋙ p).obj (z.source i).y = (z.source i).base := (z.source i).hy
      _ = (Over.forget V).obj (g.obj (z.source i)) := (z.source i).hx.symm
      _ = (Over.forget V).obj z.target := by simpa [g] using hdom
  let unitInvSrc : (z : A) → (i : Fin (n + 1)) →
      ((F ⋙ G).obj z).source i ⟶ z.source i := fun z i => by
    let a : z.target ⟶ (z.source i).x := (z.comparison i).inv
    let b : h.obj (z.source i) ⟶ (z.source i).y :=
      eqToHom (show h.obj (z.source i) = (z.source i).y from rfl)
    refine TwoFibreProductOver.Hom.mk' a b ?_ ?_
    · have : (Over.forget V).IsHomLift
          (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom :=
        z.comparison_lift i
      have : (Over.forget V).IsHomLift
          (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).inv :=
        IsHomLift.lift_id_inv (Over.forget V)
          ((Over.forget V).obj z.target) (z.comparison i)
      have hc := IsHomLift.fac' (Over.forget V)
        (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).inv
      have hc' : Over.Hom.left (z.comparison i).inv =
          eqToHom (IsHomLift.domain_eq (Over.forget V)
            (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).inv) ≫
            𝟙 ((Over.forget V).obj z.target) ≫
            eqToHom (IsHomLift.codomain_eq (Over.forget V)
              (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).inv).symm := by
        simpa using hc
      simp only [Tuple.projection, nerveBaseChange,
        Functor.ChoiceOfPullbacks.sliceFunctor_obj, TwoFibreProductOver.psiIso, Cech.nerveMap,
        Functor.comp_obj, Iso.trans_symm, eqToHom_refl, Functor.comp_map, Over.forget_obj,
        Over.forget_map, hc', Category.id_comp, eqToHom_trans, F, G, b, h, a]
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      simp
    · simp [F, nerveBaseChange, G, Cech.nerveMap, a, g,
        b, h, TwoFibreProductOver.psiIso, Category.assoc]
      simp [e]
  let unitApp : ∀ z : A, z ≅ (F ⋙ G).obj z := fun z => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨𝟙 _, fun i => ?_, ?_⟩
      · let a : (z.source i).x ⟶ z.target := (z.comparison i).hom
        have : (Over.forget V).IsHomLift
            (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom :=
          z.comparison_lift i
        let b : (z.source i).y ⟶ h.obj (z.source i) :=
          eqToHom (show (z.source i).y = h.obj (z.source i) from rfl)
        refine TwoFibreProductOver.Hom.mk' a b ?_ ?_
        · have : (Over.forget V).IsHomLift
              (𝟙 ((Over.forget V).obj z.target)) a := by
            simpa [a] using z.comparison_lift i
          have hc := IsHomLift.fac' (Over.forget V)
            (𝟙 ((Over.forget V).obj z.target)) a
          have hc' : Over.Hom.left (z.comparison i).hom =
              eqToHom (IsHomLift.domain_eq (Over.forget V)
                (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom) ≫
                𝟙 ((Over.forget V).obj z.target) ≫
                eqToHom (IsHomLift.codomain_eq (Over.forget V)
                  (𝟙 ((Over.forget V).obj z.target)) (z.comparison i).hom).symm := by
            simpa [a] using hc
          simp [a, b, h, F, nerveBaseChange, G, Cech.nerveMap, Tuple.projection,
            hc', eqToHom_refl]
        · simp [F, nerveBaseChange, G, Cech.nerveMap, a, b, h, g,
            TwoFibreProductOver.psiIso]
          simp [e]
      · intro i
        change (z.comparison i).hom ≫ 𝟙 z.target = (z.comparison i).hom ≫ 𝟙 z.target
        rfl
    · exact ⟨𝟙 _, unitInvSrc z, by
        intro i
        simp [unitInvSrc, g, F, nerveBaseChange, G, Cech.nerveMap,
          TwoFibreProductOver.fst_map, TwoFibreProductOver.Hom.mk'_a,
          Iso.inv_hom_id, h]
        rfl⟩
    · apply Cech.tupleHom_ext
      · change 𝟙 z.target ≫ 𝟙 z.target = 𝟙 z.target
        simp
      · funext i
        apply TwoFibreProductOver.Hom.ext'
        · change (z.comparison i).hom ≫ (z.comparison i).inv = 𝟙 _
          exact Iso.hom_inv_id _
        · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
          simp
    · apply Cech.tupleHom_ext
      · change 𝟙 z.target ≫ 𝟙 z.target = 𝟙 z.target
        simp
      · funext i
        apply TwoFibreProductOver.Hom.ext'
        · change (z.comparison i).inv ≫ (z.comparison i).hom = 𝟙 _
          exact Iso.inv_hom_id _
        · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
          simp
  let counitApp : ∀ P : W, P ≅ (G ⋙ F).obj P := fun P => by
    let yHom : Tuple.Hom p f P.y (φ.obj (G.obj P)) := by
      refine ⟨P.iso.inv, fun i => 𝟙 (P.y.source i), ?_⟩
      intro i
      change f.map (𝟙 (P.y.source i)) ≫
        (((P.y.comparison i).hom ≫ P.iso.inv) ≫ e.map (𝟙 P.x)) =
          (P.y.comparison i).hom ≫ P.iso.inv
      simp
    let yInv : Tuple.Hom p f (φ.obj (G.obj P)) P.y := by
      refine ⟨P.iso.hom, fun i => 𝟙 (P.y.source i), ?_⟩
      intro i
      change f.map (𝟙 (P.y.source i)) ≫ (P.y.comparison i).hom =
        (((P.y.comparison i).hom ≫ P.iso.inv) ≫ e.map (𝟙 P.x)) ≫ P.iso.hom
      simp [Category.assoc]
    have : p.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have : p.IsHomLift (𝟙 P.base) P.iso.inv := IsHomLift.lift_id_inv p P.base P.iso
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine TwoFibreProductOver.Hom.mk' (𝟙 P.x) yHom ?_ ?_
      · change eqToHom P.hy.symm ≫ p.map P.iso.inv ≫ _ = _
        rw [IsHomLift.fac' p (𝟙 P.base) P.iso.inv]
        simp only [Functor.comp_obj, Category.id_comp, eqToHom_trans, eqToHom_refl,
          eqToHom_trans_assoc, Over.forget_obj, Over.forget_map, Over.id_left]
        exact Category.comp_id _
      · change e.map (𝟙 P.x) ≫ 𝟙 _ = P.iso.hom ≫ P.iso.inv
        simp
    · refine TwoFibreProductOver.Hom.mk' (𝟙 P.x) yInv ?_ ?_
      · change _ ≫ p.map P.iso.hom ≫ eqToHom P.hy = _
        rw [IsHomLift.fac' p (𝟙 P.base) P.iso.hom]
        simp [F, nerveBaseChange, G, Tuple.projection, e]
      · change e.map (𝟙 P.x) ≫ P.iso.hom = 𝟙 _ ≫ P.iso.hom
        simp
    · apply TwoFibreProductOver.Hom.ext'
      · change 𝟙 P.x ≫ 𝟙 P.x = 𝟙 P.x
        simp
      · apply Cech.tupleHom_ext
        · change P.iso.inv ≫ P.iso.hom = 𝟙 _
          simp
        · funext i
          change 𝟙 (P.y.source i) ≫ 𝟙 _ = 𝟙 _
          simp
    · apply TwoFibreProductOver.Hom.ext'
      · change 𝟙 P.x ≫ 𝟙 P.x = 𝟙 P.x
        simp
      · apply Cech.tupleHom_ext
        · change P.iso.hom ≫ P.iso.inv = 𝟙 _
          simp
        · funext i
          change 𝟙 (P.y.source i) ≫ 𝟙 _ = 𝟙 _
          simp
  let E : A ≌ W :=
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents unitApp (by
        intro z z' k
        dsimp only [unitApp]
        apply Cech.tupleHom_ext
        · change k.target ≫ 𝟙 z'.target = 𝟙 z.target ≫ k.target
          simp
        · funext i
          apply TwoFibreProductOver.Hom.ext'
          · change (k.source i).a ≫ (z'.comparison i).hom =
              (z.comparison i).hom ≫ k.target
            exact k.comparison_naturality i
          · dsimp [CategoryTheory.CategoryStruct.comp, Tuple.instCategory, Tuple.homComp,
              TwoFibreProductOver.instCategory, TwoFibreProductOver.Hom.comp,
              F, G, φ, Cech.nerveMap, h]
            change (k.source i).b ≫ 𝟙 _ = 𝟙 _ ≫ (k.source i).b
            simp)
      counitIso := NatIso.ofComponents (fun P => (counitApp P).symm) (by
        intro P Q k
        apply TwoFibreProductOver.Hom.ext'
        · change k.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ k.a
          simp
        · apply Cech.tupleHom_ext
          · change e.map k.a ≫ Q.iso.hom = P.iso.hom ≫ k.b.target
            exact k.w
          · funext i
            change k.b.source i ≫ 𝟙 _ = 𝟙 _ ≫ k.b.source i
            simp)
      functor_unitIso_comp := by
        intro z
        apply TwoFibreProductOver.Hom.ext'
        · change 𝟙 z.target ≫ 𝟙 z.target = 𝟙 z.target
          simp
        · apply Cech.tupleHom_ext
          · change (c.sliceFunctor x).map (𝟙 z.target) ≫ 𝟙 _ = 𝟙 _
            simp
          · funext i
            change 𝟙 (z.source i).y ≫ 𝟙 _ = 𝟙 _
            simp }
  exact E.isEquivalence_functor

/-- The Čech nerve of the base change of `f` to the slice over `p(x)` is, in each degree, the base
change of the Čech nerve of `f`. -/
@[stacks 06XB "equivalence of Čech nerves"]
public def nerveBaseChangeEquivalence (p : X ⥤ C) (f : U ⥤ X) (c : p.ChoiceOfPullbacks)
    {V : C} (x : p.Fiber V) (n : ℕ) :
    Tuple (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n ≌
      TwoFibreProductOver (Over.forget V) (Tuple.projection p f n ⋙ p) p
        (c.sliceFunctor x) (Tuple.projection p f n) :=
  (nerveBaseChange p f c x n).asEquivalence

/-- The first projection of the base change of the Čech nerve corresponds, under the equivalence,
to the projection of the Čech nerve of the base change. -/
@[stacks 06XB "equivalence of Čech nerves"]
public theorem nerveBaseChangeEquivalence_functor_comp_fst (p : X ⥤ C) (f : U ⥤ X)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V) (n : ℕ) :
    (nerveBaseChangeEquivalence p f c x n).functor ⋙
        TwoFibreProductOver.fst (Over.forget V) (Tuple.projection p f n ⋙ p) p
          (c.sliceFunctor x) (Tuple.projection p f n) =
      Tuple.projection (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n :=
  rfl

/-- The second projection of the base change of the Čech nerve corresponds, under the equivalence,
to the `1`-morphism of Čech nerves of `Stacks.Cech.nerveMap`. -/
@[stacks 06XB "equivalence of Čech nerves"]
public theorem nerveBaseChangeEquivalence_functor_comp_snd (p : X ⥤ C) (f : U ⥤ X)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V) (n : ℕ) :
    (nerveBaseChangeEquivalence p f c x n).functor ⋙
        TwoFibreProductOver.snd (Over.forget V) (Tuple.projection p f n ⋙ p) p
          (c.sliceFunctor x) (Tuple.projection p f n) =
      Cech.nerveMap p (Over.forget V) f
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
        (TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
        (c.sliceFunctor x)
        (TwoFibreProductOver.psiIso (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f).symm
        (c.sliceFunctor_comp x)
        (isHomLift_psi_inv (Over.forget V) p (c.sliceFunctor x) f) n :=
  rfl

/-- The cone, indexed by the 2-fibre product `(𝒞/p(x)) ×_{x, 𝒳} 𝒰`, whose apex is the value at
`x` of the pushforward `f_*ℱ` and whose leg at an object of the 2-fibre product restricts along
the comparison arrow and applies the right-Kan-extension counit. -/
public def pushforwardCone (p : X ⥤ C) (f : U ⥤ X) (c : p.ChoiceOfPullbacks)
    {V : C} (x : p.Fiber V) (F : Uᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) :
    Cone ((TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f).op ⋙ F) where
  pt := (f.op.ran.obj F).obj (op x.1)
  π :=
    { app := fun P => (f.op.ran.obj F).map (P.unop.iso.inv ≫ c.map P.unop.x.hom x).op ≫
        (f.op.ranCounit.app F).app (op P.unop.y)
      naturality := by
        intro P Q k
        have hk : f.map k.unop.b ≫ P.unop.iso.inv ≫ c.map P.unop.x.hom x =
            Q.unop.iso.inv ≫ c.map Q.unop.x.hom x := by
          have hw : f.map k.unop.b ≫ P.unop.iso.inv =
              Q.unop.iso.inv ≫ (c.sliceFunctor x).map k.unop.a := by
            apply (Iso.eq_inv_comp _).2
            rw [← Category.assoc, ← k.unop.w]
            simp
          rw [← Category.assoc, hw, Category.assoc,
            Functor.ChoiceOfPullbacks.sliceFunctor_map_fac]
        have hn := (f.op.ranCounit.app F).naturality k.unop.b.op
        change (f.op.ran.obj F).map (f.map k.unop.b).op ≫
          (f.op.ranCounit.app F).app (op Q.unop.y) =
          (f.op.ranCounit.app F).app (op P.unop.y) ≫ F.map k.unop.b.op at hn
        dsimp
        rw [Category.id_comp, Category.assoc,
          show (TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f).map
              k.unop = k.unop.b from rfl,
          ← hn, ← Category.assoc, ← Functor.map_comp]
        congr 2
        exact congrArg Quiver.Hom.op hk.symm }

/-- The cone of `Stacks.RelativeCech.pushforwardCone` is a limit cone, so the value at `x` of the
pushforward of an abelian presheaf `ℱ` is the group of global sections of `ℱ` over the 2-fibre
product. -/
public def isLimitPushforwardCone (p : X ⥤ C) (f : U ⥤ X) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Uᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) :
    IsLimit (pushforwardCone p f c x F) := by
  let H := forget AddCommGrpCat.{max uU uX uC vU vX vC w}
  let α := H.rightKanExtensionCompIsoOfPreserves F f.op
  let E := ((Iso.toEquiv (α.app (op x.1))).trans
    (Presheaf.pushforwardSectionsEquiv (f ⋙ p) p f hp rfl c x (F ⋙ H))).trans
      (Presheaf.globalSectionsEquivSections _)
  apply isLimitOfReflects H
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).2
  have hE : Types.sectionOfCone (H.mapCone (pushforwardCone p f c x F)) = E := by
    funext s
    apply Subtype.ext
    funext P
    have h := Presheaf.pushforwardSectionsEquiv_apply
      (f ⋙ p) p f hp rfl c x (F ⋙ H) ((α.hom.app (op x.1)) s) P.unop
    change _ = ((Presheaf.globalSectionsEquivSections _)
      (Presheaf.pushforwardSectionsEquiv (f ⋙ p) p f hp rfl c x (F ⋙ H)
        ((α.hom.app (op x.1)) s))).1 P
    rw [h]
    have hn := α.hom.naturality (P.unop.iso.inv ≫ c.map P.unop.x.hom x).op
    change H.map ((f.op.ran.obj F).map (P.unop.iso.inv ≫ c.map P.unop.x.hom x).op) ≫
      α.hom.app (op (f.obj P.unop.y)) = α.hom.app (op x.1) ≫
      (f.op.ran.obj (F ⋙ H)).map (P.unop.iso.inv ≫ c.map P.unop.x.hom x).op at hn
    have hf := H.rightKanExtensionCompIsoOfPreserves_hom_fac_app F f.op (op P.unop.y)
    change α.hom.app (op (f.obj P.unop.y)) ≫
      (f.op.ranCounit.app (F ⋙ H)).app (op P.unop.y) =
      H.map ((f.op.ranCounit.app F).app (op P.unop.y)) at hf
    change _ = ((α.hom.app (op x.1) ≫
      (f.op.ran.obj (F ⋙ H)).map (P.unop.iso.inv ≫ c.map P.unop.x.hom x).op ≫
      (f.op.ranCounit.app (F ⋙ H)).app (op P.unop.y)) s)
    rw [← Category.assoc, ← hn, Category.assoc, hf]
    rfl
  rw [hE]
  exact E.bijective

/-- The value at `x` of the degree `n` term of the relative Čech complex is the degree `n` term
of the Čech complex of the base-changed covering. -/
public def termSectionsIso (p : X ⥤ C) (f : U ⥤ X) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) (n : ℕ) :
    (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).obj (op x.1) ≅
      Cech.term (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
        ((c.sliceFunctor x).op ⋙ F) n :=
  ((Functor.Initial.isLimitWhiskerEquiv (nerveBaseChange p f c x n).op
      (pushforwardCone p (Tuple.projection p f n) c x
        ((Tuple.projection p f n).op ⋙ F))).symm
    (isLimitPushforwardCone p (Tuple.projection p f n) hp c x
      ((Tuple.projection p f n).op ⋙ F))).conePointUniqueUpToIso
    (limit.isLimit ((Tuple.projection (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
        (c.sliceFunctor x).op ⋙ F))

/-- The degreewise identification restricts a relative section along the chosen pullback
comparison of the tuple's target and then applies the right-Kan-extension counit. -/
public theorem termSectionsIso_π (p : X ⥤ C) (f : U ⥤ X) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) (n : ℕ)
    (a : Tuple (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n) :
    (termSectionsIso p f hp c x F n).hom ≫
        limit.π ((Tuple.projection (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
            (c.sliceFunctor x).op ⋙ F) (op a) =
      (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).map
          (c.map a.target.hom x).op ≫
        ((Tuple.projection p f n).op.ranCounit.app ((Tuple.projection p f n).op ⋙ F)).app
          (op ((nerveBaseChange p f c x n).obj a).y) := by
  have hh := ((Functor.Initial.isLimitWhiskerEquiv (nerveBaseChange p f c x n).op
      (pushforwardCone p (Tuple.projection p f n) c x
        ((Tuple.projection p f n).op ⋙ F))).symm
    (isLimitPushforwardCone p (Tuple.projection p f n) hp c x
      ((Tuple.projection p f n).op ⋙ F))).conePointUniqueUpToIso_hom_comp
        (limit.isLimit ((Tuple.projection (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
            (c.sliceFunctor x).op ⋙ F)) (op a)
  change (termSectionsIso p f hp c x F n).hom ≫ _ =
    (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).map
      ((𝟙 _) ≫ c.map a.target.hom x).op ≫ _ at hh
  change (termSectionsIso p f hp c x F n).hom ≫
    limit.π ((Tuple.projection (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
        (c.sliceFunctor x).op ⋙ F) (op a) = _ at hh
  simpa only [Category.id_comp, Functor.op_obj, unop_op] using hh

/-- The degreewise identifications are compatible with the coface pullback maps. -/
public theorem termSectionsIso_comp_reindexMap (p : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (reindexMap.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F φ).app (op x.1) ≫
        (termSectionsIso p f hp c x F n).hom =
      (termSectionsIso p f hp c x F m).hom ≫
        Cech.reindexMap (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
          ((c.sliceFunctor x).op ⋙ F) φ := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, termSectionsIso_π, Category.assoc, Cech.reindexMap_π,
    termSectionsIso_π, ← Category.assoc, ← NatTrans.naturality, Category.assoc]
  exact congrArg (fun k => (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F m).map
      (c.map a.unop.target.hom x).op ≫ k)
    (congr_app (reindexMap_fac.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F φ)
      (op ((nerveBaseChange p f c x n).obj a.unop).y))

/-- The value at an object `x` of `𝒳` of the relative Čech complex of `f` is canonically the Čech
complex of the base change of `f` to the slice `𝒞/p(x)`, which represents `x`. This is an
isomorphism of complexes: it is compatible with the Čech differentials. -/
@[stacks 06XB "isomorphism of complexes"]
public def complexSectionsIso (p : X ⥤ C) (f : U ⥤ X) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) :
    (((evaluation Xᵒᵖ AddCommGrpCat.{max uU uX uC vU vX vC w}).obj
          (op x.1)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (complex.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F) ≅
      Cech.complex (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
        ((c.sliceFunctor x).op ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (termSectionsIso p f hp c x F) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simp only [Cech.complex_X]
    change (termSectionsIso p f hp c x F i).hom ≫
        (Cech.complex (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
          ((c.sliceFunctor x).op ⋙ F)).d i (i + 1) =
      ((evaluation Xᵒᵖ AddCommGrpCat.{max uU uX uC vU vX vC w}).obj (op x.1)).map
        ((complex.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F).d i (i + 1)) ≫
          (termSectionsIso p f hp c x F (i + 1)).hom
    rw [Cech.complex_d, complex_d]
    simp only [Cech.complex_X, complex_X, Cech.cosimplicial_δ, Functor.map_sum,
      Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    exact Finset.sum_congr rfl fun k _ => congrArg (fun t => (-1 : ℤ) ^ (k : ℕ) • t)
      (termSectionsIso_comp_reindexMap p f hp c x F (SimplexCategory.δ k)).symm)

/-- On a Čech tuple of the base-changed covering, the identification of complexes restricts a
relative section along the chosen pullback comparison of the tuple's target and then applies the
right-Kan-extension counit. -/
@[stacks 06XB "componentwise identification"]
public theorem complexSectionsIso_π (p : X ⥤ C) (f : U ⥤ X) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) (n : ℕ)
    (a : Tuple (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n)
    (s : (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).obj (op x.1)) :
    ((complexSectionsIso p f hp c x F).hom.f n ≫
        limit.π ((Tuple.projection (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
            (c.sliceFunctor x).op ⋙ F) (op a)) s =
      ((Tuple.projection p f n).op.ranCounit.app ((Tuple.projection p f n).op ⋙ F)).app
          (op ((Cech.nerveMap p (Over.forget V) f
            (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
            (TwoFibreProductOver.snd (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f)
            (c.sliceFunctor x)
            (TwoFibreProductOver.psiIso (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f).symm
            (c.sliceFunctor_comp x)
            (isHomLift_psi_inv (Over.forget V) p (c.sliceFunctor x) f) n).obj a))
        ((term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).map
          (c.map a.target.hom x).op s) :=
  congrArg (fun k => k s) (termSectionsIso_π p f hp c x F n a)

/-- The identification commutes in every degree with a morphism of coefficient presheaves; in
particular it is natural in the abelian presheaf. -/
@[stacks 06XB "naturality in the coefficient presheaf"]
public theorem complexSectionsIso_naturality (p : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (F G : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX uC vU vX vC w}) (η : F ⟶ G) (n : ℕ) :
    ((Tuple.projection p f n).op.ran.map
          (Functor.whiskerLeft (Tuple.projection p f n).op η)).app (op x.1) ≫
        (complexSectionsIso p f hp c x G).hom.f n =
      (complexSectionsIso p f hp c x F).hom.f n ≫
        limMap (Functor.whiskerLeft ((Tuple.projection (Over.forget V)
          (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n) ⋙
            c.sliceFunctor x).op η) := by
  change ((Tuple.projection p f n).op.ran.map
      (Functor.whiskerLeft (Tuple.projection p f n).op η)).app (op x.1) ≫
      (termSectionsIso p f hp c x G n).hom =
    (termSectionsIso p f hp c x F n).hom ≫ _
  apply limit.hom_ext
  intro a
  have hl := limMap_π (Functor.whiskerLeft ((Tuple.projection (Over.forget V)
    (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n) ⋙
      c.sliceFunctor x).op η) a
  change limMap (Functor.whiskerLeft ((Tuple.projection (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n) ⋙
        c.sliceFunctor x).op η) ≫
      limit.π ((Tuple.projection (Over.forget V)
        (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
          (c.sliceFunctor x).op ⋙ G) a =
    limit.π ((Tuple.projection (Over.forget V)
      (TwoFibreProductOver.fst (Over.forget V) (f ⋙ p) p (c.sliceFunctor x) f) n).op ⋙
        (c.sliceFunctor x).op ⋙ F) a ≫
      η.app (op ((c.sliceFunctor x).obj a.unop.target)) at hl
  rw [Category.assoc, termSectionsIso_π, Category.assoc, hl,
    ← Category.assoc (termSectionsIso p f hp c x F n).hom, termSectionsIso_π,
    Category.assoc, ← Category.assoc]
  dsimp only [term]
  rw [← NatTrans.naturality, Category.assoc]
  exact congrArg (fun k =>
      (term.{vU, vX, vC, uU, uX, uC, max uC vC vU w} p f F n).map
        (c.map a.unop.target.hom x).op ≫ k)
    (congr_app ((Tuple.projection p f n).op.ranCounit.naturality
      (Functor.whiskerLeft (Tuple.projection p f n).op η))
        (op ((nerveBaseChange p f c x n).obj a.unop).y))

end Stacks.RelativeCech

end
