module

public import Mathlib.CategoryTheory.RepresentedBy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceFunctorComparison
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct

/-!
# Representable morphisms of categories fibred in groupoids

A morphism of categories fibred in groupoids over the big fppf category of a scheme is
representable exactly when, for each object `y` of the target, the presheaf `x ↦ Hom(F x, y)`
on the source category is representable.

Both directions go through the 2-fibre product of the source with a slice of the base. A
terminal object of that 2-fibre product is the same thing as a universal element of the
hom-presheaf: `homOfPairMorphism` turns a morphism of hom-presheaves into a morphism of the
2-fibre product, and `pairOfMorphism` turns an element of the hom-presheaf into an object of
it. Having a terminal object is in turn equivalent to being representable as a category fibred
in groupoids, which is `representableCFG_of_terminal` and
`exists_terminal_of_isRepresentableCFG`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isRepresentableMorphism_iff_forall_isRepresentable`: the
  representability criterion in terms of hom-presheaves.
* `Stacks.RepresentableMorphism.isRepresentableCFG_iff_nonempty_isTerminal`: a category fibred
  in groupoids is representable exactly when it has a terminal object.

## Implementation notes

The presheaf at `y` is the composite of the opposite of the morphism with the Yoneda presheaf
of `y`, so representability includes a natural isomorphism of functors rather than merely
objectwise bijections.

## References

* [Stacks Project, Tag 06W7](https://stacks.math.columbia.edu/tag/06W7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

universe u v u₁ u₂ u₃ v₁ v₂ v₃

open Functor.ChoiceOfPullbacks

attribute [local implicit_reducible] Functor.Fiber

section Terminal

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
  {p : X ⥤ C} (hp : p.IsFiberedInGroupoids) {t : X} (ht : Limits.IsTerminal t)

include hp ht in
private lemma faithful_of_terminal {a b : X} (f g : a ⟶ b) (h : p.map f = p.map g) : f = g := by
  obtain ⟨l, hl, huniq⟩ := hp.unique_lift (ht.from b) (ht.from a) (p.map f)
    (by rw [← p.map_comp, ht.hom_ext (f ≫ ht.from b) (ht.from a)])
  exact (huniq f ⟨rfl, ht.hom_ext _ _⟩).trans (huniq g ⟨h.symm, ht.hom_ext _ _⟩).symm

/-- A fibre object determines a base morphism to the image of the terminal object. -/
private def terminalClassMap (U : C) : StacksRepresentableCFG.IsoClass p U → (U ⟶ p.obj t) :=
  Quotient.lift (fun x : p.Fiber U => eqToHom x.2.symm ≫ p.map (ht.from x.1)) (by
    rintro a b ⟨i⟩
    have hi := (i.hom).property
    have h := congrArg p.map (ht.hom_ext
      (Functor.Fiber.fiberInclusion.map i.hom ≫ ht.from b.1) (ht.from a.1))
    have hmap : p.map (Functor.Fiber.fiberInclusion.map i.hom) =
        eqToHom a.2 ≫ eqToHom b.2.symm := by
      have hfac := IsHomLift.fac' p (𝟙 U) (Functor.Fiber.fiberInclusion.map i.hom)
      dsimp only [Functor.Fiber.fiberInclusion] at hfac ⊢
      simpa only [Category.id_comp] using hfac
    rw [p.map_comp (Functor.Fiber.fiberInclusion.map i.hom) (ht.from b.1)] at h
    rw [hmap] at h
    have hcancel : eqToHom a.2.symm ≫ eqToHom a.2 = 𝟙 U := by simp
    have hh := (congrArg (eqToHom a.2.symm ≫ ·) h).symm
    dsimp only [Functor.Fiber.fiberInclusion] at hh ⊢
    simpa only [← Category.assoc, hcancel, Category.id_comp] using hh)

include hp in
private lemma terminalClassMap_bijective (U : C) :
    Function.Bijective (terminalClassMap (p := p) ht U) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    intro h
    change eqToHom a.2.symm ≫ p.map (ht.from a.1) =
      eqToHom b.2.symm ≫ p.map (ht.from b.1) at h
    let f : U ⟶ p.obj t := eqToHom a.2.symm ≫ p.map (ht.from a.1)
    have ha : p.IsHomLift f (ht.from a.1) := IsHomLift.of_fac' p f _ a.2 rfl (by simp [f])
    have hb : p.IsHomLift f (ht.from b.1) :=
      IsHomLift.of_fac' p f _ b.2 rfl (by dsimp [f]; rw [h]; simp)
    exact Quotient.sound ⟨Functor.Fiber.isoMk
      (Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso p hp f (ht.from a.1) (ht.from b.1) ha
        hb)
      (Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso_isHomLift p hp f _ _ ha hb)⟩
  · intro f
    obtain ⟨x, φ, hφ⟩ := hp.exists_lift f t rfl
    refine ⟨StacksRepresentableCFG.IsoClass.mk p ⟨x, IsHomLift.domain_eq p f φ⟩, ?_⟩
    change eqToHom _ ≫ p.map (ht.from x) = f
    rw [ht.hom_ext (ht.from x) φ, IsHomLift.fac' p f φ]
    simp

include hp ht in
/-- A terminal object in a category fibred in groupoids represents the fibration. -/
private lemma representableCFG_of_terminal : Stacks.RepresentableMorphism.IsRepresentableCFG p := by
  apply Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable
  apply (StacksRepresentableCFG.representable_iff p).2
  refine ⟨⟨hp, ?_⟩, p.obj t, ⟨{
    equiv := fun U => Equiv.ofBijective
      (terminalClassMap ht U) (terminalClassMap_bijective hp ht U)
    naturality := ?_ }⟩⟩
  · intro U a b
    refine ⟨fun f g => Functor.Fiber.hom_ext (faithful_of_terminal hp ht _ _ ?_)⟩
    have hf := f.property
    have hg := g.property
    rw [IsHomLift.fac' p (𝟙 U) (Functor.Fiber.fiberInclusion.map f),
      IsHomLift.fac' p (𝟙 U) (Functor.Fiber.fiberInclusion.map g)]
  · intro U V f x y hxy
    obtain ⟨φ, hφ, _⟩ := hxy
    change eqToHom y.2.symm ≫ p.map (ht.from y.1) =
      f ≫ eqToHom x.2.symm ≫ p.map (ht.from x.1)
    rw [ht.hom_ext (ht.from y.1) (φ ≫ ht.from x.1), p.map_comp, IsHomLift.fac' p f φ]
    simp

end Terminal

private lemma exists_terminal_of_isRepresentableCFG
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : Stacks.RepresentableMorphism.IsRepresentableCFG p) :
    Nonempty (Σ t : X, Limits.IsTerminal t) := by
  obtain ⟨c, E, hE⟩ := hp
  have := Stacks.RepresentableMorphism.SliceEquivalence.isEquivalence_of_isEquivalenceOver p c E hE
  exact ⟨⟨E.asEquivalence.inverse.obj (Over.mk (𝟙 c)),
    Limits.IsTerminal.isTerminalObj E.asEquivalence.inverse _ Over.mkIdTerminal⟩⟩

/-- **A category fibred in groupoids is representable exactly when it has a terminal object.**
For `p : X ⥤ C` fibred in groupoids, `p` is representable in the sense of Stacks 02Y3 — equivalent
over `C` to a slice `C/U` — if and only if `X` has a terminal object: a slice has the terminal
object `𝟙 U`, and a terminal object `t` of `X` represents `p` by `p.obj t`.

The condition on the right does not mention the base, so it is the form in which representability
is compared across a change of base, such as from a slice `C/U` to `C`. -/
theorem _root_.Stacks.RepresentableMorphism.isRepresentableCFG_iff_nonempty_isTerminal
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    {p : X ⥤ C} (hp : p.IsFiberedInGroupoids) :
    Stacks.RepresentableMorphism.IsRepresentableCFG p ↔
      Nonempty (Σ t : X, Limits.IsTerminal t) :=
  ⟨exists_terminal_of_isRepresentableCFG p, fun ⟨⟨_, ht⟩⟩ => representableCFG_of_terminal hp ht⟩

section HomPresheaf

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
  {Y : Type u₃} [Category.{v₃} Y]
  {p : X ⥤ C} {q : Y ⥤ C} {F : X ⥤ Y} {U : C} {G : Over U ⥤ Y}
  (hF : F ⋙ q = p) (hG : G ⋙ q = Over.forget U)
  (hq : q.IsFiberedInGroupoids)

private lemma map_over {A B : Over U} (a : A ⟶ B) :
    q.map (G.map a) = eqToHom (Functor.congr_obj hG A) ≫ a.left ≫
      eqToHom (Functor.congr_obj hG B).symm := by
  simpa only [Functor.comp_map, Over.forget_map] using Functor.congr_hom hG a

private lemma map_over_F {A B : X} (a : A ⟶ B) :
    q.map (F.map a) = eqToHom (Functor.congr_obj hF A) ≫ p.map a ≫
      eqToHom (Functor.congr_obj hF B).symm := by
  simpa only [Functor.comp_map] using Functor.congr_hom hF a

/-- Forgetting the base arrow of a triple gives a morphism to the value at the identity. -/
private abbrev pairMorphism (P : TwoFibreProductOver (Over.forget U) p q G F) :=
  P.iso.inv ≫ G.map (toTerminal P.x)

private lemma pullbackHom_ext {P Q : TwoFibreProductOver (Over.forget U) p q G F}
    {f g : P ⟶ Q} (hb : f.b = g.b) : f = g := by
  apply TwoFibreProductOver.Hom.ext' _ hb
  apply Over.OverMorphism.ext
  have hf := f.ha
  have hg := g.ha
  have hfb := f.hb
  have hgb := g.hb
  have he : f.hbase = g.hbase := by
    have hh := congrArg p.map hb
    rw [IsHomLift.fac' p f.hbase f.b, IsHomLift.fac' p g.hbase g.b] at hh
    simpa using congrArg (fun k => eqToHom P.hy.symm ≫ k ≫ eqToHom Q.hy) hh
  have hh := IsHomLift.fac' (Over.forget U) f.hbase f.a
  have hh' := IsHomLift.fac' (Over.forget U) g.hbase g.a
  exact hh.trans (by simpa [he] using hh'.symm)

private lemma pairMorphism_naturality {P Q : TwoFibreProductOver (Over.forget U) p q G F}
    (f : P ⟶ Q) : F.map f.b ≫ pairMorphism Q = pairMorphism P := by
  dsimp only [pairMorphism]
  apply (cancel_epi P.iso.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← f.w]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← G.map_comp, comp_toTerminal]

/-- A commuting triangle in the source lifts to a morphism of the 2-fibre product. -/
private noncomputable def homOfPairMorphism
    {P Q : TwoFibreProductOver (Over.forget U) p q G F}
    (b : P.y ⟶ Q.y) (hb : F.map b ≫ pairMorphism Q = pairMorphism P) : P ⟶ Q := by
  let δ : G.obj P.x ⟶ G.obj Q.x := P.iso.hom ≫ F.map b ≫ Q.iso.inv
  have hδ : δ ≫ G.map (toTerminal Q.x) = G.map (toTerminal P.x) := by
    dsimp [δ]
    simpa [pairMorphism, Category.assoc] using congrArg (P.iso.hom ≫ ·) hb
  let a₀ : P.x.left ⟶ Q.x.left :=
    eqToHom (Functor.congr_obj hG P.x).symm ≫ q.map δ ≫ eqToHom (Functor.congr_obj hG Q.x)
  have ha₀ : a₀ ≫ Q.x.hom = P.x.hom := by
    have hh := congrArg q.map hδ
    rw [q.map_comp, map_over hG (toTerminal Q.x), map_over hG (toTerminal P.x)] at hh
    dsimp [toTerminal] at hh
    simpa [a₀, Category.assoc] using
      congrArg (fun k => eqToHom (Functor.congr_obj hG P.x).symm ≫ k ≫
        eqToHom (Functor.congr_obj hG (Over.mk (𝟙 U)))) hh
  let a : P.x ⟶ Q.x := Over.homMk a₀ ha₀
  have ha : q.map (G.map a) = q.map δ := by
    rw [map_over hG a]
    simp [a, a₀]
  have hGa : G.map a = δ := by
    obtain ⟨l, hl, huniq⟩ := hq.unique_lift (G.map (toTerminal Q.x))
      (G.map (toTerminal P.x)) (q.map δ) (by rw [← q.map_comp, hδ])
    apply (huniq _ ⟨ha, ?_⟩).trans (huniq _ ⟨rfl, hδ⟩).symm
    rw [← G.map_comp, comp_toTerminal]
  refine TwoFibreProductOver.Hom.mk' a b ?_ ?_
  · have hPv := P.vertical
    have hQv := Q.vertical
    have hQinv := IsHomLift.lift_id_inv q Q.base Q.iso
    change eqToHom P.hy.symm ≫ p.map b ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ a₀ ≫ eqToHom Q.hx
    dsimp only [a₀, δ]
    rw [q.map_comp, q.map_comp, IsHomLift.fac' q (𝟙 P.base) P.iso.hom,
      IsHomLift.fac' q (𝟙 Q.base) Q.iso.inv, map_over_F hF b]
    simp
  · rw [hGa]
    simp [δ, Category.assoc]

/-- A morphism `β` into `G (𝟙 U)` lies over its image in the base, transported along `hG`. -/
private lemma isHomLift_map_comp_eqToHom {x : Y} (β : x ⟶ G.obj (Over.mk (𝟙 U))) :
    q.IsHomLift (q.map β ≫ eqToHom (Functor.congr_obj hG (Over.mk (𝟙 U)))) β :=
  IsHomLift.of_fac' q _ β rfl (Functor.congr_obj hG (Over.mk (𝟙 U))) (by simp)

/-- Factor a morphism through the cartesian arrow classified by its image in the base. -/
private noncomputable abbrev pairOfMorphism (x : X) (β : F.obj x ⟶ G.obj (Over.mk (𝟙 U))) :
    TwoFibreProductOver (Over.forget U) p q G F := by
  let f := q.map β ≫ eqToHom (Functor.congr_obj hG (Over.mk (𝟙 U)))
  have hβ := isHomLift_map_comp_eqToHom hG β
  have hGf := map_toTerminal_isHomLift G hG (Over.mk f)
  exact {
    base := q.obj (F.obj x)
    x := Over.mk f
    y := x
    hx := rfl
    hy := (Functor.congr_obj hF x).symm
    iso := Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso q hq f
      (G.map (toTerminal (Over.mk f))) β
      hGf hβ
    vertical := Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso_isHomLift q hq f _ _ hGf hβ
      }

private lemma pairMorphism_pairOfMorphism (x : X) (β : F.obj x ⟶ G.obj (Over.mk (𝟙 U))) :
    pairMorphism (pairOfMorphism hF hG hq x β) = β := by
  let f := q.map β ≫ eqToHom (Functor.congr_obj hG (Over.mk (𝟙 U)))
  have hβ := isHomLift_map_comp_eqToHom hG β
  have hGf := map_toTerminal_isHomLift G hG (Over.mk f)
  have h : (pairOfMorphism hF hG hq x β).iso.hom ≫ β =
      G.map (toTerminal (pairOfMorphism hF hG hq x β).x) :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso_comp q hq f _ β hGf hβ
  dsimp only [pairMorphism]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (congrArg ((pairOfMorphism hF hG hq x β).iso.inv ≫ ·) h).symm

include hF hG hq in
/-- The terminal triple gives the universal element of the hom-presheaf. -/
private lemma representable_of_terminal_product
    {P : TwoFibreProductOver (Over.forget U) p q G F} (ht : Limits.IsTerminal P) :
    (F.op ⋙ yoneda.obj (G.obj (Over.mk (𝟙 U)))).IsRepresentable := by
  classical
  refine ⟨⟨P.y, ⟨{
    homEquiv := fun {x} => {
      toFun := fun b => F.map b ≫ pairMorphism P
      invFun := fun β => (ht.from (pairOfMorphism hF hG hq x β)).b
      left_inv := ?_
      right_inv := ?_ }
    homEquiv_comp := ?_ }⟩⟩⟩
  · intro b; rename_i x
    exact congrArg TwoFibreProductOver.Hom.b (ht.hom_ext
      (ht.from (pairOfMorphism hF hG hq x (F.map b ≫ pairMorphism P)))
      (homOfPairMorphism hF hG hq (P := pairOfMorphism hF hG hq x (F.map b ≫ pairMorphism P))
        (Q := P) b (pairMorphism_pairOfMorphism hF hG hq x _).symm))
  · intro β; rename_i x
    exact (pairMorphism_naturality (ht.from (pairOfMorphism hF hG hq x β))).trans
      (pairMorphism_pairOfMorphism hF hG hq x β)
  · intro x x' f g
    change F.map (f ≫ g) ≫ pairMorphism P = F.map f ≫ (F.map g ≫ pairMorphism P)
    rw [F.map_comp, Category.assoc]

include hF hG hq in
/-- The universal element of the hom-presheaf gives a terminal triple. -/
private lemma terminal_product_of_representable
    (hr : (F.op ⋙ yoneda.obj (G.obj (Over.mk (𝟙 U)))).IsRepresentable) :
    Nonempty (Σ P : TwoFibreProductOver (Over.forget U) p q G F, Limits.IsTerminal P) := by
  classical
  obtain ⟨x, ⟨R⟩⟩ := hr
  let β : F.obj x ⟶ G.obj (Over.mk (𝟙 U)) := R.homEquiv (𝟙 x)
  let P := pairOfMorphism hF hG hq x β
  have hP : pairMorphism P = β := pairMorphism_pairOfMorphism hF hG hq x β
  have hR {a : X} (b : a ⟶ x) : R.homEquiv b = F.map b ≫ β := R.homEquiv_eq b
  let toP (Q : TwoFibreProductOver (Over.forget U) p q G F) : Q ⟶ P :=
    homOfPairMorphism hF hG hq (R.homEquiv.symm (pairMorphism Q)) (by
      rw [hP, ← hR, Equiv.apply_symm_apply])
  refine ⟨⟨P, Limits.IsTerminal.ofUniqueHom toP (fun Q f => ?_)⟩⟩
  apply pullbackHom_ext
  apply R.homEquiv.injective
  change R.homEquiv f.b = R.homEquiv (R.homEquiv.symm (pairMorphism Q))
  rw [Equiv.apply_symm_apply, hR, ← hP]
  exact pairMorphism_naturality f

end HomPresheaf

/-- A representable 1-morphism has representable hom-presheaves `x ↦ Hom(F x, y)`. -/
private lemma isRepresentable_of_isRepresentableMorphism
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] {Y : Type u₃}
    [Category.{v₃} Y] {p : X ⥤ C} {q : Y ⥤ C} {F : X ⥤ Y} (hF : F ⋙ q = p)
    (hq : q.IsFiberedInGroupoids)
    (hr : Stacks.RepresentableMorphism.IsRepresentableMorphism p q F) (y : Y) :
    (F.op ⋙ yoneda.obj y).IsRepresentable := by
  obtain ⟨G, hG, ξ, -⟩ :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor q hq (q.obj y) y
      rfl
  obtain ⟨⟨P, hP⟩⟩ := exists_terminal_of_isRepresentableCFG _ (hr _ G hG)
  obtain ⟨x, ⟨R⟩⟩ := representable_of_terminal_product hF hG hq hP
  exact ⟨⟨x, ⟨R.ofIso (Functor.isoWhiskerLeft F.op (yoneda.mapIso ξ))⟩⟩⟩

/-- **Stacks 06W7.** A morphism of categories fibred in groupoids over the big fppf category of
`S` is representable if and only if every presheaf `x ↦ Hom(F x, y)` on the source category is
representable. -/
@[stacks 06W7]
theorem isRepresentableMorphism_iff_forall_isRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{u + 1} 𝒳] [Category.{u + 1} 𝒴]
    (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS)
    (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS)
    (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism p𝒳 p𝒴 F ↔
      ∀ y : 𝒴, (F.op ⋙ yoneda.obj y).IsRepresentable := by
  constructor
  · exact fun hr y => isRepresentable_of_isRepresentableMorphism hF h𝒴 hr y
  · intro hr U G hG
    obtain ⟨⟨P, hP⟩⟩ := terminal_product_of_representable hF hG h𝒴 (hr _)
    exact representableCFG_of_terminal
      (TwoFibreProductOver.fst_isFiberedInGroupoids U p𝒳 p𝒴 F G h𝒳 h𝒴 hF hG) hP

/-- **The representability criterion of Stacks 06W7, the direction that builds a representation,
for categories fibred in groupoids over an arbitrary base and at arbitrary universes.** If every
presheaf `x ↦ Hom(F x, y)` on the source is representable, then `F` is representable: the
representing element of the hom-presheaf at `G(id_U)` is a terminal object of each 2-fibre product
`(𝒞/U) ×_𝒴 𝒳`. Unlike
`AlgebraicGeometry.BigFppfOver.isRepresentableMorphism_iff_forall_isRepresentable` this asks
nothing of the hom universes beyond their agreement on source and target, so it applies to the
categories fibred in groupoids of algebraic stacks, whose morphisms lie in the universe of the
base. -/
theorem isRepresentableMorphism_of_forall_isRepresentable
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] {Y : Type u₃}
    [Category.{v₂} Y] {p : X ⥤ C} {q : Y ⥤ C} (F : X ⥤ Y) (hF : F ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hr : ∀ y : Y, (F.op ⋙ yoneda.obj y).IsRepresentable) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism p q F := by
  intro U G hG
  obtain ⟨⟨P, hP⟩⟩ := terminal_product_of_representable hF hG hq (hr _)
  exact representableCFG_of_terminal
    (TwoFibreProductOver.fst_isFiberedInGroupoids U p q F G hp hq hF hG) hP

/-- **A representable 1-morphism has terminal arrows into every object, at arbitrary
universes.** If `F : X ⥤ Y` is a representable 1-morphism of categories over `C`, with `Y`
fibred in groupoids, then for every object `y` of `Y` the comma category `CostructuredArrow F y`
has a terminal object: the representing object of the hom-presheaf `x ↦ Hom(F x, y)`, which is
the second component of a terminal object of the 2-fibre product `(C/U) ×_Y X` along a
classifying functor of `y`. Unlike
`AlgebraicGeometry.BigFppfOver.isRepresentableMorphism_iff_forall_isRepresentable` this asks
nothing of the hom universes, so it applies to the categories fibred in groupoids of algebraic
stacks. -/
theorem _root_.Stacks.RepresentableMorphism.exists_isTerminal_costructuredArrow
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] {Y : Type u₃}
    [Category.{v₃} Y] {p : X ⥤ C} {q : Y ⥤ C} {F : X ⥤ Y} (hF : F ⋙ q = p)
    (hq : q.IsFiberedInGroupoids)
    (hr : Stacks.RepresentableMorphism.IsRepresentableMorphism p q F) (y : Y) :
    ∃ t : CostructuredArrow F y, Nonempty (Limits.IsTerminal t) := by
  obtain ⟨x, ⟨R⟩⟩ := isRepresentable_of_isRepresentableMorphism hF hq hr y
  have hR {a : X} (b : a ⟶ x) : R.homEquiv b = F.map b ≫ R.homEquiv (𝟙 x) := R.homEquiv_eq b
  refine ⟨CostructuredArrow.mk (Y := x) (R.homEquiv (𝟙 x)),
    ⟨Limits.IsTerminal.ofUniqueHom (fun c => CostructuredArrow.homMk
      (R.homEquiv.symm c.hom) ?_) (fun c m => ?_)⟩⟩
  · change F.map (R.homEquiv.symm c.hom) ≫ R.homEquiv (𝟙 x) = c.hom
    rw [← hR, Equiv.apply_symm_apply]
  · refine CostructuredArrow.hom_ext _ _ ?_
    change m.left = R.homEquiv.symm c.hom
    rw [Equiv.eq_symm_apply, hR]
    exact CostructuredArrow.w m

end AlgebraicGeometry.BigFppfOver

end
