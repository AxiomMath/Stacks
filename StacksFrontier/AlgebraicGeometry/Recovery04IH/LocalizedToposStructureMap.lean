module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforwardBeckChevalley
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The structure map of Stacks 04IF's localized morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of sets
on `D` and put `F = f⁻¹G`.  [Stacks Project, Tag 04IF] localizes `(f, f♯)` to
`(f', (f')♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)` and records the commutativity of the
localization square twice: on inverse images, as
`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso`, and on direct images, as
`AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso`.  This file proves that the two
are **Beck–Chevalley mates**, in the element form that determines them.

Both squares are built by transporting Stacks 04H1's two squares across the identifications of
the two localizations with their slice topoi, so the content of the identity sits at the slice
level and is
`MorphismOfTopoi.homEquiv_inverseImageCompToOverIso_inv_app_comp`; what is proved here is the
transport.

## Main results

* `Stacks.CategoryTheory.homEquiv_beckChevalley_transport`: the transport of a Beck–Chevalley
  identity across two equivalences, in the shape that Stacks 04IF's two squares have.
* `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_inv_app'` and
  `.localizationCompPushforwardIso_hom_app`: the components of the two squares.  The primed
  name is this file's own reading of the first component; the unprimed
  `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_inv_app` of
  `StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizationSquareMate.lean` states the
  same identity with the three inverse-image factors kept apart, over two independent object
  universes.
* `AlgebraicGeometry.RingedToposHom.homEquiv_inverseImageCompLocalizationIso_inv_app`: **the
  Beck–Chevalley identity for Stacks 04IF's two squares**, in the element form that determines
  them.
* `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_hom_app_comp_homEquiv_symm`:
  its element-level consequence, that the inverse-image square followed by the adjunct of a
  restricted morphism is the restriction of its adjunct.
* The structure map of the localized morphism on underlying sheaves of sets is
  `AlgebraicGeometry.RingedToposHom.localized_fSharp_forget` of
  `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean`,
  which states that identity over two independent object universes and so applies here; this
  file states only the unfolding `AlgebraicGeometry.RingedToposHom.localized_fSharp_eq'` of the
  structure map into its four factors that the forgetful computation runs on.

**Stacks 04IF's structure-map identity** — the inverse-image form of `(f')♯`, read through 04IF's
inverse-image square, is the restriction `j_F⁻¹` of the inverse-image form of `f♯` — is *not*
stated here.  It is `AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean`,
which carries `@[stacks 04IF]` and holds over two independent object universes.

## Implementation notes

The transport is clean for one reason: the identification `λ_F` of `j_F⁻¹ ⋙ Φ_F` with `toOver F`
enters the inverse-image square as its inverse and the direct-image square as itself, so in the
composite it cancels outright; and `λ_G` enters only through its naturality at the unit of
`f⁻¹ ⊣ f_*`.  Nothing about either identification beyond those two facts is used, which is what
makes the argument independent of the opaque
`AlgebraicGeometry.RingedTopos.localizationEquivalence`.

Both component lemmas are proved by `rfl` against the definitions and then regrouped.  The
`rfl` is instant — but **only if every object argument is spelled the way the definition spells
it**: writing `j_F⁻¹.obj (f⁻¹.obj Z)` where the definition produces `(f⁻¹ ⋙ j_F⁻¹).obj Z`
exhausts the 200,000-heartbeat `isDefEq` budget, while the two are equal by `rfl`.  The regrouping
is then done by the generic `Stacks.CategoryTheory.map_comp_three_left` and `_right`, applied by
`exact`, so the spelling is converted once, at default transparency.

For the same reason the Beck–Chevalley identity takes the two squares and their components as
*hypotheses* of a generic lemma rather than rewriting with the component lemmas in place: `rw`
with either component lemma underneath `(f')⁻¹ ⊣ f'_*`'s hom-set bijection also exhausts the
heartbeat budget, whereas passing them as arguments to a lemma whose statement is in terms of
variables costs nothing.

**The `forgetRing` bookkeeping obeys the same rule, and more sharply.**  Deciding that the two
iterated transports of the ring operations appearing in
`AlgebraicGeometry.RingedToposHom.localizedPushforwardCommRingIso` have the same underlying
sheaf of sets is, at the geometric instantiation, beyond the heartbeat budget — `rw` with any of
the three factor computations dies, and so does the `𝟙` of a statement that needs that object
twice.  The whole three-factor computation is therefore done once in
`Stacks.Sheaves.ToposPullback.forget_map_transportCompIso_inv_app`, where every functor is a
variable and the same defeq is immediate; instantiating an already-proved statement costs
nothing.  For the same reason the two one-step computations are stated with the **morphism of
topoi** as their explicit argument
(`Stacks.Sheaves.ToposPushforward.forget_map_pushforwardCommRingFunctor_map` and its
inverse-image sibling) rather than with the transporting functor of sheaves of sets.

## References

* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-- The hom-set bijection of a composite of three adjunctions. -/
theorem homEquiv_comp_comp {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (W : A) (Z : D)
    (x : L₃.obj (L₂.obj (L₁.obj W)) ⟶ Z) :
    (((adj₁.comp adj₂).comp adj₃).homEquiv W Z) x =
      (adj₁.homEquiv W _) ((adj₂.homEquiv _ _) ((adj₃.homEquiv _ Z) x)) := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- Three factors of a functor's image, left-nested, with a trailing identity removed. -/
theorem map_comp_three_left {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {a b c d : C} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) {T : D} (w : F.obj d ⟶ T) :
    (((F.map x ≫ F.map y) ≫ F.map z) ≫ w) ≫ 𝟙 T = F.map (x ≫ y ≫ z) ≫ w := by
  rw [Category.comp_id, ← F.map_comp, ← F.map_comp, Category.assoc]

/-- Three factors of a functor's image, right-nested, with a trailing identity removed. -/
theorem map_comp_three_right {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D]
    (F : C ⥤ D) {a b c d : C} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) {T : D} (w : F.obj d ⟶ T) :
    F.map x ≫ F.map y ≫ F.map z ≫ w ≫ 𝟙 T = F.map (x ≫ y ≫ z) ≫ w := by
  rw [Category.comp_id, F.map_comp, F.map_comp]
  simp only [Category.assoc]

/-- Two images of a functor, each flanked by one further morphism, merged into one. -/
theorem comp_map_comp_map_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : D ⥤ C) {A B : C} {P Q R : D} (u : A ⟶ F.obj P) (x : P ⟶ Q) (y : Q ⟶ R)
    (v : F.obj R ⟶ B) :
    (u ≫ F.map x) ≫ F.map y ≫ v = u ≫ F.map (x ≫ y) ≫ v := by
  rw [Category.assoc, ← Category.assoc (F.map x) (F.map y), ← F.map_comp]

/-- Conjugating the image of a morphism under an equivalence's functor by the two components of
the equivalence's unit recovers the morphism. -/
theorem unitIso_hom_comp_map_map_comp_unitIso_inv {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (E : C ≌ D) {A B : C} (g : A ⟶ B) :
    E.unitIso.hom.app A ≫ E.inverse.map (E.functor.map g) ≫ E.unitIso.inv.app B = g := by
  have h := E.unit_naturality g
  rw [← Category.assoc]
  refine Eq.trans (congrArg (fun z ↦ z ≫ E.unitIso.inv.app B) h) ?_
  rw [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id g

/-- A functor's image of a left-nested composite of three morphisms. -/
theorem map_comp_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B E T : C} (x : A ⟶ B) (y : B ⟶ E) (z : E ⟶ T) :
    F.map ((x ≫ y) ≫ z) = (F.map x ≫ F.map y) ≫ F.map z := by
  rw [F.map_comp, F.map_comp]

/-- A functor's image of a right-nested composite of four morphisms. -/
theorem map_comp_four' {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B E T S : C} (w : A ⟶ B) (x : B ⟶ E) (y : E ⟶ T) (z : T ⟶ S) :
    F.map (w ≫ x ≫ y ≫ z) = F.map w ≫ F.map x ≫ F.map y ≫ F.map z := by
  rw [F.map_comp, F.map_comp, F.map_comp]

/-- A right-nested composite of four morphisms, each rewritten. -/
theorem comp_congr₄ {C : Type u₁} [Category.{v₁} C] {A B E T S : C} {w w' : A ⟶ B}
    {x x' : B ⟶ E} {y y' : E ⟶ T} {z z' : T ⟶ S} (hw : w = w') (hx : x = x') (hy : y = y')
    (hz : z = z') : w ≫ x ≫ y ≫ z = w' ≫ x' ≫ y' ≫ z' := by
  rw [hw, hx, hy, hz]

/-- A left-nested composite of three morphisms, with the outer two rewritten.  Stated so that
it is applied by `exact`, which needs no pattern search: `rw` with either of the two equations
here compares the pattern against the *other* two factors, and that comparison is what exhausts
the heartbeat budget. -/
theorem comp_comp_congr₂ {C : Type u₁} [Category.{v₁} C] {A B E T : C} {x x' : A ⟶ B}
    {z z' : E ⟶ T} (y : B ⟶ E) (hx : x = x') (hz : z = z') : (x ≫ y) ≫ z = (x' ≫ y) ≫ z' := by
  rw [hx, hz]

/-- From `p ≫ i.hom.app W = q` conclude `q ≫ i.inv.app W = p`. -/
theorem comp_inv_app_of_comp_hom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (i : F ≅ G) {A : D} {W : C} {p : A ⟶ F.obj W}
    {q : A ⟶ G.obj W} (h : p ≫ i.hom.app W = q) : q ≫ i.inv.app W = p := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- A functor's image of the backward direction of an isomorphism, read off a one-sided inverse
of the image of its forward direction. -/
theorem map_inv_eq_of_comp_eq_id {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B : C} (i : A ≅ B) {n : F.obj B ⟶ F.obj A}
    (h : F.map i.hom ≫ n = 𝟙 (F.obj A)) : F.map i.inv = n := by
  exact (cancel_epi (F.map i.hom)).1 ((i.hom_inv_id_map F).trans h.symm)

/-- **The element-level form of a Beck–Chevalley unit identity.**

Given a square of functors `jF`, `jG` over an adjunction `a : phiI ⊣ phiS` and an adjunction
`d : Lp ⊣ Rp`, with comparisons `nu : phiI ⋙ jF ≅ jG ⋙ Lp` and `th : jF ⋙ Rp ≅ phiS ⋙ jG`
satisfying the unit identity `hU`, the inverse-image comparison followed by the adjunct of a
restricted morphism is the restriction of that morphism.

This is pure adjunction naturality: the unit identity is the whole content. -/
theorem homEquiv_symm_comp_of_unit {AT : Type u₁} [Category.{v₁} AT] {BT : Type u₂}
    [Category.{v₂} BT] {CX : Type u₃} [Category.{v₃} CX] {CY : Type u₄} [Category.{v₄} CY]
    {phiI : BT ⥤ AT} {phiS : AT ⥤ BT} (a : phiI ⊣ phiS)
    {Lp : CY ⥤ CX} {Rp : CX ⥤ CY} (d : Lp ⊣ Rp)
    {jF : AT ⥤ CX} {jG : BT ⥤ CY}
    (nu : phiI ⋙ jF ≅ jG ⋙ Lp) (th : jF ⋙ Rp ≅ phiS ⋙ jG)
    (hU : ∀ Z : BT, jG.map (a.unit.app Z) ≫ th.inv.app (phiI.obj Z) =
      (d.homEquiv (jG.obj Z) (jF.obj (phiI.obj Z))) (nu.inv.app Z))
    (H : BT) (K : AT) (g : phiI.obj H ⟶ K) :
    nu.hom.app H ≫ ((d.homEquiv (jG.obj H) (jF.obj K)).symm
        (jG.map ((a.homEquiv H K) g) ≫ th.inv.app K)) = jF.map g := by
  have hnat : jG.map (phiS.map g) ≫ th.inv.app K =
      th.inv.app (phiI.obj H) ≫ Rp.map (jF.map g) := th.inv.naturality g
  have key : jG.map ((a.homEquiv H K) g) ≫ th.inv.app K =
      (d.homEquiv (jG.obj H) (jF.obj K)) (nu.inv.app H ≫ jF.map g) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
      hU H, Adjunction.homEquiv_naturality_right]
    rfl
  rw [key, Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The transport of a Beck–Chevalley identity across two equivalences.**

This is the shape of Stacks 04IF's two squares: a morphism `f` of topoi with adjunction `a`, a
slice-level adjunction `e`, two further functors `jF`, `jG` whose composites with the
equivalences are identified with `toF`, `toG` by `lF`, `lG`, and the two slice-level squares
`ii` and `pp`.  Given the slice-level Beck–Chevalley identity `hS`, the transported squares
satisfy the corresponding identity.

The transport is clean because `lF` cancels outright — it enters the inverse-image square as its
inverse and the direct-image square as itself — and `lG` enters only through its naturality. -/
theorem homEquiv_beckChevalley_transport {AT : Type u₁} [Category.{v₁} AT] {BT : Type u₂}
    [Category.{v₂} BT] {CX : Type u₃} [Category.{v₃} CX] {CY : Type u₄} [Category.{v₄} CY]
    {OF : Type u₅} [Category.{v₅} OF] {OG : Type u₆} [Category.{v₆} OG]
    (EX : CX ≌ OF) (EY : CY ≌ OG)
    {phiI : BT ⥤ AT} {phiS : AT ⥤ BT} (a : phiI ⊣ phiS)
    {P : OG ⥤ OF} {Q : OF ⥤ OG} (e : P ⊣ Q)
    {jF : AT ⥤ CX} {jG : BT ⥤ CY} {toF : AT ⥤ OF} {toG : BT ⥤ OG}
    (lF : jF ⋙ EX.functor ≅ toF) (lG : jG ⋙ EY.functor ≅ toG)
    (ii : phiI ⋙ toF ≅ toG ⋙ P) (pp : toF ⋙ Q ≅ phiS ⋙ toG)
    (nu : phiI ⋙ jF ≅ jG ⋙ (EY.functor ⋙ P ⋙ EX.inverse))
    (th : jF ⋙ (EX.functor ⋙ Q ⋙ EY.inverse) ≅ phiS ⋙ jG)
    (hnu : ∀ Z : BT, nu.inv.app Z =
      EX.inverse.map (P.map (lG.hom.app Z) ≫ ii.inv.app Z ≫ lF.inv.app (phiI.obj Z)) ≫
        EX.unitIso.inv.app (jF.obj (phiI.obj Z)))
    (hth : ∀ W : AT, th.hom.app W =
      EY.inverse.map (Q.map (lF.hom.app W) ≫ pp.hom.app W ≫ lG.inv.app (phiS.obj W)) ≫
        EY.unitIso.inv.app (jG.obj (phiS.obj W)))
    (hS : ∀ Z : BT, (e.homEquiv (toG.obj Z) (toF.obj (phiI.obj Z))) (ii.inv.app Z) ≫
        pp.hom.app (phiI.obj Z) = toG.map (a.unit.app Z))
    (Z : BT) :
    (((EY.toAdjunction.comp e).comp EX.symm.toAdjunction).homEquiv (jG.obj Z)
          (jF.obj (phiI.obj Z))) (nu.inv.app Z) ≫ th.hom.app (phiI.obj Z) =
      jG.map (a.unit.app Z) := by
  rw [hnu Z, hth (phiI.obj Z)]
  have hEX : ∀ (A : OF) (B : CX) (m : A ⟶ EX.functor.obj B),
      (EX.symm.toAdjunction.homEquiv A B) (EX.inverse.map m ≫ EX.unitIso.inv.app B) = m := by
    intro A B m
    refine (Equiv.eq_symm_apply _).mp ?_
    rw [Adjunction.homEquiv_counit]
    rfl
  have hQ : Q.map (lF.inv.app (phiI.obj Z)) ≫ Q.map (lF.hom.app (phiI.obj Z)) =
      𝟙 (Q.obj (toF.obj (phiI.obj Z))) :=
    (lF.app (phiI.obj Z)).inv_hom_id_map Q
  have hnat : EY.functor.map (jG.map (a.unit.app Z)) ≫
        lG.hom.app (phiS.obj (phiI.obj Z)) =
      lG.hom.app Z ≫ toG.map (a.unit.app Z) :=
    lG.hom.naturality (a.unit.app Z)
  have hin : (lG.hom.app Z ≫
        (e.homEquiv (toG.obj Z) (toF.obj (phiI.obj Z))) (ii.inv.app Z) ≫
          Q.map (lF.inv.app (phiI.obj Z))) ≫
      (Q.map (lF.hom.app (phiI.obj Z)) ≫ pp.hom.app (phiI.obj Z) ≫
        lG.inv.app (phiS.obj (phiI.obj Z))) =
      EY.functor.map (jG.map (a.unit.app Z)) := by
    simp only [Category.assoc]
    rw [← Category.assoc (Q.map (lF.inv.app (phiI.obj Z))), hQ, Category.id_comp,
      ← Category.assoc ((e.homEquiv (toG.obj Z) (toF.obj (phiI.obj Z))) (ii.inv.app Z)),
      hS Z, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [homEquiv_comp_comp, hEX, e.homEquiv_naturality_left, e.homEquiv_naturality_right,
    Adjunction.homEquiv_unit]
  refine Eq.trans (comp_map_comp_map_comp EY.inverse (EY.toAdjunction.unit.app (jG.obj Z))
    (lG.hom.app Z ≫ (e.homEquiv (toG.obj Z) (toF.obj (phiI.obj Z))) (ii.inv.app Z) ≫
      Q.map (lF.inv.app (phiI.obj Z)))
    (Q.map (lF.hom.app (phiI.obj Z)) ≫ pp.hom.app (phiI.obj Z) ≫
      lG.inv.app (phiS.obj (phiI.obj Z)))
    (EY.unitIso.inv.app (jG.obj (phiS.obj (phiI.obj Z))))) ?_
  refine Eq.trans (congrArg (fun z ↦ EY.toAdjunction.unit.app (jG.obj Z) ≫ EY.inverse.map z ≫
    EY.unitIso.inv.app (jG.obj (phiS.obj (phiI.obj Z)))) hin) ?_
  exact unitIso_hom_comp_map_map_comp_unitIso_inv EY (jG.map (a.unit.app Z))

end Stacks.CategoryTheory

namespace Stacks.Sheaves.ToposPushforward

universe ww vv uu vv' uu' vvv uuu vvvv uuuu

section OneStep

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww})]
  (g : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))

/-- On underlying sheaves of sets, the inverse image along a morphism of topoi of a morphism of
sheaves of commutative rings is the inverse image of the underlying map of sheaves of sets.

Stated with the morphism of topoi as the explicit argument — rather than with the transporting
functor of sheaves of sets — so that the application matches structurally. -/
theorem forget_map_inverseImageCommRingFunctor_map {O O' : Sheaf K CommRingCat.{ww}}
    (a : O ⟶ O') :
    (sheafCompose J (forget CommRingCat.{ww})).map ((inverseImageCommRingFunctor g).map a) =
      g.inverseImage.map ((sheafCompose K (forget CommRingCat.{ww})).map a) :=
  underlyingRingSheaf_map_pullbackCommRingSheafMap J _ a

/-- On underlying sheaves of sets, the direct image along a morphism of topoi of a morphism of
sheaves of commutative rings is the direct image of the underlying map of sheaves of sets.

Stated with the morphism of topoi as the explicit argument.  That matters: at
`g = f.localizedToposMorphism G` the form of
`Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap` with the
transporting functor of sheaves of sets supplied instead — named implicitly, explicitly, or
inferred — exhausts the 200,000-heartbeat `whnf` budget, because the functor has then to be
recognised inside `pushforwardCommRingFunctor`, instance arguments and all. -/
theorem forget_map_pushforwardCommRingFunctor_map {O O' : Sheaf J CommRingCat.{ww}}
    (a : O ⟶ O') :
    (sheafCompose K (forget CommRingCat.{ww})).map ((pushforwardCommRingFunctor g).map a) =
      g.pushforward.map ((sheafCompose J (forget CommRingCat.{ww})).map a) :=
  underlyingRingSheaf_map_pullbackCommRingSheafMap K _ a

end OneStep

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu' vvv uuu vvvv uuuu

section Transport

variable {C₁ : Type uu} [Category.{vv} C₁] {C₁' : Type uuu} [Category.{vvv} C₁']
  {C₂ : Type uu'} [Category.{vv'} C₂] {D : Type uuuu} [Category.{vvvv} D]
  (J₁ : GrothendieckTopology C₁) (J₁' : GrothendieckTopology C₁')
  (J₂ : GrothendieckTopology C₂) {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₁'.HasSheafCompose (forget RingCat.{ww})]
  [J₂.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₁'.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]
  (Ψ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁' (Type ww)) [PreservesFiniteProducts Ψ₁]
  (Ψ₂ : Sheaf J₁' (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Ψ₂]

omit [J₂.HasSheafCompose (forget RingCat)] [J₁.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison of the iterated with the one-step transport of the ring operations is the
identity on underlying sheaves of sets, in the backward direction. -/
theorem forget_map_pullbackCommRingSheafComp_inv' (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).inv =
      𝟙 ((sheafCompose J₂ (forget CommRingCat.{ww})).obj
        (pullbackCommRingSheaf J₂ Φ₂ (pullbackCommRingSheaf J₁ Φ₁ O))) := by
  exact Stacks.CategoryTheory.map_inv_eq_of_comp_eq_id _ _
    (by rw [forget_map_pullbackCommRingSheafComp_hom]; exact Category.id_comp _)

/-- **The underlying sheaf-of-sets comparison of a transported ring-level comparison.**

Transporting the ring operations along a natural isomorphism `e : Φ₁ ⋙ Φ₂ ≅ Ψ₁ ⋙ Ψ₂` of
finite-product-preserving functors, and composing with the two comparisons of the iterated with
the one-step transport, gives an isomorphism of the two iterated transports whose underlying map
of sheaves of sets is `e` itself.

This is the shape of `AlgebraicGeometry.RingedToposHom.localizedPushforwardCommRingIso`.  It is
stated here, with every functor a variable, because at the geometric instantiation deciding that
the two iterated transports have the same underlying sheaf of sets is far beyond the heartbeat
budget, while in a generic context it is immediate — and applying an already-proved statement
costs nothing. -/
theorem forget_map_transportCompIso_inv_app (e : Φ₁ ⋙ Φ₂ ≅ Ψ₁ ⋙ Ψ₂)
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorComp J₁ J₂ Φ₁ Φ₂ ≪≫
          pullbackCommRingSheafFunctorIsoOfNatIso J₂ e ≪≫
          (pullbackCommRingSheafFunctorComp J₁' J₂ Ψ₁ Ψ₂).symm).inv.app O) =
      e.inv.app ((sheafCompose K (forget CommRingCat.{ww})).obj O) := by
  have hraw : ((pullbackCommRingSheafFunctorComp J₁ J₂ Φ₁ Φ₂ ≪≫
        pullbackCommRingSheafFunctorIsoOfNatIso J₂ e ≪≫
        (pullbackCommRingSheafFunctorComp J₁' J₂ Ψ₁ Ψ₂).symm).inv.app O) =
      ((pullbackCommRingSheafComp J₁' J₂ Ψ₁ Ψ₂ O).hom ≫
          pullbackCommRingSheafMapOfNatTrans J₂ e.inv O) ≫
        (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).inv := rfl
  refine Eq.trans (congrArg (sheafCompose J₂ (forget CommRingCat.{ww})).map hraw) ?_
  refine Eq.trans (Stacks.CategoryTheory.map_comp_comp
    (sheafCompose J₂ (forget CommRingCat.{ww})) _ _ _) ?_
  refine Eq.trans (Stacks.CategoryTheory.comp_comp_congr₂ _
    (forget_map_pullbackCommRingSheafComp_hom J₁' J₂ Ψ₁ Ψ₂ O)
    (forget_map_pullbackCommRingSheafComp_inv' J₁ J₂ Φ₁ Φ₂ O)) ?_
  refine Eq.trans (Category.comp_id _) ?_
  exact (Category.id_comp _).trans (pullbackCommRingSheafMapOfNatTrans_forget J₂ e.inv O)

end Transport

end Stacks.Sheaves.ToposPullback

universe v u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable {X Y : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C]
  (f : RingedToposHom X Y) (G : Y.Topos)

/-- The component of Stacks 04IF's inverse-image square, read through the two identifications
with the slice topoi. -/
theorem inverseImageCompLocalizationIso_inv_app' (Z : Y.Topos) :
    (f.inverseImageCompLocalizationIso G).inv.app Z =
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
          ((f.toToposHom.over G).inverseImage.map
              ((Y.localizationInverseImageIso G).hom.app Z) ≫
            (f.toToposHom.inverseImageCompToOverIso G).inv.app Z ≫
              (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).inv.app
                (f.toToposHom.inverseImage.obj Z)) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.inv.app
          ((f.toToposHom.inverseImage ⋙
              (X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage).obj Z) := by
  have hraw : (f.inverseImageCompLocalizationIso G).inv.app Z =
      ((((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
                  ((f.toToposHom.over G).inverseImage.map
                    ((Y.localizationInverseImageIso G).hom.app Z)) ≫
                (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
                  ((f.toToposHom.inverseImageCompToOverIso G).inv.app Z)) ≫
              (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
                ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).inv.app
                  (f.toToposHom.inverseImage.obj Z))) ≫
            (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.inv.app
              ((f.toToposHom.inverseImage ⋙
                  (X.localizationMorphism
                    (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage).obj Z)) ≫
        𝟙 ((f.toToposHom.inverseImage ⋙
              (X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage).obj Z) := rfl
  exact hraw.trans (Stacks.CategoryTheory.map_comp_three_left _ _ _ _ _)

/-- The component of Stacks 04IF's direct-image square, read through the two identifications
with the slice topoi. -/
theorem localizationCompPushforwardIso_hom_app (W : X.Topos) :
    (f.localizationCompPushforwardIso G).hom.app W =
      (Y.localizationEquivalence G).inverse.map
          ((f.toToposHom.over G).pushforward.map
              ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app W) ≫
            (f.toToposHom.toOverCompPushforwardIso G).hom.app W ≫
              (Y.localizationInverseImageIso G).inv.app (f.toToposHom.pushforward.obj W)) ≫
        (Y.localizationEquivalence G).unitIso.inv.app
          ((f.toToposHom.pushforward ⋙
              (Y.localizationMorphism G).toToposHom.inverseImage).obj W) := by
  have hraw : (f.localizationCompPushforwardIso G).hom.app W =
      (Y.localizationEquivalence G).inverse.map
          ((f.toToposHom.over G).pushforward.map
            ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app W)) ≫
        (Y.localizationEquivalence G).inverse.map
            ((f.toToposHom.toOverCompPushforwardIso G).hom.app W) ≫
          (Y.localizationEquivalence G).inverse.map
              ((Y.localizationInverseImageIso G).inv.app (f.toToposHom.pushforward.obj W)) ≫
            (Y.localizationEquivalence G).unitIso.inv.app
                ((f.toToposHom.pushforward ⋙
                    (Y.localizationMorphism G).toToposHom.inverseImage).obj W) ≫
              𝟙 ((f.toToposHom.pushforward ⋙
                    (Y.localizationMorphism G).toToposHom.inverseImage).obj W) := rfl
  exact hraw.trans (Stacks.CategoryTheory.map_comp_three_right _ _ _ _ _)

/-- **The two squares of Stacks 04IF are Beck–Chevalley mates**, in the element form that
determines them: the adjunct of the inverse-image square undone, followed by the direct-image
square, is `j_G⁻¹` of the unit of `f⁻¹ ⊣ f_*`. -/
theorem homEquiv_inverseImageCompLocalizationIso_inv_app (Z : Y.Topos) :
    ((f.localizedToposMorphism G).adj.homEquiv
        ((Y.localizationMorphism G).toToposHom.inverseImage.obj Z)
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
          (f.toToposHom.inverseImage.obj Z)))
      ((f.inverseImageCompLocalizationIso G).inv.app Z) ≫
        (f.localizationCompPushforwardIso G).hom.app (f.toToposHom.inverseImage.obj Z) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (f.toToposHom.adj.unit.app Z) :=
  Stacks.CategoryTheory.homEquiv_beckChevalley_transport
    (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)) (Y.localizationEquivalence G)
    f.toToposHom.adj (f.toToposHom.over G).adj
    (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G))
    (Y.localizationInverseImageIso G) (f.toToposHom.inverseImageCompToOverIso G)
    (f.toToposHom.toOverCompPushforwardIso G) (f.inverseImageCompLocalizationIso G)
    (f.localizationCompPushforwardIso G) (inverseImageCompLocalizationIso_inv_app' f G)
    (localizationCompPushforwardIso_hom_app f G)
    (MorphismOfTopoi.homEquiv_inverseImageCompToOverIso_inv_app_comp f.toToposHom G) Z

/-- **The Beck–Chevalley identity, read against the direct-image square.** -/
theorem inverseImageCompLocalizationIso_inv_app_homEquiv (Z : Y.Topos) :
    (Y.localizationMorphism G).toToposHom.inverseImage.map (f.toToposHom.adj.unit.app Z) ≫
        (f.localizationCompPushforwardIso G).inv.app (f.toToposHom.inverseImage.obj Z) =
      ((f.localizedToposMorphism G).adj.homEquiv
          ((Y.localizationMorphism G).toToposHom.inverseImage.obj Z)
          ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
            (f.toToposHom.inverseImage.obj Z)))
        ((f.inverseImageCompLocalizationIso G).inv.app Z) :=
  Stacks.CategoryTheory.comp_inv_app_of_comp_hom_app (f.localizationCompPushforwardIso G)
    (homEquiv_inverseImageCompLocalizationIso_inv_app f G Z)

/-- **The structure-map identity of Stacks 04IF, in adjunct form**: the inverse-image square
followed by the adjunct of a restricted morphism is the restriction of its adjunct. -/
theorem inverseImageCompLocalizationIso_hom_app_comp_homEquiv_symm (H : Y.Topos) (K : X.Topos)
    (g : f.toToposHom.inverseImage.obj H ⟶ K) :
    (f.inverseImageCompLocalizationIso G).hom.app H ≫
        ((f.localizedToposMorphism G).adj.homEquiv
            ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)
            ((X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K)).symm
          ((Y.localizationMorphism G).toToposHom.inverseImage.map
              ((f.toToposHom.adj.homEquiv H K) g) ≫
            (f.localizationCompPushforwardIso G).inv.app K) =
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map g :=
  Stacks.CategoryTheory.homEquiv_symm_comp_of_unit f.toToposHom.adj
    (f.localizedToposMorphism G).adj (f.inverseImageCompLocalizationIso G)
    (f.localizationCompPushforwardIso G)
    (inverseImageCompLocalizationIso_inv_app_homEquiv f G) H K g

/-- On underlying sheaves of sets, the comparison of the two direct images of sheaves of
commutative rings in Stacks 04IF is the comparison of sheaves of sets.

This is the generic `Stacks.Sheaves.ToposPullback.forget_map_transportCompIso_inv_app`
instantiated, which is what makes it affordable. -/
theorem localizedPushforwardCommRingIso_inv_app_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((localizedPushforwardCommRingIso f G).inv.app X.O) =
      (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) :=
  forget_map_transportCompIso_inv_app
    (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J Y.J
    (Y.localizedRingedTopos G).J
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
    (f.localizedToposMorphism G).pushforward f.toToposHom.pushforward
    (Y.localizationMorphism G).toToposHom.inverseImage
    (f.localizationCompPushforwardIso G) X.O

/-- The structure map of Stacks 04IF's localized morphism, unfolded into its four factors. -/
theorem localized_fSharp_eq' :
    (f.localized G).fSharp =
      (Y.localizationInverseImageCommRingIso G).inv ≫
        (inverseImageCommRingFunctor (Y.localizationMorphism G).toToposHom).map f.fSharp ≫
          (localizedPushforwardCommRingIso f G).inv.app X.O ≫
            (pushforwardCommRingFunctor (f.localizedToposMorphism G)).map
              (X.localizationInverseImageCommRingIso
                (f.toToposHom.inverseImage.obj G)).hom := rfl

end AlgebraicGeometry.RingedToposHom

end
