module

public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages

/-!
# The étale-local criterion for the base change map of sheaves of sets

Consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

and let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S` with
`Vᵢ → S` étale.  Writing `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, the induced squares

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

are again cartesian.  This file sets up the statement of the first part of Stacks 0EZR for
sheaves of sets: the data of the diagram, the base change map
`f^{-1} g_* F ⟶ h_* e^{-1} F` whose invertibility part (1) concludes, and the two steps of the
source's argument that are carried out here — the locality of invertibility on the small étale
site, and the identification of the two composite direct images around a commutative square.

## Main definitions

* `Stacks.EtaleCohomology.EtaleLocalBaseChangeData` — the data of Stacks 0EZR: the cartesian
  square, the étale covering, the factorizations through the `Vᵢ`, the induced cartesian squares
  and the sheaf.
* `Stacks.EtaleCohomology.smallEtaleSetsAdjunction` — the inverse-image/direct-image adjunction
  for sheaves of sets on the small étale sites.
* `Stacks.EtaleCohomology.smallEtaleSetsRestrictionAdjunction` — restriction along an étale
  morphism is left adjoint to the direct image.
* `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` — the base change map
  `g^{-1} f_* ⟶ f'_* (g')^{-1}` for sheaves of sets on the small étale sites of a commutative
  square of schemes: the mate of the identification of the two composite direct images.

## Implementation notes

The base change map is the mate, under the two inverse-image/direct-image adjunctions, of the
comparison of the two composite direct images around the square, so no choice enters beyond the
commutativity of the square itself.  The abelian analogue already in the library is
`Stacks.EtaleCohomology.etaleAbelianBaseChange`; sheaves of sets are the coefficients in which
the source states part (1), and the adjunction is available for them because inverse image is a
left Kan extension along base change followed by sheafification.

The source's argument compares the restriction to `Uᵢ` of the base change map of the outer square
with the base change map of the `i`-th local square through the pasting law for mates: the
rectangle `Uᵢ ⟶ X ⟶ S` obtained by stacking the outer square on the `i`-th upper square is the
one obtained by stacking the `i`-th local square on the `i`-th lower square, because
`Uᵢ → X → S` equals `Uᵢ → Vᵢ → S`.  Two of the four base change maps occurring in that
comparison are invertible for free, being attached to cartesian squares one side of which is
étale; that is the appeal to Sites, Lemma 03EF in the source.  The mate calculus the comparison
needs is assembled in the `Mates` section below, including
`mate_sheafPushforward_app`, which computes the mate of a 2-square of sheaf pushforwards
sectionwise from the mate of the underlying 2-square of site functors; the comparison of the two
composite base change functors of sites is `siteSquare`, and of the two composite direct images
is `rightSquare`.

Coefficients are `Type (max (u + 1) v)` for a scheme universe `u` and arbitrary `v`, matching
`Stacks.EtaleCohomology.smallEtaleInverseImage` and
`Stacks.EtaleCohomology.smallEtaleDirectImage`.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v z

namespace Stacks.EtaleCohomology

/-! ### Abstract lemmas on mates -/

section Mates

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- Invertibility of a component of a mate is unchanged by replacing the two right adjoints by
isomorphic ones, provided the two 2-squares correspond under those isomorphisms. -/
private lemma isIso_mate_symm_iff
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁')
    (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
    {G : A ⥤ C} {H : B ⥤ D}
    (s : TwoSquare R₁ H G R₂) (s' : TwoSquare R₁' H G R₂')
    (r₁ : R₁ ≅ R₁') (r₂ : R₂ ≅ R₂')
    (hs : s.whiskerBottom r₂.hom = s'.whiskerTop r₁.hom) (X : A) :
    IsIso (((mateEquiv a₁ a₂).symm s).app X) ↔
      IsIso (((mateEquiv a₁' a₂').symm s').app X) := by
  let l₁ := (conjugateIsoEquiv a₁ a₁').symm r₁
  let l₂ := (conjugateIsoEquiv a₂ a₂').symm r₂
  have hl₁ : conjugateEquiv a₁ a₁' l₁.hom = r₁.hom :=
    (conjugateEquiv a₁ a₁').apply_symm_apply _
  have hl₂ : conjugateEquiv a₂ a₂' l₂.hom = r₂.hom :=
    (conjugateEquiv a₂ a₂').apply_symm_apply _
  have he : ((mateEquiv a₁ a₂).symm s).whiskerRight l₂.hom =
      ((mateEquiv a₁' a₂').symm s').whiskerLeft l₁.hom := by
    apply (mateEquiv a₁ a₂').injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hl₁, hl₂, hs]
  have hx := congrArg (fun t => t.app X) he
  change l₂.hom.app (G.obj X) ≫ _ = _ ≫ H.map (l₁.hom.app X) at hx
  rw [← isIso_comp_left_iff (l₂.hom.app (G.obj X)), hx, isIso_comp_right_iff]

/-- The mate of a horizontal composite of 2-squares is the vertical composite of the mates. -/
private lemma mate_symm_hcomp
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : B ⥤ E} {R₃ : E ⥤ B} {L₄ : D ⥤ F} {R₄ : F ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G : A ⥤ C} {H : B ⥤ D} {K : E ⥤ F}
    (s : TwoSquare R₁ H G R₂) (t : TwoSquare R₃ K H R₄) :
    (mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (t.hComp s) =
      ((mateEquiv a₁ a₂).symm s).vComp ((mateEquiv a₃ a₄).symm t) := by
  apply (mateEquiv (a₁.comp a₃) (a₂.comp a₄)).injective
  rw [Equiv.apply_symm_apply, mateEquiv_hcomp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The component of a mate, written out in terms of the unit and the counit. -/
private lemma mate_symm_app_eq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : A ⥤ C} {H : B ⥤ D}
    (s : TwoSquare R₁ H G R₂) (X : A) :
    ((mateEquiv a₁ a₂).symm s).app X =
      L₂.map (G.map (a₁.unit.app X)) ≫ L₂.map (s.app (L₁.obj X)) ≫
        a₂.counit.app (H.obj (L₁.obj X)) := by
  simp [mateEquiv]

/-- **Three of the four mates of a cube are invertible, hence so is the image of the fourth.**
Given eight adjunctions arranged as a cube and the identity `hc` expressing that the two ways
around it agree, invertibility of the three mates `t`, `t'`, `s'` forces invertibility of the
image under `Lu` of the mate of `s`. -/
private lemma isIso_map_mate_of_cube
    {A B C D E F G H : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* E] [Category* F] [Category* G] [Category* H]
    {Le : A ⥤ B} {Re : B ⥤ A} {Lf : C ⥤ D} {Rf : D ⥤ C}
    {Lq : B ⥤ F} {Rq : F ⥤ B} {Lu : D ⥤ H} {Ru : H ⥤ D}
    {La : A ⥤ E} {Ra : E ⥤ A} {Lv : C ⥤ G} {Rv : G ⥤ C}
    {Li : E ⥤ F} {Ri : F ⥤ E} {Lj : G ⥤ H} {Rj : H ⥤ G}
    (ae : Le ⊣ Re) (af : Lf ⊣ Rf) (aq : Lq ⊣ Rq) (au : Lu ⊣ Ru)
    (aa : La ⊣ Ra) (av : Lv ⊣ Rv) (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj)
    {g : A ⥤ C} {h : B ⥤ D} {gi : E ⥤ G} {hi : F ⥤ H}
    (s : TwoSquare Re h g Rf) (t : TwoSquare Rq hi h Ru)
    (s' : TwoSquare Ri hi gi Rj) (t' : TwoSquare Ra gi g Rv)
    (r₁ : Rq ⋙ Re ≅ Ri ⋙ Ra) (r₂ : Ru ⋙ Rf ≅ Rj ⋙ Rv)
    (hc : (t.hComp s).whiskerBottom r₂.hom = (s'.hComp t').whiskerTop r₁.hom)
    (X : A)
    [IsIso (((mateEquiv aq au).symm t).app (Le.obj X))]
    [IsIso (((mateEquiv aa av).symm t').app X)]
    [IsIso (((mateEquiv ai aj).symm s').app (La.obj X))] :
    IsIso (Lu.map (((mateEquiv ae af).symm s).app X)) := by
  have h₂ : IsIso (((mateEquiv (aa.comp ai) (av.comp aj)).symm (s'.hComp t')).app X) := by
    rw [mate_symm_hcomp, TwoSquare.vComp_app]
    change IsIso (Lj.map (((mateEquiv aa av).symm t').app X) ≫
      ((mateEquiv ai aj).symm s').app (La.obj X))
    infer_instance
  have h₁ := (isIso_mate_symm_iff (ae.comp aq) (aa.comp ai) (af.comp au)
    (av.comp aj) (t.hComp s) (s'.hComp t') r₁ r₂ hc X).mpr h₂
  rw [mate_symm_hcomp, TwoSquare.vComp_app] at h₁
  change IsIso (Lu.map (((mateEquiv ae af).symm s).app X) ≫
    ((mateEquiv aq au).symm t).app (Le.obj X)) at h₁
  exact IsIso.of_isIso_comp_right _ (((mateEquiv aq au).symm t).app (Le.obj X))

/-- The mate of a 2-square of sheaf pushforwards is computed sectionwise by the mate of the
underlying 2-square of site functors. -/
private lemma mate_sheafPushforward_app
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    {E : Type*} [Category* E]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : A ⥤ C} {H : B ⥤ D}
    [L₁.IsContinuous JA JB] [R₁.IsContinuous JB JA]
    [L₂.IsContinuous JC JD] [R₂.IsContinuous JD JC]
    [G.IsContinuous JA JC] [H.IsContinuous JB JD]
    (s : TwoSquare R₁ H G R₂)
    (t : TwoSquare (R₂.sheafPushforwardContinuous E JD JC)
      (G.sheafPushforwardContinuous E JA JC)
      (H.sheafPushforwardContinuous E JB JD)
      (R₁.sheafPushforwardContinuous E JB JA))
    (ht : ∀ (F : Sheaf JC E) (V : B),
      (t.app F).hom.app (op V) = F.obj.map (s.app V).op)
    (F : Sheaf JD E) (V : A) :
    (((mateEquiv (a₂.sheafPushforwardContinuous JC JD)
      (a₁.sheafPushforwardContinuous JA JB)).symm t).app F).hom.app (op V) =
      F.obj.map (((mateEquiv a₁ a₂).symm s).app V).op := by
  rw [mate_symm_app_eq, mate_symm_app_eq]
  have hu : ((a₂.sheafPushforwardContinuous JC JD).unit.app F).hom.app
      (op (H.obj (L₁.obj V))) = F.obj.map (a₂.counit.app (H.obj (L₁.obj V))).op := by
    change ((a₂.op.whiskerLeft E).unit.app F.obj).app _ = _
    simp
  have hc (P : Sheaf JA E) : ((a₁.sheafPushforwardContinuous JA JB).counit.app P).hom.app
      (op V) = P.obj.map (a₁.unit.app V).op := by
    change ((a₁.op.whiskerLeft E).counit.app P.obj).app _ = _
    simp
  change ((a₂.sheafPushforwardContinuous JC JD).unit.app F).hom.app
      (op (H.obj (L₁.obj V))) ≫
    (t.app ((L₂.sheafPushforwardContinuous E JC JD).obj F)).hom.app (op (L₁.obj V)) ≫
    ((a₁.sheafPushforwardContinuous JA JB).counit.app
      ((G.sheafPushforwardContinuous E JA JC).obj
        ((L₂.sheafPushforwardContinuous E JC JD).obj F))).hom.app (op V) = _
  rw [hu, hc, ht]
  change F.obj.map _ ≫ F.obj.map (L₂.map (s.app (L₁.obj V))).op ≫
    F.obj.map (L₂.map (G.map (a₁.unit.app V))).op = _
  simp only [← F.obj.map_comp, ← op_comp, Category.assoc]

end Mates

/-! ### The base change map for sheaves of sets on small étale sites -/

section BaseChangeMap

/-- Direct image of sheaves of sets along the small étale sites, abbreviated. -/
private abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  smallEtaleDirectImage.{u, v} f

/-- Inverse image of sheaves of sets along the small étale sites, abbreviated. -/
private abbrev invImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  smallEtaleInverseImage.{u, v} f

/-- **The inverse-image/direct-image adjunction for sheaves of sets on the small étale sites.**
Inverse image is a left Kan extension along base change followed by sheafification, so it is left
adjoint to the direct image, which is restriction along base change. -/
public def smallEtaleSetsAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, v} f ⊣ smallEtaleDirectImage.{u, v} f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange f) (Type (max (u + 1) v)) _ _

/-- The inverse-image/direct-image adjunction, abbreviated. -/
private abbrev adj {X Y : Scheme.{u}} (f : X ⟶ Y) : invImage.{u, v} f ⊣ push.{u, v} f :=
  smallEtaleSetsAdjunction.{u, v} f

/-- Restriction of sheaves of sets along an étale morphism, abbreviated. -/
private abbrev restriction {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :=
  etaleRestrictionSets.{u, v} f

/-- **Restriction along an étale morphism is left adjoint to the direct image** of sheaves of
sets: both are precomposition along a functor of small étale sites, and composition with an
étale morphism is left adjoint to base change along it. -/
public def smallEtaleSetsRestrictionAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    etaleRestrictionSets.{u, v} f ⊣ smallEtaleDirectImage.{u, v} f :=
  (smallEtaleComposeBaseChangeAdj f).sheafPushforwardContinuous _ _

/-- The restriction/direct-image adjunction, abbreviated. -/
private abbrev restrictionAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    restriction.{u, v} f ⊣ push.{u, v} f :=
  smallEtaleSetsRestrictionAdjunction.{u, v} f

/-- **The base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` for sheaves of sets** on the small étale
sites of a commutative square `g' ≫ f = f' ≫ g` of schemes: the mate, under the two
inverse-image/direct-image adjunctions, of the identification of the two composite direct images
around the square. -/
@[stacks 0EZR "the set-valued base change map and the locality calculus only: the map \
g^{-1} f_* to f'_* (g')^{-1} for sheaves of SETS, which the library previously had only \
for abelian coefficients, together with the hypothesis bundle and the option-free mate \
calculus the locality argument runs on. NONE of the tag's three clauses is proved here. \
Clause (1) is blocked at rightSquare_app by a kernel defeq the elaborator cannot reduce \
because getLimitCone is not exposed by the module system; clause (3) sits on top of it; \
clause (2) has no proof content anywhere in the repository."]
public def smallEtaleSetsBaseChange {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    smallEtaleDirectImage.{u, v} f ⋙ smallEtaleInverseImage.{u, v} g ⟶
      smallEtaleInverseImage.{u, v} g' ⋙ smallEtaleDirectImage.{u, v} f' :=
  (mateEquiv (smallEtaleSetsAdjunction.{u, v} g') (smallEtaleSetsAdjunction.{u, v} g)).symm
    ((smallEtalePushforwardCompIso.{u, v} g' f).hom ≫
      (eqToIso (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage.{u, v} k) w)).hom ≫
      (smallEtalePushforwardCompIso.{u, v} f' g).inv)

end BaseChangeMap

/-! ### The base change map of a cartesian square with one side étale

For a cartesian square one side of which is étale, the base change map is invertible.  This is
the appeal to Sites, Lemma 03EF in the proof of Stacks 0EZR: it is what identifies
`g_* F|_{V_i}` with `g_{i,*} F_i`, and `h_* e^{-1} F|_{U_i}` with
`h_{i,*} e_i^{-1} F_i`. -/

section EtaleSquare

/-- Invertibility of the restriction of a morphism of sheaves to the small étale site of a
member `U` of the site implies invertibility of its image under the slice-site pullback.  Every
object of `X_étale` over `U` is isomorphic to the image under composition with `U.hom` of an
object of `U_étale`, namely of its own underlying scheme read over `U`. -/
private lemma isIso_overPullback_of_restriction {X : Scheme.{u}} (U : X.Etale)
    {F G : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (a : F ⟶ G)
    (ha : IsIso ((restriction.{u, v} U.hom).map a)) :
    IsIso (((smallEtaleTopology X).overPullback _ U).map a) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  let V : U.left.Etale := Scheme.Etale.mk W.unop.hom.left
  let k : (smallEtaleCompose U.hom).obj V ≅ W.unop.left :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 W.unop.left.left ≫ W.unop.left.hom = W.unop.hom.left ≫ U.hom
      rw [Category.id_comp]
      exact (MorphismProperty.Over.w W.unop.hom).symm)
  have : IsIso (a.hom.app (op ((smallEtaleCompose U.hom).obj V))) := by
    change IsIso (((restriction.{u, v} U.hom).map a).hom.app (op V))
    infer_instance
  change IsIso (a.hom.app (op W.unop.left))
  rw [← isIso_comp_right_iff _ (G.obj.map k.hom.op), ← a.hom.naturality k.hom.op]
  infer_instance

/-- The identification `e_* g_* ≅ h_* f_*` of the two composite direct images around a
commutative square, read as a 2-square. -/
private def rightSquare {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) : push.{u, v} e ⋙ push.{u, v} g ≅ push.{u, v} h ⋙ push.{u, v} f :=
  smallEtalePushforwardCompIso.{u, v} e g ≪≫
    eqToIso (congrArg (fun k : Y ⟶ S => push.{u, v} k) w) ≪≫
    (smallEtalePushforwardCompIso.{u, v} h f).symm

/-- The base change map of a commutative square with both vertical sides étale, formed with
restriction in place of the inverse image. -/
private def restrictionBaseChange {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) [Etale e] [Etale f] :
    push.{u, v} g ⋙ restriction.{u, v} f ⟶ restriction.{u, v} e ⋙ push.{u, v} h :=
  (mateEquiv (restrictionAdjunction.{u, v} e) (restrictionAdjunction.{u, v} f)).symm
    (rightSquare.{u, v} e h g f w).hom

/-- The composition isomorphism for direct images acts on sections by the composition
isomorphism for the site functors. -/
private lemma pushComp_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : Z.Etale) :
    ((smallEtalePushforwardCompIso.{u, v} f g).hom.app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp f g).hom.app V).op := by
  change 𝟙 _ ≫ F.obj.map ((smallEtaleBaseChangeComp f g).hom.app V).op = _
  rw [Category.id_comp]

/-- The inverse of the composition isomorphism for direct images, on sections. -/
private lemma pushComp_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : Z.Etale) :
    ((smallEtalePushforwardCompIso.{u, v} f g).inv.app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp f g).inv.app V).op := by
  change F.obj.map ((smallEtaleBaseChangeComp f g).inv.app V).op ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Transport of the direct image along an equality of morphisms, on sections. -/
private lemma pushCongr_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : Y.Etale) :
    ((eqToHom (congrArg (fun k : X ⟶ Y => push.{u, v} k) h)).app F).hom.app (op V) =
      F.obj.map (eqToHom (congrArg
        (fun k => (smallEtaleBaseChange k).obj V) h.symm)).op := by
  subst g
  simp
  rfl

/-- The identification of the two composite base change functors of small étale sites around a
commutative square. -/
private def siteSquare {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) :
    smallEtaleBaseChange f ⋙ smallEtaleBaseChange h ≅
      smallEtaleBaseChange g ⋙ smallEtaleBaseChange e :=
  (smallEtaleBaseChangeComp h f).symm ≪≫
    eqToIso (congrArg (fun k : Y ⟶ S => smallEtaleBaseChange k) w.symm) ≪≫
    smallEtaleBaseChangeComp e g

/-- Transport of base change along an equality of morphisms, followed by the projection. -/
private lemma siteCongr_fst {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (V : Y.Etale) :
    (eqToHom (congrArg (fun k => (smallEtaleBaseChange k).obj V) w)).left ≫
      pullback.fst V.hom g = pullback.fst V.hom f := by
  subst g
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The canonical morphism `V ×_X Y ⟶ V ×_S T` attached to a cartesian square is invertible:
pasting the chosen pullback square for `k` and `h` with the given cartesian square exhibits
`V ×_X Y` as the fibre product of `V ⟶ X ⟶ S` and `g`. -/
private lemma isIso_pullbackLift_of_isPullback
    {C : Type*} [Category* C] {Y T X S V : C}
    {e : Y ⟶ T} {h : Y ⟶ X} {g : T ⟶ S} {f : X ⟶ S}
    (sq : IsPullback e h g f) (k : V ⟶ X)
    [HasPullback k h] [HasPullback (k ≫ f) g]
    (w : pullback.fst k h ≫ (k ≫ f) = (pullback.snd k h ≫ e) ≫ g) :
    IsIso (pullback.lift (pullback.fst k h) (pullback.snd k h ≫ e) w) := by
  let q := ((IsPullback.of_hasPullback k h).flip.paste_horiz sq).flip
  have he : pullback.lift (pullback.fst k h) (pullback.snd k h ≫ e) w =
      q.isoPullback.hom :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans q.isoPullback_hom_fst.symm)
      ((pullback.lift_snd _ _ _).trans q.isoPullback_hom_snd.symm)
  rw [he]
  infer_instance

/-- The site comparison of a commutative square, written as the composite of its three
factors. -/
private lemma siteSquare_hom_app {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) (V : S.Etale) :
    (siteSquare e h g f w).hom.app V =
      (smallEtaleBaseChangeComp h f).inv.app V ≫
      eqToHom (congrArg (fun k => (smallEtaleBaseChange k).obj V) w.symm) ≫
      (smallEtaleBaseChangeComp e g).hom.app V := by
  simp -implicitDefEqProofs only [siteSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app]

/-- Three consecutive contravariant maps compose to the map of the composite. -/
private lemma map_op_triple {A B : Type*} [Category* A] [Category* B]
    (F : Aᵒᵖ ⥤ B) {W X Y Z : A} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    F.map c.op ≫ F.map b.op ≫ F.map a.op = F.map (a ≫ b ≫ c).op := by
  simp only [op_comp, F.map_comp, Category.assoc]

end EtaleSquare

/-! ### The data of Stacks 0EZR -/

/-- **The data of Stacks 0EZR.**  A cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

together with an étale covering `{u i : U i ⟶ X}` of `X` such that each `u i ≫ f` factors as
`f_i i ≫ v i` with `v i : V i ⟶ S` étale, the induced cartesian squares `Y_i i = U i ×_X Y` and
`T_i i = V i ×_S T`, the diagonal `e_i i` of the `i`-th local square, and a sheaf `F` on the
small étale site of `T`.

The two fibre products at each index are specified by their cartesian squares rather than chosen,
which determines them up to unique isomorphism; likewise `e_i i` is specified by the two
compatibilities the source uses implicitly, and the cartesianness of the local square is part of
the data, as in the source. -/
public structure EtaleLocalBaseChangeData (C : Type*) [Category* C] where
  /-- The upper left corner of the square. -/
  X : Scheme.{u}
  /-- The upper right corner of the square. -/
  Y : Scheme.{u}
  /-- The lower left corner of the square. -/
  S : Scheme.{u}
  /-- The lower right corner of the square. -/
  T : Scheme.{u}
  /-- The left vertical morphism of the square. -/
  f : X ⟶ S
  /-- The upper horizontal morphism of the square. -/
  h : Y ⟶ X
  /-- The right vertical morphism of the square. -/
  e : Y ⟶ T
  /-- The lower horizontal morphism of the square. -/
  g : T ⟶ S
  /-- The square is cartesian: `Y = X ×_S T`. -/
  cartesian : IsPullback h e f g
  /-- The index set of the covering. -/
  I : Type z
  /-- The members of the covering. -/
  U : I → Scheme.{u}
  /-- The structure morphisms of the covering. -/
  u : ∀ i, U i ⟶ X
  /-- The family `{U i → X}` is an étale covering. -/
  cover : Presieve.ofArrows U u ∈ Scheme.etalePrecoverage X
  /-- The intermediate schemes étale over `S`. -/
  V : I → Scheme.{u}
  /-- The structure morphisms of the intermediate schemes. -/
  v : ∀ i, V i ⟶ S
  /-- Each `V i ⟶ S` is étale. -/
  etale_v : ∀ i, Etale (v i)
  /-- The factorizing morphisms `U i ⟶ V i`. -/
  f_i : ∀ i, U i ⟶ V i
  /-- `U i → X → S` equals `U i → V i → S`. -/
  factorization : ∀ i, f_i i ≫ v i = u i ≫ f
  /-- The upper right corners `U i ×_X Y` of the local squares. -/
  Y_i : I → Scheme.{u}
  /-- The upper horizontal morphisms of the local squares. -/
  h_i : ∀ i, Y_i i ⟶ U i
  /-- The projections `U i ×_X Y ⟶ Y`. -/
  toY_i : ∀ i, Y_i i ⟶ Y
  /-- `Y_i i` is the fibre product `U i ×_X Y`. -/
  upper_cartesian : ∀ i, IsPullback (h_i i) (toY_i i) (u i) h
  /-- The lower right corners `V i ×_S T` of the local squares. -/
  T_i : I → Scheme.{u}
  /-- The lower horizontal morphisms of the local squares. -/
  g_i : ∀ i, T_i i ⟶ V i
  /-- The projections `V i ×_S T ⟶ T`. -/
  toT_i : ∀ i, T_i i ⟶ T
  /-- `T_i i` is the fibre product `V i ×_S T`. -/
  lower_cartesian : ∀ i, IsPullback (g_i i) (toT_i i) (v i) g
  /-- The right vertical morphisms of the local squares. -/
  e_i : ∀ i, Y_i i ⟶ T_i i
  /-- The diagonal `e_i i` lies over `e`. -/
  e_i_compatible : ∀ i, e_i i ≫ toT_i i = toY_i i ≫ e
  /-- The `i`-th local square is cartesian. -/
  local_cartesian : ∀ i, IsPullback (h_i i) (e_i i) (f_i i) (g_i i)
  /-- The sheaf on the small étale site of `T`. -/
  F : Sheaf T.smallEtaleTopology C

/-! ### The right square on sections

The comparison `rightSquare` of the two composite direct images is the composite of three
natural isomorphisms whose actions on sections are `pushComp_hom_app`, `pushCongr_app` and
`pushComp_inv_app`.  Assembling those into the action of `rightSquare` has to be arranged with
care: the obvious ways to split the composite all ask the kernel to compute a component of a
composite of four sheaf-pushforward functors with the transport
`eqToHom (congrArg (fun k ↦ push k) w)` in its path, and that costs far more than the default
budget: `rfl` on such a goal, `simp only [Iso.trans_hom, NatTrans.comp_app]` on
it, and every instantiation of `NatTrans.comp_app` whose second argument is — or begins with —
that transport all exceed it, which rules out both associations of the three-fold composite.
What is cheap, by contrast, is the same equation between *natural transformations*
(`rightSquare_hom_eq`), its transport to one component by `congrArg` (`rightSquare_app_eq`), and
the splitting of a component of such a composite *with the transport factor left as a variable*
(`pushComp₃_app_hom_app`): with that factor abstract the splitting is definitional and small,
and `pushComp₃_app_hom_app_map` then absorbs all three factors into a single `F.obj.map`.

The one step still outstanding is gluing those two halves, i.e. the sectionwise formula
`((rightSquare e h g f w).hom.app F).hom.app (op V) = F.obj.map ((siteSquare e h g f w).hom.app
V).op` itself.  Each direct route to it — `Eq.trans` with the two halves (with the middle
factor inferred and with it given explicitly), the same by `rw`, and the inlined `rw` chain
`rightSquare_app_eq, pushComp₃_app_hom_app, pushComp_hom_app, pushCongr_app, pushComp_inv_app`
— exceeds the budget, although both halves and the statement itself are each well inside it.
The defeq in question is between the two spellings of a section of a composite direct image,
`((push e ⋙ push g).obj F).obj.obj (op V)` and `F.obj.obj (op ((smallEtaleBaseChange g ⋙
smallEtaleBaseChange e).obj V))`; the elaborator reports that it needs `getLimitCone`, which the
module system does not expose, so the kernel is left to unfold it. -/

section RightSquareApp

/-- The right-square comparison, written as the composite of its three factors.  This is an
equation between natural transformations, where no component of a composite of direct images is
formed. -/
private lemma rightSquare_hom_eq {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) :
    (rightSquare.{u, v} e h g f w).hom =
      (smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        eqToHom (congrArg (fun k : Y ⟶ S => push.{u, v} k) w) ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv :=
  rfl

/-- The sections of a component of the composite of the two composition isomorphisms for direct
images with a natural transformation between them, factor by factor.  That transformation is a
variable, which is what keeps the equation definitional at a cost the kernel can pay. -/
private lemma pushComp₃_app_hom_app {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (β : push.{u, v} (e ≫ g) ⟶ push.{u, v} (h ≫ f))
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S.Etale) :
    (((smallEtalePushforwardCompIso.{u, v} e g).hom ≫ β ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app F).hom.app (op V) =
      ((smallEtalePushforwardCompIso.{u, v} e g).hom.app F).hom.app (op V) ≫
        (β.app F).hom.app (op V) ≫
        ((smallEtalePushforwardCompIso.{u, v} h f).inv.app F).hom.app (op V) :=
  rfl

/-- The same composite, with its three factors absorbed into a single contravariant map of `F`,
given the action of the middle factor on sections. -/
private lemma pushComp₃_app_hom_app_map {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S.Etale)
    (β : push.{u, v} (e ≫ g) ⟶ push.{u, v} (h ≫ f))
    (b : (smallEtaleBaseChange (h ≫ f)).obj V ⟶ (smallEtaleBaseChange (e ≫ g)).obj V)
    (hβ : (β.app F).hom.app (op V) = F.obj.map b.op) :
    (((smallEtalePushforwardCompIso.{u, v} e g).hom ≫ β ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp h f).inv.app V ≫ b ≫
        (smallEtaleBaseChangeComp e g).hom.app V).op := by
  rw [pushComp₃_app_hom_app, pushComp_hom_app, hβ, pushComp_inv_app]
  exact map_op_triple F.obj _ b _

/-- A component of the right-square comparison, as the composite of its three factors. -/
private lemma rightSquare_app_eq {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S.Etale) :
    ((rightSquare.{u, v} e h g f w).hom.app F).hom.app (op V) =
      (((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        eqToHom (congrArg (fun k : Y ⟶ S => push.{u, v} k) w) ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app F).hom.app (op V) :=
  congrArg (fun t : push.{u, v} e ⋙ push.{u, v} g ⟶ push.{u, v} h ⋙ push.{u, v} f =>
    (NatTrans.app t F).hom.app (op V)) (rightSquare_hom_eq.{u, v} e h g f w)

end RightSquareApp

/-! ### The site comparison on the projection to the base -/

section SiteProjections

/-- A composite of two morphisms of the small étale site, on underlying schemes.  Mathlib's
`CategoryTheory.MorphismProperty.Comma.comp_left` is the same statement spelled through
`MorphismProperty.Comma.Hom.toCommaMorphism`, which does not match the projection used here. -/
private lemma etaleOver_comp_left {X : Scheme.{u}} {A B D : X.Etale} (a : A ⟶ B) (b : B ⟶ D) :
    (a ≫ b).left = a.left ≫ b.left :=
  rfl

/-- A composite of three morphisms of the small étale site, on underlying schemes. -/
private lemma etaleOver_comp₃_left {X : Scheme.{u}} {A B D E : X.Etale}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) :
    (a ≫ b ≫ c).left = a.left ≫ b.left ≫ c.left :=
  rfl


/-- The identity of the small étale site, on underlying schemes. -/
private lemma etaleOver_id_left {X : Scheme.{u}} (A : X.Etale) :
    (𝟙 A : A ⟶ A).left = 𝟙 A.left :=
  rfl

/-- **The composition isomorphism for base change, followed by the projection to the base.**
This is Mathlib's `CategoryTheory.MorphismProperty.Over.pullbackComp_left_fst_fst`, of which
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp` is an instance. -/
private lemma siteComp_hom_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) := by
  have key {A B : Scheme.{u}} (k : A ⟶ B) :
      MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) k ∧
      MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) k :=
    ⟨⟨fun _ _ ↦ inferInstance⟩,
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩⟩
  obtain ⟨_, _⟩ := key f
  obtain ⟨_, _⟩ := key g
  exact MorphismProperty.Over.pullbackComp_left_fst_fst
    (P := (@Etale : MorphismProperty Scheme.{u})) (Q := ⊤) f g V

/-- The inverse of the composition isomorphism for base change, followed by the projection to
the base: `siteComp_hom_fst` read the other way. -/
private lemma siteComp_inv_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app V).left ≫ pullback.fst V.hom (f ≫ g) =
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g := by
  have hi : ((smallEtaleBaseChangeComp f g).inv.app V).left ≫
      ((smallEtaleBaseChangeComp f g).hom.app V).left = 𝟙 _ := by
    rw [← etaleOver_comp_left, (smallEtaleBaseChangeComp f g).inv_hom_id_app, etaleOver_id_left]
  rw [← siteComp_hom_fst f g V, ← Category.assoc, hi, Category.id_comp]
  rfl

/-- **The site comparison of a commutative square, followed by the projection to the base.**
Both ways around the square project to the structure morphism of `V`; this is the component
identity on which the invertibility of the site comparison of a cartesian square rests. -/
private lemma siteSquare_hom_fst {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) (V : S.Etale) :
    ((siteSquare e h g f w).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) e ≫ pullback.fst V.hom g =
      pullback.fst (pullback.snd V.hom f) h ≫ pullback.fst V.hom f := by
  rw [siteSquare_hom_app e h g f w V, etaleOver_comp_left, etaleOver_comp_left,
    Category.assoc, Category.assoc,
    siteComp_hom_fst, siteCongr_fst w.symm V, siteComp_inv_fst]

end SiteProjections
end Stacks.EtaleCohomology

end
