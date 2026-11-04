module

public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekFreeAbelian

/-!
# The free abelian sheaf functor commutes with lower shriek, compatibly with composition

Let `v : (C₀, T₀) ⥤ (C₁, T₁)` and `w : (C₁, T₁) ⥤ (C₂, T₂)` be continuous functors of sites and
`e : v ⋙ w ≅ u` an identification of their composite with a third continuous functor. Extension
by zero along a continuous functor commutes with the free abelian sheaf functor, both composites
being left adjoint to restriction followed by forgetting the group structure
(`CategoryTheory.Functor.freeLowerShriekIso`); and extension by zero along `u` is extension by
zero along `v` followed by extension by zero along `w`
(`CategoryTheory.Functor.lowerShriekComp`).

This module proves that the two are **compatible**: moving the free abelian sheaf functor across
`u_!` at once and then breaking `u_!` into `v_!` followed by `w_!` is the same as breaking `u_!`
up first and then moving the free abelian sheaf functor across `v_!` and `w_!` in turn.

For the componentwise localization functors of a morphism `f : M ⟶ N` of semi-representable
objects — `v` the relocalization functor `r_f`, `w` the localization functor `j_N` and `u` the
localization functor `j_M` — this is the **naturality in the semi-representable object** of
`CategoryTheory.SemiRepresentable.freeSheafPullbackIso`, which is the one of the three
ingredients of the naturality of Stacks 0D87 part (2) on free abelian sheaves that
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceLowerShriekFreeAbelianNaturality.lean` records
as missing. The other two are
`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality` and
`CategoryTheory.SemiRepresentable.freeAbelianSheafTensorIso_naturality`, both proved there.

## Main definitions

* `CategoryTheory.Functor.freeShriekAdjunction` and
  `CategoryTheory.Functor.shriekFreeAdjunction`: the two adjunctions whose left adjoints the
  commutation compares, `ℤ_{(-)}^♯ ⋙ u_!` and `u_! ⋙ ℤ_{(-)}^♯`, both against restriction along
  `u` followed by forgetting the group structure.
* `CategoryTheory.Functor.freeLowerShriekIso`: `ℤ_{(-)}^♯ ⋙ u_! ≅ u_! ⋙ ℤ_{(-)}^♯`, for an
  arbitrary continuous functor of sites. `CategoryTheory.SemiRepresentable.freeSheafPullbackIso`
  is its value at a componentwise localization functor, on the nose
  (`CategoryTheory.SemiRepresentable.freeSheafPullbackIso_eq`).
* `CategoryTheory.Functor.lowerShriekComp`: `u_! ≅ v_! ⋙ w_!` from `e : v ⋙ w ≅ u`.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_self`: the comparison of a left adjoint with itself
  is the identity.
* `CategoryTheory.Adjunction.comp_assoc'`, `.comp_ofNatIsoRight_isoWhiskerRight`,
  `.ofNatIsoRight_comp`: the algebra of `CategoryTheory.Adjunction.comp` against
  `CategoryTheory.Adjunction.ofNatIsoRight`, which is what matches up the three bracketings of
  one composite of three adjunctions.
* `CategoryTheory.Functor.isoWhiskerLeft_sheafPushforwardContinuousComp'_forget`: the
  composition comparison of restriction functors is the same read on sheaves of sets after
  forgetting the group structure as it is on abelian sheaves before.
* `CategoryTheory.Functor.freeLowerShriekIso_comp`: **the compatibility.**

## Implementation notes

The proof is three applications of the hexagon
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker`, at three factorizations of one and
the same right adjoint `u_* ⋙ (forget)`:

* `v_! ⊣ v_*` on sheaves of sets as the first leg and `ℤ_{(-)}^♯ ⋙ w_!` as the second, which
  produces the third factor of the upper path;
* `ℤ_{(-)}^♯ ⋙ v_!` as the first leg and `w_!` on abelian sheaves as the second, which produces
  the second factor;
* `u_!` on sheaves of sets as the first leg and `ℤ_{(-)}^♯` as the second, which produces the
  lower path.

In each one of the two comparisons is a `CategoryTheory.Adjunction.leftAdjointUniq` of an
adjunction with itself, hence the identity; so each hexagon contributes exactly one factor. The
hypothesis `hcomp` of the hexagon is `rfl` for the first and an associativity rearrangement for
the other two, because the three bracket the composite of three adjunctions differently.

The identity isomorphism of `u_* ⋙ (forget)` that the third hexagon needs is written out rather
than left as `Iso.refl _`: its two endpoints are the two orders in which restriction along `u`
and forgetting the group structure can be performed, which are the same functor but not the same
expression, and a metavariable is solved against the first of them and then fails against the
second.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace CategoryTheory.Adjunction

variable {C₀ : Type*} [Category C₀] {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
  {C₃ : Type*} [Category C₃]

/-- **The comparison of a left adjoint with itself is the identity.** -/
theorem leftAdjointUniq_self {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} (adj : F ⊣ G) :
    leftAdjointUniq adj adj = Iso.refl F := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  refine (adj.homEquiv x (F.obj x)).injective ?_
  rw [homEquiv_unit, homEquiv_unit, unit_leftAdjointUniq_hom_app adj adj]
  simp

/-- **Reading the second of two composable adjunctions through an isomorphism of its right
adjoint** reads the composite through that isomorphism whiskered by the first right adjoint. -/
theorem comp_ofNatIsoRight_isoWhiskerRight {F₀ : C₀ ⥤ C₁} {G₀ : C₁ ⥤ C₀} (adj₀ : F₀ ⊣ G₀)
    {F : C₁ ⥤ C₂} {R R' : C₂ ⥤ C₁} (adj : F ⊣ R) (ε : R ≅ R') :
    adj₀.comp (adj.ofNatIsoRight ε) =
      (adj₀.comp adj).ofNatIsoRight (Functor.isoWhiskerRight ε G₀) := by
  refine Adjunction.ext (NatTrans.ext (funext fun x => ?_))
  simp [Adjunction.comp, Adjunction.ofNatIsoRight]

/-- **Reading the first of two composable adjunctions through an isomorphism of its right
adjoint** reads the composite through that isomorphism whiskered by the second right adjoint. -/
theorem ofNatIsoRight_comp {F : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀} (adj : F ⊣ R) (ε : R ≅ R')
    {F₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} (adj₂ : F₂ ⊣ R₂) :
    (adj.ofNatIsoRight ε).comp adj₂ =
      (adj.comp adj₂).ofNatIsoRight (Functor.isoWhiskerLeft R₂ ε) := by
  refine Adjunction.ext (NatTrans.ext (funext fun x => ?_))
  simp [Adjunction.comp, Adjunction.ofNatIsoRight]

/-- **Composition of adjunctions is associative.** -/
theorem comp_assoc' {F₀ : C₀ ⥤ C₁} {G₀ : C₁ ⥤ C₀} (adj₀ : F₀ ⊣ G₀)
    {F₁ : C₁ ⥤ C₂} {G₁ : C₂ ⥤ C₁} (adj₁ : F₁ ⊣ G₁)
    {F₂ : C₂ ⥤ C₃} {G₂ : C₃ ⥤ C₂} (adj₂ : F₂ ⊣ G₂) :
    (adj₀.comp adj₁).comp adj₂ = adj₀.comp (adj₁.comp adj₂) := by
  refine Adjunction.ext (NatTrans.ext (funext fun x => ?_))
  simp [Adjunction.comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

section One

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous JC JD]
  [HasWeakSheafify JC (Type u)] [HasWeakSheafify JD (Type u)]
  [HasWeakSheafify JC AddCommGrpCat.{u}] [HasWeakSheafify JD AddCommGrpCat.{u}]
  [∀ F : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F]

/-- The free abelian sheaf functor followed by extension by zero along `u`, adjoint to
restriction along `u` followed by forgetting the group structure. -/
def freeShriekAdjunction :
    Sheaf.composeAndSheafify JC AddCommGrpCat.free ⋙
      Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{u} JC JD ⊣
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD ⋙
      sheafCompose JC (forget AddCommGrpCat.{u}) :=
  (Sheaf.adjunction JC AddCommGrpCat.adj).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u AddCommGrpCat.{u} JC JD)

/-- Extension by zero along `u` followed by the free abelian sheaf functor, adjoint to the same
functor as `CategoryTheory.Functor.freeShriekAdjunction`: forgetting the group structure and
restricting along `u` can be performed in either order. -/
def shriekFreeAdjunction :
    Functor.sheafPullbackConstruction.sheafPullback u (Type u) JC JD ⋙
      Sheaf.composeAndSheafify JD AddCommGrpCat.free ⊣
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD ⋙
      sheafCompose JC (forget AddCommGrpCat.{u}) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u) JC JD).comp
    (Sheaf.adjunction JD AddCommGrpCat.adj)

/-- **Extension by zero along a continuous functor of sites commutes with the free abelian sheaf
functor.** Both composites are left adjoint to restriction along `u` followed by the functor
taking an abelian sheaf to its underlying sheaf of sets, and that composite does not depend on
the order in which restriction and forgetting are performed.

This is `CategoryTheory.SemiRepresentable.freeSheafPullbackIso` with the componentwise
localization functor replaced by an arbitrary continuous functor. -/
def freeLowerShriekIso :
    Sheaf.composeAndSheafify JC AddCommGrpCat.free ⋙
        Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{u} JC JD ≅
      Functor.sheafPullbackConstruction.sheafPullback u (Type u) JC JD ⋙
        Sheaf.composeAndSheafify JD AddCommGrpCat.free :=
  Adjunction.leftAdjointUniq (freeShriekAdjunction JC JD u) (shriekFreeAdjunction JC JD u)

end One

section Pushforward

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsCocontinuous JC JD]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify JC (Type u)] [HasWeakSheafify JD (Type u)]
  [HasWeakSheafify JC AddCommGrpCat.{u}] [HasWeakSheafify JD AddCommGrpCat.{u}]

/-- **Restriction along a continuous and cocontinuous functor of sites commutes with the free
abelian sheaf functor.** Applying the sectionwise free abelian group commutes with restriction of
presheaves strictly, and restriction commutes with sheafification by Mathlib's
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`.

This is `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso` with the componentwise
localization functor replaced by an arbitrary continuous and cocontinuous functor
(`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_eq`). Packaging it as a named
isomorphism of *functors* is what makes its components `.app`s of named composites: the
components of the underlying Mathlib comparison are indexed by presheaves, and the presheaf
`u.op ⋙ (Z.obj ⋙ ℤ)` it is read at is a different expression from the presheaf
`((u^{-1}Z).obj ⋙ ℤ)` the surrounding composites produce, which makes each equation between them
a defeq check on a large term. -/
def freePushforwardIso :
    Sheaf.composeAndSheafify JD AddCommGrpCat.free ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD ≅
      u.sheafPushforwardContinuous (Type u) JC JD ⋙
        Sheaf.composeAndSheafify JC AddCommGrpCat.free :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf JD (Type u) ⋙
      (Functor.whiskeringRight Dᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free)
    (u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} JC JD).symm

end Pushforward

section Comp

variable {C₀ C₁ C₂ : Type u} [SmallCategory C₀] [SmallCategory C₁] [SmallCategory C₂]
  (T₀ : GrothendieckTopology C₀) (T₁ : GrothendieckTopology C₁) (T₂ : GrothendieckTopology C₂)
  (v : C₀ ⥤ C₁) (w : C₁ ⥤ C₂) (uu : C₀ ⥤ C₂)
  [v.IsContinuous T₀ T₁] [w.IsContinuous T₁ T₂] [uu.IsContinuous T₀ T₂]

/-- **Extension by zero along a composite is the composite of the extensions by zero.** Both are
left adjoint to restriction along the composite, which `e` identifies with restriction along `w`
followed by restriction along `v`. -/
def lowerShriekComp (A : Type t) [Category.{u} A] [HasWeakSheafify T₁ A] [HasWeakSheafify T₂ A]
    [∀ F : C₀ᵒᵖ ⥤ A, v.op.HasLeftKanExtension F]
    [∀ F : C₁ᵒᵖ ⥤ A, w.op.HasLeftKanExtension F]
    [∀ F : C₀ᵒᵖ ⥤ A, uu.op.HasLeftKanExtension F]
    (e : v ⋙ w ≅ uu) :
    Functor.sheafPullbackConstruction.sheafPullback uu A T₀ T₂ ≅
      Functor.sheafPullbackConstruction.sheafPullback v A T₀ T₁ ⋙
        Functor.sheafPullbackConstruction.sheafPullback w A T₁ T₂ :=
  Adjunction.leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uu A T₀ T₂)
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v A T₀ T₁).comp
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous w A T₁ T₂)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e A T₀ T₁ T₂))

variable [HasWeakSheafify T₀ (Type u)] [HasWeakSheafify T₁ (Type u)] [HasWeakSheafify T₂ (Type u)]
  [HasWeakSheafify T₀ AddCommGrpCat.{u}] [HasWeakSheafify T₁ AddCommGrpCat.{u}]
  [HasWeakSheafify T₂ AddCommGrpCat.{u}]
  [∀ F : C₀ᵒᵖ ⥤ Type u, v.op.HasLeftKanExtension F]
  [∀ F : C₁ᵒᵖ ⥤ Type u, w.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ Type u, uu.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ AddCommGrpCat.{u}, v.op.HasLeftKanExtension F]
  [∀ F : C₁ᵒᵖ ⥤ AddCommGrpCat.{u}, w.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ AddCommGrpCat.{u}, uu.op.HasLeftKanExtension F]

variable (e : v ⋙ w ≅ uu)

omit [HasWeakSheafify T₀ (Type u)] [HasWeakSheafify T₁ (Type u)] [HasWeakSheafify T₂ (Type u)]
  [HasWeakSheafify T₀ AddCommGrpCat.{u}] [HasWeakSheafify T₁ AddCommGrpCat.{u}]
  [HasWeakSheafify T₂ AddCommGrpCat.{u}]
  [∀ F : C₀ᵒᵖ ⥤ Type u, v.op.HasLeftKanExtension F]
  [∀ F : C₁ᵒᵖ ⥤ Type u, w.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ Type u, uu.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ AddCommGrpCat.{u}, v.op.HasLeftKanExtension F]
  [∀ F : C₁ᵒᵖ ⥤ AddCommGrpCat.{u}, w.op.HasLeftKanExtension F]
  [∀ F : C₀ᵒᵖ ⥤ AddCommGrpCat.{u}, uu.op.HasLeftKanExtension F] in
/-- **The composition comparison of restriction functors is the same before and after forgetting
the group structure.** Both whiskerings of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` are, at a sheaf and an object,
precomposition with `e` on underlying sections. -/
theorem isoWhiskerLeft_sheafPushforwardContinuousComp'_forget :
    Functor.isoWhiskerLeft (sheafCompose T₂ (forget AddCommGrpCat.{u}))
        (Functor.sheafPushforwardContinuousComp' e (Type u) T₀ T₁ T₂) =
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} T₀ T₁ T₂)
        (sheafCompose T₀ (forget AddCommGrpCat.{u})) := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  ext Y
  rfl

section Proof

/-- The comparison of restrictions along `v ⋙ w` and along `uu`, on abelian sheaves, whiskered
by the functor forgetting the group structure. This is the comparison `e` of right adjoints that
all three hexagons of `CategoryTheory.Functor.freeLowerShriekIso_comp` are read at. -/
private abbrev cmp :
    w.sheafPushforwardContinuous AddCommGrpCat.{u} T₁ T₂ ⋙
        v.sheafPushforwardContinuous AddCommGrpCat.{u} T₀ T₁ ⋙
          sheafCompose T₀ (forget AddCommGrpCat.{u}) ≅
      uu.sheafPushforwardContinuous AddCommGrpCat.{u} T₀ T₂ ⋙
        sheafCompose T₀ (forget AddCommGrpCat.{u}) :=
  Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} T₀ T₁ T₂)
    (sheafCompose T₀ (forget AddCommGrpCat.{u}))

private abbrev sV := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v (Type u) T₀ T₁
private abbrev sW := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous w (Type u) T₁ T₂
private abbrev sU := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uu (Type u) T₀ T₂
private abbrev aV :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v AddCommGrpCat.{u} T₀ T₁
private abbrev aW :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous w AddCommGrpCat.{u} T₁ T₂

omit [HasWeakSheafify T₀ (Type u)] in
/-- **The free abelian sheaf functor commutes with lower shriek compatibly with composition.**
Going along the upper path — extension by zero along `u` broken into `v` then `w`, then the free
abelian sheaf functor moved across `v_!` and then across `w_!` — is the same as moving it across
`u_!` at once and then breaking `u_!` into `v_!` followed by `w_!`.

For the componentwise localization functors of semi-representable objects this is the naturality
in the semi-representable object of
`CategoryTheory.SemiRepresentable.freeSheafPullbackIso`. -/
theorem freeLowerShriekIso_comp :
    Functor.whiskerLeft (Sheaf.composeAndSheafify T₀ AddCommGrpCat.free)
          (lowerShriekComp T₀ T₁ T₂ v w uu AddCommGrpCat.{u} e).hom ≫
        Functor.whiskerRight (freeLowerShriekIso T₀ T₁ v).hom
          (Functor.sheafPullbackConstruction.sheafPullback w AddCommGrpCat.{u} T₁ T₂) ≫
          Functor.whiskerLeft
            (Functor.sheafPullbackConstruction.sheafPullback v (Type u) T₀ T₁)
            (freeLowerShriekIso T₁ T₂ w).hom =
      (freeLowerShriekIso T₀ T₂ uu).hom ≫
        Functor.whiskerRight (lowerShriekComp T₀ T₁ T₂ v w uu (Type u) e).hom
          (Sheaf.composeAndSheafify T₂ AddCommGrpCat.free) := by
  set C := cmp T₀ T₁ T₂ v w uu e with hC
  set aU := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uu AddCommGrpCat.{u} T₀ T₂
    with haU
  set f₀ := Sheaf.adjunction T₀ AddCommGrpCat.adj with hf₀
  set f₁ := Sheaf.adjunction T₁ AddCommGrpCat.adj with hf₁
  set f₂ := Sheaf.adjunction T₂ AddCommGrpCat.adj with hf₂
  set sv := sV T₀ T₁ v with hsv
  set sw := sW T₁ T₂ w with hsw
  set su := sU T₀ T₂ uu with hsu
  set av := aV T₀ T₁ v with hav
  set aw := aW T₁ T₂ w with haw
  set idc := Iso.refl (uu.sheafPushforwardContinuous AddCommGrpCat.{u} T₀ T₂ ⋙
    sheafCompose T₀ (forget AddCommGrpCat.{u})) with hidc
  -- the three bracketings of one composite of three adjunctions
  have eP : ((f₀.comp av).comp aw).ofNatIsoRight C =
      f₀.comp ((av.comp aw).ofNatIsoRight
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} T₀ T₁ T₂)) :=
    (congrArg (fun a => a.ofNatIsoRight C) (Adjunction.comp_assoc' f₀ av aw)).trans
      (Adjunction.comp_ofNatIsoRight_isoWhiskerRight f₀ (av.comp aw)
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} T₀ T₁ T₂)).symm
  have eQ : ((sv.comp f₁).comp aw).ofNatIsoRight C =
      (sv.comp (f₁.comp aw)).ofNatIsoRight C :=
    congrArg (fun a => a.ofNatIsoRight C) (Adjunction.comp_assoc' sv f₁ aw)
  have eZ : (((sv.comp sw).ofNatIsoRight
        (Functor.sheafPushforwardContinuousComp' e (Type u) T₀ T₁ T₂)).comp f₂).ofNatIsoRight
        idc =
      (sv.comp (sw.comp f₂)).ofNatIsoRight C :=
    (Adjunction.ofNatIsoRight_refl _).trans
      ((Adjunction.ofNatIsoRight_comp (sv.comp sw)
          (Functor.sheafPushforwardContinuousComp' e (Type u) T₀ T₁ T₂) f₂).trans
        ((congrArg (fun a => a.ofNatIsoRight
                (Functor.isoWhiskerLeft (sheafCompose T₂ (forget AddCommGrpCat.{u}))
                  (Functor.sheafPushforwardContinuousComp' e (Type u) T₀ T₁ T₂)))
              (Adjunction.comp_assoc' sv sw f₂)).trans
          (congrArg (fun ε => (sv.comp (sw.comp f₂)).ofNatIsoRight ε)
            (isoWhiskerLeft_sheafPushforwardContinuousComp'_forget T₀ T₁ T₂ v w uu e))))
  have eR : (su.comp f₂).ofNatIsoRight idc = su.comp f₂ := Adjunction.ofNatIsoRight_refl _
  -- the three hexagons, at the three factorizations of `u_* ⋙ (forget)`
  have h1 := Adjunction.leftAdjointUniq_hom_comp_whisker sv sv (f₁.comp aw) (sw.comp f₂)
    (f₀.comp aU) ((sv.comp (sw.comp f₂)).ofNatIsoRight C) C rfl
  have h2 := Adjunction.leftAdjointUniq_hom_comp_whisker (f₀.comp av) (sv.comp f₁) aw aw
    (f₀.comp aU) ((sv.comp (f₁.comp aw)).ofNatIsoRight C) C eQ.symm
  have h3 := Adjunction.leftAdjointUniq_hom_comp_whisker su
    ((sv.comp sw).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e (Type u) T₀ T₁ T₂)) f₂ f₂
    (f₀.comp aU) ((sv.comp (sw.comp f₂)).ofNatIsoRight C) idc eZ.symm
  -- the first factor of the upper path, in the bracketing the second hexagon forces
  rw [congrArg (fun a => (Adjunction.leftAdjointUniq (f₀.comp aU) a).hom) eP,
    Adjunction.leftAdjointUniq_comp f₀ f₀ aU
      ((av.comp aw).ofNatIsoRight
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} T₀ T₁ T₂))] at h2
  rw [congrArg (fun a => (Adjunction.leftAdjointUniq (f₀.comp aU) a).hom) eR] at h3
  -- each hexagon has one comparison of an adjunction with itself, hence the identity
  simp only [Adjunction.leftAdjointUniq_self, Iso.refl_hom, Functor.whiskerRight_id',
    Functor.whiskerLeft_id', Category.id_comp, Category.comp_id] at h1 h2 h3
  dsimp only [freeLowerShriekIso, lowerShriekComp, freeShriekAdjunction, shriekFreeAdjunction]
  rw [← Category.assoc, h2, h1, ← h3]

end Proof

end Comp

end CategoryTheory.Functor

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : FormalCoproduct.{u} C)

/-- `freeSheafPullbackIso` is the general statement
`CategoryTheory.Functor.freeLowerShriekIso` at the componentwise localization functor. -/
theorem freeSheafPullbackIso_eq :
    freeSheafPullbackIso J K =
      Functor.freeLowerShriekIso (componentwiseTopology J K) J (componentOverForget K) :=
  rfl

/-- `freeSheafPushforwardIso` is the general statement
`CategoryTheory.Functor.freePushforwardIso` at the componentwise localization functor. -/
theorem freeSheafPushforwardIso_eq :
    freeSheafPushforwardIso J K =
      Functor.freePushforwardIso (componentwiseTopology J K) J (componentOverForget K) :=
  rfl

end CategoryTheory.SemiRepresentable

end
