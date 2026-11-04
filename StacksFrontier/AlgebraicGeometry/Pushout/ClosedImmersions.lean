module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Abelian.CommSq
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections

/-!
# Pushouts of two closed immersions of schemes

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions of schemes.  Then the pushout
`Y ⨿_Z X` exists in the category of schemes, the defining square is also cartesian, the two
canonical maps `a : X ⟶ Y ⨿_Z X` and `b : Y ⟶ Y ⨿_Z X` are closed immersions, and the
structure sheaves fit into a short exact sequence

`0 ⟶ 𝒪_(Y ⨿_Z X) ⟶ a_* 𝒪_X ⊕ b_* 𝒪_Y ⟶ c_* 𝒪_Z ⟶ 0`

of modules over `𝒪_(Y ⨿_Z X)`, where `c = a ∘ i = b ∘ j`.

## Main definitions

* `AlgebraicGeometry.Scheme.structureSheafModule` regards the structure sheaf of a scheme as a
  module over itself, and `AlgebraicGeometry.Scheme.Hom.pushforwardStructureSheafModule` pushes
  such a module forward along a morphism.
* `AlgebraicGeometry.pushoutStructureSheafModuleToBiprod` and
  `AlgebraicGeometry.pushoutBiprodToIntersection` are the two maps of the structure-sheaf
  sequence of the pushout.

## Main results

* `AlgebraicGeometry.hasPushout_of_isClosedImmersion`: the pushout exists.
* `AlgebraicGeometry.isPullback_pushout_of_isClosedImmersion`: its defining square is also a
  fibre square.
* `AlgebraicGeometry.pushout_inl_isClosedImmersion` and
  `AlgebraicGeometry.pushout_inr_isClosedImmersion`: the two canonical maps into the pushout
  are closed immersions.
* `AlgebraicGeometry.pushout_structureSheafModule_shortExact`: the structure-sheaf sequence is
  short exact.

## Implementation notes

A closed immersion is integral, and a closed immersion `i : Z ⟶ X` always satisfies the
affine-neighbourhood condition of
`AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation`, because the fibres of a
closed immersion are at most singletons and affine opens form a basis.  So the pushout is
obtained from the construction for a closed immersion and an integral morphism, over the
terminal scheme as a base; existence is recorded as a `HasPushout` instance so that everything
downstream can use Mathlib's canonical `pushout`, `pushout.inl` and `pushout.inr`.

The short exact sequence is formed in the abelian category of modules over the structure sheaf
of the pushout.  Its second map is the difference of the two restriction maps to the common
closed subscheme, so that the sequence is the one attached by
`CategoryTheory.CommSq.shortComplex'` to the cartesian square of sections; exactness in the
middle and injectivity on the left are therefore the pullback square of sections of the
pushout, while surjectivity on the right is right exactness of pushforward along a closed
immersion.

## References

* [Stacks Project, Tag 0B7M](https://stacks.math.columbia.edu/tag/0B7M)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-! ### Existence of the pushout -/

/-- The standing situation of [Stacks Project, Tag 0ECI] attached to two closed immersions
`i : Z ⟶ X` and `j : Z ⟶ Y`, with the terminal scheme as a base.  A closed immersion is
integral, and the affine-neighbourhood condition holds because a closed immersion has at most
one point in each fibre and affine opens form a basis. -/
private def closedImmersionPushoutSituation {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
  letI : IsFinite j := IsFinite.instOfIsClosedImmersion j
  { S := ⊤_ Scheme
    X := X
    Y := Y
    Z := Z
    pX := terminal.from X
    pY := terminal.from Y
    pZ := terminal.from Z
    i := i
    j := j
    i_over := by subsingleton
    j_over := by subsingleton
    fiber_preimage_subset_affine := by
      intro y
      by_cases hy : ∃ z, j z = y
      · obtain ⟨z, rfl⟩ := hy
        obtain ⟨_, ⟨U, hU, rfl⟩, hzi, _⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (a := i z) (by trivial) isOpen_univ
        refine ⟨U, hU, fun z' hz' ↦ ?_⟩
        obtain rfl := j.isClosedEmbedding.injective hz'
        simpa using hzi
      · exact ⟨⊥, isAffineOpen_bot X, fun z hz ↦ absurd ⟨z, hz⟩ hy⟩ }

/-- **[Stacks, Tag 0B7M].** The pushout of two closed immersions of schemes exists in the
category of schemes. -/
@[stacks 0B7M "the pushout exists"]
instance hasPushout_of_isClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : HasPushout i j :=
  let h := pushoutAlongClosedImmersionAndIntegral (closedImmersionPushoutSituation i j)
  ⟨⟨⟨PushoutCocone.mk h.a h.b h.isPushout.w, h.isPushout.isColimit⟩⟩⟩

/-- **[Stacks, Tag 0B7M].** The defining pushout square of two closed immersions of schemes is
also a fibre square. -/
@[stacks 0B7M "the diagram is a fibre square"]
theorem isPullback_pushout_of_isClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsPullback i j (pushout.inl i j) (pushout.inr i j) := by
  let s := closedImmersionPushoutSituation i j
  let h := pushoutAlongClosedImmersionAndIntegral s
  let e := h.isPushout.isColimit.coconePointUniqueUpToIso (pushout.isColimit i j)
  refine (pushoutSquare_isPullback s).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e rfl rfl
    ?_ ?_
  · show h.a ≫ e.hom = pushout.inl i j
    exact h.isPushout.isColimit.comp_coconePointUniqueUpToIso_hom
      (pushout.isColimit i j) WalkingSpan.left
  · show h.b ≫ e.hom = pushout.inr i j
    exact h.isPushout.isColimit.comp_coconePointUniqueUpToIso_hom
      (pushout.isColimit i j) WalkingSpan.right

/-- Composing a closed immersion with an isomorphism gives a closed immersion. -/
private lemma isClosedImmersion_comp_iso {X Y W : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (e : Y ≅ W) : IsClosedImmersion (f ≫ e.hom) :=
  (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) f e.hom).2 ‹_›

/-- **[Stacks, Tag 0B7M].** The canonical map `a : X ⟶ Y ⨿_Z X` out of the first scheme is a
closed immersion. -/
@[stacks 0B7M "the morphism a is a closed immersion"]
instance pushout_inl_isClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsClosedImmersion (pushout.inl i j) := by
  let s := closedImmersionPushoutSituation j i
  let h := pushoutAlongClosedImmersionAndIntegral s
  let e := h.isPushout.flip.isColimit.coconePointUniqueUpToIso (pushout.isColimit i j)
  have hcomp : h.b ≫ e.hom = pushout.inl i j :=
    h.isPushout.flip.isColimit.comp_coconePointUniqueUpToIso_hom
      (pushout.isColimit i j) WalkingSpan.left
  have : IsClosedImmersion h.b := pushoutInr_isClosedImmersion s
  rw [← hcomp]
  exact isClosedImmersion_comp_iso h.b e

/-- **[Stacks, Tag 0B7M].** The canonical map `b : Y ⟶ Y ⨿_Z X` out of the second scheme is a
closed immersion. -/
@[stacks 0B7M "the morphism b is a closed immersion"]
instance pushout_inr_isClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsClosedImmersion (pushout.inr i j) := by
  let s := closedImmersionPushoutSituation i j
  let h := pushoutAlongClosedImmersionAndIntegral s
  let e := h.isPushout.isColimit.coconePointUniqueUpToIso (pushout.isColimit i j)
  have hcomp : h.b ≫ e.hom = pushout.inr i j :=
    h.isPushout.isColimit.comp_coconePointUniqueUpToIso_hom
      (pushout.isColimit i j) WalkingSpan.right
  have : IsClosedImmersion h.b := pushoutInr_isClosedImmersion s
  rw [← hcomp]
  exact isClosedImmersion_comp_iso h.b e

/-! ### The structure sheaf as a module, and its pushforward -/

/-- The structure sheaf of a scheme, regarded as a module over itself. -/
def Scheme.structureSheafModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The structure sheaf of the source of a morphism of schemes, pushed forward to its target
and regarded as a module over the structure sheaf of the target. -/
abbrev Scheme.Hom.pushforwardStructureSheafModule {X P : Scheme.{u}} (f : X ⟶ P) : P.Modules :=
  (Scheme.Modules.pushforward f).obj X.structureSheafModule

/-- The canonical map from the structure sheaf of the target of `f` to the pushforward along
`f` of the structure sheaf of its source. -/
def Scheme.Hom.structureSheafModuleMap {X P : Scheme.{u}} (f : X ⟶ P) :
    P.structureSheafModule ⟶ f.pushforwardStructureSheafModule :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

private lemma structureSheafModuleMap_app {X P : Scheme.{u}} (f : X ⟶ P) (U : P.Opens) :
    (f.structureSheafModuleMap).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (f.app U) := by
  ext x
  rfl

/-- Restriction along a morphism `i : Z ⟶ X`, pushed forward along a second morphism
`a : X ⟶ P`: the canonical map `a_* 𝒪_X ⟶ (i ≫ a)_* 𝒪_Z`. -/
def pushforwardStructureSheafModuleToComp {Z X P : Scheme.{u}} (i : Z ⟶ X) (a : X ⟶ P) :
    a.pushforwardStructureSheafModule ⟶ (i ≫ a).pushforwardStructureSheafModule :=
  (Scheme.Modules.pushforward a).map i.structureSheafModuleMap ≫
    (Scheme.Modules.pushforwardComp i a).hom.app _

/-- For a pushout square of a closed immersion and an integral morphism whose map out of `X` is
affine, the structure sheaves form a fibre square of modules over the structure sheaf of the
pushout.  This is the module-theoretic form of [Stacks Project, Tag 0E25]. -/
private lemma isPullback_pushforwardStructureSheafModule {Z X Y P : Scheme.{u}} (i : Z ⟶ X)
    (j : Z ⟶ Y) (a : X ⟶ P) (b : Y ⟶ P) [IsClosedImmersion i] [IsIntegralHom j]
    [IsAffineHom a] (h : IsPushout i j a b) :
    IsPullback a.structureSheafModuleMap b.structureSheafModuleMap
      (pushforwardStructureSheafModuleToComp i a)
      (pushforwardStructureSheafModuleToComp j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _) := by
  let F := Scheme.Modules.toPresheaf P
  have hF : IsPullback (F.map a.structureSheafModuleMap) (F.map b.structureSheafModuleMap)
      (F.map (pushforwardStructureSheafModuleToComp i a))
      (F.map (pushforwardStructureSheafModuleToComp j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)) := by
    apply IsPullback.of_forall_isPullback_app
    intro U
    let G := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    have hU := (structureSheaf_isPullback_of_isPushout_of_isAffineHom h U.unop).map G |>.flip
    have e : i ⁻¹ᵁ (a ⁻¹ᵁ U.unop) = j ⁻¹ᵁ (b ⁻¹ᵁ U.unop) := by
      simpa only [Scheme.Hom.comp_preimage] using
        congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U.unop) h.w
    let eR := congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e.symm
    let eΓ := congrArg G.obj eR
    have hunitMap : (Z.structureSheafModule).presheaf.map (eqToHom e).op = G.map (eqToHom eR) := by
      show G.map (Z.presheaf.map (eqToHom e).op) = G.map (eqToHom eR)
      simp only [eqToHom_op, eqToHom_map]
    have htransport : G.map (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e)) =
        eqToHom eΓ.symm := by
      simp only [eqToHom_map]
    have htransport' : G.map (eqToHom eR) = eqToHom eΓ := by
      simp only [eqToHom_map]
    have hU' : IsPullback (G.map (a.app U.unop)) (G.map (b.app U.unop))
        (G.map (i.app (a ⁻¹ᵁ U.unop)))
        (G.map (j.app (b ⁻¹ᵁ U.unop)) ≫ eqToHom eΓ) :=
      hU.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso eΓ) rfl rfl
        (by
          show (G.map (i.app (a ⁻¹ᵁ U.unop)) ≫
            G.map (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e))) ≫
              eqToHom eΓ = G.map (i.app _)
          rw [htransport]
          simp)
        (by simp [G])
    have key : ∀ {W V : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ P),
        (F.map (pushforwardStructureSheafModuleToComp f g)).app (Opposite.op U.unop) =
          G.map (f.app (g ⁻¹ᵁ U.unop)) := fun f g ↦ by
      show ((Scheme.Modules.pushforward g).map f.structureSheafModuleMap).app U.unop ≫
        ((Scheme.Modules.pushforwardComp f g).hom.app _).app U.unop = _
      simp only [Scheme.Modules.pushforwardComp_hom_app_app,
        Scheme.Modules.pushforward_map_app, structureSheafModuleMap_app]
      rfl
    have h₄ : ((F.map (pushforwardStructureSheafModuleToComp j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)).app (Opposite.op U.unop)) =
        G.map (j.app (b ⁻¹ᵁ U.unop)) ≫ eqToHom eΓ := by
      rw [Functor.map_comp, NatTrans.comp_app, key]
      congr 1
      show ((Scheme.Modules.pushforwardCongr h.w.symm).hom.app
        Z.structureSheafModule).app U.unop = _
      simp only [Scheme.Modules.pushforwardCongr_hom_app_app]
      ext x
      exact congrArg
        (fun f : AddCommGrpCat.Hom _ _ ↦ f.hom x) (hunitMap.trans htransport')
    show IsPullback ((F.map a.structureSheafModuleMap).app (Opposite.op U.unop))
      ((F.map b.structureSheafModuleMap).app (Opposite.op U.unop))
      ((F.map (pushforwardStructureSheafModuleToComp i a)).app (Opposite.op U.unop))
      ((F.map (pushforwardStructureSheafModuleToComp j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)).app (Opposite.op U.unop))
    rw [show ((F.map a.structureSheafModuleMap).app (Opposite.op U.unop)) =
      G.map (a.app U.unop) from rfl,
      show ((F.map b.structureSheafModuleMap).app (Opposite.op U.unop)) =
        G.map (b.app U.unop) from rfl, key, h₄]
    exact hU'
  exact hF.of_map_of_faithful F

private lemma epi_structureSheafModuleMap {X Z : Scheme.{u}} (f : Z ⟶ X)
    [IsClosedImmersion f] : Epi f.structureSheafModuleMap :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion f

private lemma epi_pushforwardStructureSheafModuleToComp {Z X P : Scheme.{u}} (i : Z ⟶ X)
    (a : X ⟶ P) [IsClosedImmersion i] [IsClosedImmersion a] :
    Epi (pushforwardStructureSheafModuleToComp i a) := by
  have : (Scheme.Modules.pushforward a).PreservesEpimorphisms := by
    show (RingedSpaceModuleAdjunction.modulePushforward
      a.toLRSHom.toShHom).PreservesEpimorphisms
    infer_instance
  have : Epi i.structureSheafModuleMap := epi_structureSheafModuleMap i
  have : IsIso ((Scheme.Modules.pushforwardComp i a).hom.app Z.structureSheafModule) :=
    ⟨⟨(Scheme.Modules.pushforwardComp i a).inv.app Z.structureSheafModule, by simp, by simp⟩⟩
  exact epi_comp _ _

/-! ### The structure-sheaf sequence of the pushout -/

/-- The pair of canonical structure-sheaf maps from the pushout of two closed immersions to its
two pieces, as a map into their biproduct.  This is the first map of the short exact sequence
of [Stacks Project, Tag 0B7M]. -/
def pushoutStructureSheafModuleToBiprod {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (pushout i j).structureSheafModule ⟶
      (pushout.inl i j).pushforwardStructureSheafModule ⊞
        (pushout.inr i j).pushforwardStructureSheafModule :=
  biprod.lift (pushout.inl i j).structureSheafModuleMap (pushout.inr i j).structureSheafModuleMap

/-- The difference of the two restriction maps from the pieces of the pushout of two closed
immersions to their common closed subscheme.  This is the second map of the short exact
sequence of [Stacks Project, Tag 0B7M]. -/
def pushoutBiprodToIntersection {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (pushout.inl i j).pushforwardStructureSheafModule ⊞
        (pushout.inr i j).pushforwardStructureSheafModule ⟶
      (i ≫ pushout.inl i j).pushforwardStructureSheafModule :=
  biprod.desc (pushforwardStructureSheafModuleToComp i (pushout.inl i j))
    (-(pushforwardStructureSheafModuleToComp j (pushout.inr i j) ≫
      (Scheme.Modules.pushforwardCongr (pushout.condition (f := i) (g := j)).symm).hom.app _))

/-- **[Stacks, Tag 0B7M].** For two closed immersions `i : Z ⟶ X` and `j : Z ⟶ Y`, the
canonical sequence

`0 ⟶ 𝒪_(Y ⨿_Z X) ⟶ a_* 𝒪_X ⊕ b_* 𝒪_Y ⟶ c_* 𝒪_Z ⟶ 0`

of modules over the structure sheaf of the pushout is short exact, where `a` and `b` are the
two canonical maps into the pushout and `c = a ∘ i = b ∘ j`. -/
@[stacks 0B7M "the short exact sequence"]
theorem pushout_structureSheafModule_shortExact {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ zero : pushoutStructureSheafModuleToBiprod i j ≫ pushoutBiprodToIntersection i j = 0,
      (ShortComplex.mk (pushoutStructureSheafModuleToBiprod i j)
        (pushoutBiprodToIntersection i j) zero).ShortExact := by
  have : IsFinite j := IsFinite.instOfIsClosedImmersion j
  have hp := isPullback_pushforwardStructureSheafModule i j (pushout.inl i j) (pushout.inr i j)
    ⟨⟨pushout.condition⟩, ⟨pushoutIsPushout i j⟩⟩
  have zero : pushoutStructureSheafModuleToBiprod i j ≫ pushoutBiprodToIntersection i j = 0 :=
    hp.toCommSq.shortComplex'.zero
  refine ⟨zero, .mk' hp.exact_shortComplex' hp.mono_shortComplex'_f ?_⟩
  have hfac : biprod.inl ≫ pushoutBiprodToIntersection i j =
      pushforwardStructureSheafModuleToComp i (pushout.inl i j) := by
    simp [pushoutBiprodToIntersection]
  have := epi_pushforwardStructureSheafModuleToComp i (pushout.inl i j)
  exact epi_of_epi_fac hfac

end AlgebraicGeometry

end
