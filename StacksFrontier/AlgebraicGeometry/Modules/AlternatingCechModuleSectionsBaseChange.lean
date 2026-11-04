module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Base change of the sections of a quasi-coherent module

Let `g : X' ⟶ X` be a morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module. The unit
of the pullback--pushforward adjunction gives, over every open `W` of `X`, a canonical comparison
map `Γ(F, W) → Γ(g^*F, g ⁻¹ᵁ W)`. This file shows that when `W` and its preimage are both affine
this comparison exhibits the sections of the pullback as the base change of the sections:
`Γ(g^*F, g ⁻¹ᵁ W) = Γ(X', g ⁻¹ᵁ W) ⊗_{Γ(X, W)} Γ(F, W)`.

## Main definitions

* `Stacks.Cech.pullbackSections` is the canonical comparison map on sections, and
  `Stacks.Cech.pullbackSectionsₗ` is its linear form for the module structures recorded by
  `Stacks.Cech.algebraPullbackSections`, `Stacks.Cech.modulePullbackSections` and
  `Stacks.Cech.isScalarTowerPullbackSections`.

## Main results

* `Stacks.Cech.isBaseChange_pullbackSectionsₗ`: the comparison map is a base change.

## Implementation notes

The proof reduces the statement to the affine case by passing to the spectra of the two rings of
sections. Writing `R = Γ(X, W)` and `S = Γ(X', g ⁻¹ᵁ W)`, the square formed by
`IsAffineOpen.fromSpec` for `W` and for `g ⁻¹ᵁ W` and by `Spec.map (g.app W)` commutes, which is
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`. The canonical comparison maps compose
along that square: the auxiliary `can` packages "unit followed by restriction", `can_comp` is the
cocycle identity for a composition of morphisms (deduced from
`CategoryTheory.unit_conjugateEquiv` and
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`) and `can_congr` compares the
two factorizations of the diagonal.

Along `IsAffineOpen.fromSpec` the comparison is bijective, because the unit of the *restriction*
adjunction is a restriction map of `F` and `fromSpec` has image exactly `W`; this is
`can_fromSpec_bijective`, and `can_fromSpec_smul` records its linearity over `R`. The remaining,
substantive input is the affine statement, Stacks Tag 01I9: pullback along `Spec.map φ` is
extension of scalars, in the normalized form
`AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen`, repackaged here as
`affinePullbackSectionsIso` together with `affinePullbackSectionsIso_hom_one_tmul`. The two
descriptions are glued by `IsBaseChange.iff_of_equiv_comm`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace Stacks.Cech

/-! ### The canonical comparison on sections -/

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (F : X.Modules)

/-- The canonical map on sections induced by a morphism of schemes: the component at `W` of
the unit of the pullback--pushforward adjunction. -/
def pullbackSections (W : X.Opens) :
    Γ(F, W) ⟶ Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app W

/-- The canonical comparison is compatible with restriction. -/
theorem map_comp_pullbackSections {V W : X.Opens} (h : V ≤ W) :
    F.presheaf.map (homOfLE h).op ≫ pullbackSections g F V =
      pullbackSections g F W ≫ ((Scheme.Modules.pullback g).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono g h)).op :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).mapPresheaf.naturality
    (homOfLE h).op

/-- The elementwise form of `Stacks.Cech.map_comp_pullbackSections`. -/
theorem pullbackSections_map {V W : X.Opens} (h : V ≤ W) (s : Γ(F, W)) :
    pullbackSections g F V (F.presheaf.map (homOfLE h).op s) =
      ((Scheme.Modules.pullback g).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono g h)).op (pullbackSections g F W s) :=
  congr($(map_comp_pullbackSections g F h) s)

/-- The canonical comparison is semilinear: it carries the action of `r` to the action of
`g.app W r`. -/
theorem pullbackSections_smul (W : X.Opens) (r : Γ(X, W)) (s : Γ(F, W)) :
    pullbackSections g F W (r • s) = g.app W r • pullbackSections g F W s :=
  Scheme.Modules.Hom.app_smul _ r s

/-! ### The comparison as a base change of modules -/

/-- The `Γ(X, W)`-algebra structure on `Γ(X', g ⁻¹ᵁ W)` given by `g.app W`. -/
@[instance_reducible]
def algebraPullbackSections (W : X.Opens) : Algebra Γ(X, W) Γ(X', g ⁻¹ᵁ W) :=
  (g.app W).hom.toAlgebra

/-- The `Γ(X, W)`-module structure on the sections of the pullback over `g ⁻¹ᵁ W`. -/
@[instance_reducible]
def modulePullbackSections (W : X.Opens) :
    Module Γ(X, W) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
  Module.compHom _ (g.app W).hom

/-- The scalar tower `Γ(X, W) → Γ(X', g ⁻¹ᵁ W) → Γ(g^*F, g ⁻¹ᵁ W)`. -/
theorem isScalarTowerPullbackSections (W : X.Opens) :
    letI := algebraPullbackSections g W
    letI := modulePullbackSections g F W
    IsScalarTower Γ(X, W) Γ(X', g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
  let := algebraPullbackSections g W
  let := modulePullbackSections g F W
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The canonical comparison on sections, as a `Γ(X, W)`-linear map. -/
def pullbackSectionsₗ (W : X.Opens) :
    letI := modulePullbackSections g F W
    Γ(F, W) →ₗ[Γ(X, W)] Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
  letI := modulePullbackSections g F W
  { toFun := pullbackSections g F W
    map_add' := map_add _
    map_smul' := pullbackSections_smul g F W }

/-! ### Auxiliary material: the canonical map on sections -/

/-- The canonical map on sections from `U` to an open `V ≤ h ⁻¹ᵁ U`: the unit of the
pullback--pushforward adjunction at `U`, followed by restriction to `V`. -/
private def can {A B : Scheme.{u}} (h : A ⟶ B) (N : B.Modules) (U : B.Opens) (V : A.Opens)
    (hV : V ≤ h ⁻¹ᵁ U) (m : Γ(N, U)) : Γ((Scheme.Modules.pullback h).obj N, V) :=
  ((Scheme.Modules.pullback h).obj N).presheaf.map (homOfLE hV).op
    (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app N).app U m)

/-- The canonical map on sections, as a morphism of abelian groups. -/
private def canHom {A B : Scheme.{u}} (h : A ⟶ B) (N : B.Modules) (U : B.Opens) (V : A.Opens)
    (hV : V ≤ h ⁻¹ᵁ U) : Γ(N, U) ⟶ Γ((Scheme.Modules.pullback h).obj N, V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app N).app U ≫
    ((Scheme.Modules.pullback h).obj N).presheaf.map (homOfLE hV).op

private theorem can_add {A B : Scheme.{u}} (h : A ⟶ B) (N : B.Modules) (U : B.Opens)
    (V : A.Opens) (hV : V ≤ h ⁻¹ᵁ U) (m m' : Γ(N, U)) :
    can h N U V hV (m + m') = can h N U V hV m + can h N U V hV m' :=
  map_add (ConcreteCategory.hom (canHom h N U V hV)) m m'

private theorem can_smul {A B : Scheme.{u}} (h : A ⟶ B) (N : B.Modules) (U : B.Opens)
    (V : A.Opens) (hV : V ≤ h ⁻¹ᵁ U) (r : Γ(B, U)) (m : Γ(N, U)) :
    can h N U V hV (r • m) = h.appLE U V hV r • can h N U V hV m := by
  rw [can, show ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app N).app U (r • m) = _ from
    pullbackSections_smul h N U r m]
  exact Scheme.Modules.map_smul _ (homOfLE hV) (h.app U r) _

private theorem can_self {A B : Scheme.{u}} (h : A ⟶ B) (N : B.Modules) (U : B.Opens)
    (hV : h ⁻¹ᵁ U ≤ h ⁻¹ᵁ U) (m : Γ(N, U)) :
    can h N U (h ⁻¹ᵁ U) hV m =
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app N).app U m := by
  have h1 : ((Scheme.Modules.pullback h).obj N).presheaf.map (homOfLE hV).op = 𝟙 _ := by
    rw [show homOfLE hV = 𝟙 _ from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  exact congr($h1 _)

/-- The units of the pullback--pushforward adjunctions compose, along the identification
`Scheme.Modules.pullbackComp`. -/
private theorem unitComp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (N : C.Modules)
    (U : C.Opens) (m : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp p q).hom.app N).app ((p ≫ q) ⁻¹ᵁ U)
      ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          ((Scheme.Modules.pullback q).obj N)).app (q ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app U m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app N).app U m := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q))
    (Scheme.Modules.pullbackComp p q).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have key : ((Scheme.Modules.pullbackComp p q).inv.app N).app ((p ≫ q) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app N).app U m) =
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          ((Scheme.Modules.pullback q).obj N)).app (q ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app U m) :=
    (congr($(congrArg (fun t => Scheme.Modules.Hom.app t U) h) m)).symm
  have hid : ((Scheme.Modules.pullbackComp p q).inv.app N).app ((p ≫ q) ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp p q).hom.app N).app ((p ≫ q) ⁻¹ᵁ U) = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rw [← key]
  exact congr($hid _)

private theorem can_comp_aux {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (N : C.Modules)
    (U : C.Opens) (V : B.Opens) (hV : V ≤ q ⁻¹ᵁ U) (T : A.Opens) (hT : T ≤ p ⁻¹ᵁ V)
    (hPQ : T ≤ (p ≫ q) ⁻¹ᵁ U) (z : Γ((Scheme.Modules.pullback q).obj N, q ⁻¹ᵁ U)) :
    ((Scheme.Modules.pullbackComp p q).hom.app N).app T
        (can p ((Scheme.Modules.pullback q).obj N) V T hT
          (((Scheme.Modules.pullback q).obj N).presheaf.map (homOfLE hV).op z)) =
      ((Scheme.Modules.pullback (p ≫ q)).obj N).presheaf.map (homOfLE hPQ).op
        (((Scheme.Modules.pullbackComp p q).hom.app N).app ((p ≫ q) ⁻¹ᵁ U)
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
            ((Scheme.Modules.pullback q).obj N)).app (q ⁻¹ᵁ U)) z)) := by
  have hA : (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          ((Scheme.Modules.pullback q).obj N)).app V)
        (((Scheme.Modules.pullback q).obj N).presheaf.map (homOfLE hV).op z) =
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)).presheaf.map
        ((Opens.map p.base).map (homOfLE hV)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          ((Scheme.Modules.pullback q).obj N)).app (q ⁻¹ᵁ U)) z) :=
    pullbackSections_map p _ hV z
  have hB : ∀ y : Γ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N),
        p ⁻¹ᵁ (q ⁻¹ᵁ U)),
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)).presheaf.map
          (homOfLE hT).op
        (((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)).presheaf.map
          ((Opens.map p.base).map (homOfLE hV)).op y) =
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)).presheaf.map
        (homOfLE hPQ).op y := by
    intro y
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
      show homOfLE hT ≫ (Opens.map p.base).map (homOfLE hV) = homOfLE hPQ from
        Subsingleton.elim _ _]
    rfl
  have hC : ∀ y : Γ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N),
        p ⁻¹ᵁ (q ⁻¹ᵁ U)),
      ((Scheme.Modules.pullbackComp p q).hom.app N).app T
        (((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)).presheaf.map
          (homOfLE hPQ).op y) =
      ((Scheme.Modules.pullback (p ≫ q)).obj N).presheaf.map (homOfLE hPQ).op
        (((Scheme.Modules.pullbackComp p q).hom.app N).app ((p ≫ q) ⁻¹ᵁ U) y) := fun y =>
    congr($(((Scheme.Modules.pullbackComp p q).hom.app N).mapPresheaf.naturality
      (homOfLE hPQ).op) y)
  rw [can, hA]
  exact (congrArg (fun w => ((Scheme.Modules.pullbackComp p q).hom.app N).app T w)
    (hB _)).trans (hC _)

/-- The canonical maps on sections compose, along the identification
`Scheme.Modules.pullbackComp`. -/
private theorem can_comp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (N : C.Modules)
    (U : C.Opens) (V : B.Opens) (hV : V ≤ q ⁻¹ᵁ U) (T : A.Opens) (hT : T ≤ p ⁻¹ᵁ V)
    (hPQ : T ≤ (p ≫ q) ⁻¹ᵁ U) (m : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp p q).hom.app N).app T
        (can p ((Scheme.Modules.pullback q).obj N) V T hT (can q N U V hV m)) =
      can (p ≫ q) N U T hPQ m :=
  (can_comp_aux p q N U V hV T hT hPQ
      (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app U m)).trans
    (congrArg (fun y => ((Scheme.Modules.pullback (p ≫ q)).obj N).presheaf.map (homOfLE hPQ).op y)
      (unitComp p q N U m))

/-- The canonical maps on sections along equal morphisms agree, along the identification
`Scheme.Modules.pullbackCongr`. -/
private theorem can_congr {A C : Scheme.{u}} {h₁ h₂ : A ⟶ C} (hf : h₁ = h₂) (N : C.Modules)
    (U : C.Opens) (T : A.Opens) (hT₁ : T ≤ h₁ ⁻¹ᵁ U) (hT₂ : T ≤ h₂ ⁻¹ᵁ U) (m : Γ(N, U)) :
    ((Scheme.Modules.pullbackCongr hf).hom.app N).app T (can h₁ N U T hT₁ m) =
      can h₂ N U T hT₂ m := by
  subst hf
  rw [show hT₂ = hT₁ from Subsingleton.elim _ _]
  simp [Scheme.Modules.pullbackCongr, can]

private theorem appLE_fromSpec {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(Y, U)).Opens) (hV : V ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U V hV =
      (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (Spec Γ(Y, U)).presheaf.map (Opens.leTop V).op := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← op_comp,
    show homOfLE hV ≫ eqToHom hU.fromSpec_preimage_self = Opens.leTop V from
      Subsingleton.elim _ _]

/-- Over an affine open, the canonical map on sections along `IsAffineOpen.fromSpec` is linear
over the ring of sections. -/
private theorem can_fromSpec_smul {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) (V : (Spec Γ(Y, U)).Opens) (hV : V ≤ hU.fromSpec ⁻¹ᵁ U)
    (r : Γ(Y, U)) (m : Γ(N, U)) :
    can hU.fromSpec N U V hV (r • m) = r • can hU.fromSpec N U V hV m := by
  rw [can_smul, Scheme.Modules.smul_Spec_def, congr($(appLE_fromSpec hU V hV) r)]
  rfl

/-- The unit of the restriction adjunction and the unit of the pullback--pushforward adjunction
agree, along `Scheme.Modules.restrictFunctorIsoPullback`. -/
private theorem restrict_unit {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (N : Z.Modules) (U : Z.Opens) (m : Γ(N, U)) :
    (((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N).app (f ⁻¹ᵁ U))
        (N.presheaf.map (homOfLE (f.image_preimage_le U)).op m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) N
  exact congr($(congrArg (fun t => Scheme.Modules.Hom.app t U) h) m)

/-- Restriction of sections along `V ≤ V'` is bijective when also `V' ≤ V`. -/
private theorem bijective_map_homOfLE {Y : Scheme.{u}} (N : Y.Modules) {V V' : Y.Opens}
    (h : V ≤ V') (h' : V' ≤ V) : Function.Bijective (N.presheaf.map (homOfLE h).op) := by
  rw [show homOfLE h = eqToHom (le_antisymm h h') from Subsingleton.elim _ _]
  exact ConcreteCategory.bijective_of_isIso _

/-- Over an affine open `U`, the canonical map on sections along `IsAffineOpen.fromSpec`
identifies `Γ(N, U)` with the global sections of the pullback. -/
private theorem can_fromSpec_bijective {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    Function.Bijective (can hU.fromSpec N U ⊤ hV) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have himg : hU.fromSpec ''ᵁ (hU.fromSpec ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec, inf_idem]
  have h1 : Function.Bijective
      (N.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op) :=
    bijective_map_homOfLE N _ himg.ge
  have h2 : Function.Bijective
      (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N).app
        (hU.fromSpec ⁻¹ᵁ U)) := ConcreteCategory.bijective_of_isIso _
  have h3 : Function.Bijective
      (((Scheme.Modules.pullback hU.fromSpec).obj N).presheaf.map (homOfLE hV).op) :=
    bijective_map_homOfLE _ hV hU.fromSpec_preimage_self.le
  have hcomp : ∀ m : Γ(N, U), can hU.fromSpec N U ⊤ hV m =
      ((Scheme.Modules.pullback hU.fromSpec).obj N).presheaf.map (homOfLE hV).op
        ((((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N).app
          (hU.fromSpec ⁻¹ᵁ U))
          (N.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op m)) := by
    intro m
    rw [restrict_unit, can]
  rw [show (can hU.fromSpec N U ⊤ hV) = _ from funext hcomp]
  exact h3.comp (h2.comp h1)

/-- Over an affine open `U`, the canonical map on sections along `IsAffineOpen.fromSpec` as a
linear equivalence over the ring of sections. -/
private def canFromSpecₗ {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    Γ(N, U) ≃ₗ[Γ(Y, U)] Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
  LinearEquiv.ofBijective
    { toFun := can hU.fromSpec N U ⊤ hV
      map_add' := can_add hU.fromSpec N U ⊤ hV
      map_smul' := can_fromSpec_smul N hU ⊤ hV }
    (can_fromSpec_bijective N hU hV)

/-! ### The affine case -/

/-- Global sections of the pullback of a quasi-coherent module along a morphism of affine
schemes are the extension of scalars of its global sections. -/
noncomputable def affinePullbackSectionsIso (R S : CommRingCat.{u}) (f : R ⟶ S)
    (G : (Spec R).Modules) [G.IsQuasicoherent] :
    (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj G) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map f)).obj G) := by
  let eG : tilde ((moduleSpecΓFunctor (R := R)).obj G) ≅ G :=
    @CategoryTheory.asIso (Spec R).Modules (inferInstance : Category (Spec R).Modules)
      _ _ (Scheme.Modules.fromTildeΓ G) (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)
  let eT := (pullbackTildeIso R S f).app (moduleSpecΓFunctor.obj G)
  let e := (Scheme.Modules.pullback (Spec.map f)).mapIso eG.symm ≪≫ eT
  exact (tilde.isoTop ((ModuleCat.extendScalars f.hom).obj
      ((moduleSpecΓFunctor (R := R)).obj G))) ≪≫
    (moduleSpecΓFunctor (R := S)).mapIso e.symm

/-- The isomorphism `affinePullbackSectionsIso` sends `1 ⊗ₜ m` to the image of the global
section `m` under the unit of the adjunction between pullback and pushforward along
`Spec.map f`. -/
lemma affinePullbackSectionsIso_hom_one_tmul (R S : CommRingCat.{u})
    (f : R ⟶ S) (G : (Spec R).Modules) [G.IsQuasicoherent]
    (m : (moduleSpecΓFunctor (R := R)).obj G) :
    (affinePullbackSectionsIso R S f G).hom
        ((1 : S) ⊗ₜ[R, f.hom] m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app G).val.app
        (.op ⊤) m := by
  let M := (moduleSpecΓFunctor (R := R)).obj G
  let eG : tilde M ≅ G :=
    @CategoryTheory.asIso (Spec R).Modules (inferInstance : Category (Spec R).Modules)
      _ _ (Scheme.Modules.fromTildeΓ G)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)
  let eT := (pullbackTildeIso R S f).app M
  let e := (Scheme.Modules.pullback (Spec.map f)).mapIso eG.symm ≪≫ eT
  have hΓ' (x : M) :
      (eG.hom.app ⊤) (tilde.toOpen M ⊤ x) = x := by
    have hx := congrArg (fun g => g.hom x)
      (Scheme.Modules.toOpen_fromTildeΓ_app G ⊤)
    have hx' := by simpa [ModuleCat.hom_comp] using hx
    exact hx'
  have hT : (eT.inv.app ⊤)
      (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
        ((1 : S) ⊗ₜ[R, f.hom] m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app (tilde M)).app
        ⊤ (tilde.toOpen M ⊤ m) := by
    apply (ConcreteCategory.bijective_of_isIso (eT.hom.app ⊤)).injective
    let z := tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
      ((1 : S) ⊗ₜ[R, f.hom] m)
    let w := ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app
      (tilde M)).app ⊤ (tilde.toOpen M ⊤ m)
    have hi' := congrArg (fun q => q.hom z) (congrArg (fun q => q.app ⊤) eT.inv_hom_id)
    have hleft : (eT.hom.app ⊤) ((eT.inv.app ⊤) z) = z := by
      simp only [Scheme.Modules.Hom.comp_app,
        Scheme.Modules.Hom.id_app] at hi'
      exact hi'
    have hright : (eT.hom.app ⊤) w = z := by
      change ((pullbackTildeIso R S f).hom.app M).val.app
        (.op ⊤) _ = _
      exact pullbackTildeIso_hom_app_unit_toOpen R S f M m
    exact hleft.trans hright.symm
  change (moduleSpecΓFunctor (R := S)).map e.symm.hom
      ((tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
        ((1 : S) ⊗ₜ[R, f.hom] m)) = _
  rw [tilde.isoTop_hom]
  change ((Scheme.Modules.pullback (Spec.map f)).map eG.hom).app ⊤
      ((eT.inv.app ⊤)
        (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
          ((1 : S) ⊗ₜ[R, f.hom] m))) = _
  rw [hT]
  let a : Γ((𝟭 (Spec R).Modules).obj (tilde M), ⊤) := tilde.toOpen M ⊤ m
  have hn' := congrArg (fun q => (q.app ⊤) a)
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.naturality eG.hom)
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at hn'
  simp only [AddCommGrpCat.comp_apply, Functor.id_map] at hn'
  have ha : (eG.hom.app ⊤) a = m := by
    simpa [a] using hΓ' m
  rw [ha] at hn'
  exact hn'.symm

/-! ### The main theorem -/

/-- **The sections of the pullback of a quasi-coherent module over an affine open with affine
preimage are the base change of the sections.** -/
theorem isBaseChange_pullbackSectionsₗ [F.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen (g ⁻¹ᵁ W)) :
    letI := algebraPullbackSections g W
    letI := modulePullbackSections g F W
    letI := isScalarTowerPullbackSections g F W
    IsBaseChange Γ(X', g ⁻¹ᵁ W) (pullbackSectionsₗ g F W) := by
  let _ := algebraPullbackSections g W
  let _ := modulePullbackSections g F W
  let _ := isScalarTowerPullbackSections g F W
  have hsq : Spec.map (g.app W) ≫ hW.fromSpec = hW'.fromSpec ≫ g := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec g hW hW' (le_refl (g ⁻¹ᵁ W))
    rwa [Scheme.Hom.appLE_eq_app] at h
  have h_a : (⊤ : (Spec Γ(X, W)).Opens) ≤ hW.fromSpec ⁻¹ᵁ W :=
    hW.fromSpec_preimage_self.ge
  have h_c : (⊤ : (Spec Γ(X', g ⁻¹ᵁ W)).Opens) ≤ hW'.fromSpec ⁻¹ᵁ (g ⁻¹ᵁ W) :=
    hW'.fromSpec_preimage_self.ge
  have h_b : (⊤ : (Spec Γ(X', g ⁻¹ᵁ W)).Opens) ≤
      Spec.map (g.app W) ⁻¹ᵁ (⊤ : (Spec Γ(X, W)).Opens) := le_top
  have hPQ : (⊤ : (Spec Γ(X', g ⁻¹ᵁ W)).Opens) ≤
      (Spec.map (g.app W) ≫ hW.fromSpec) ⁻¹ᵁ W := Scheme.Hom.preimage_mono _ h_a
  let aₗ := canFromSpecₗ F hW h_a
  let cₗ := canFromSpecₗ ((Scheme.Modules.pullback g).obj F) hW' h_c
  let _ : Module Γ(X, W) Γ((Scheme.Modules.pullback (Spec.map (g.app W))).obj
      ((Scheme.Modules.pullback hW.fromSpec).obj F), ⊤) :=
    Module.compHom _ (g.app W).hom
  let _ : IsScalarTower Γ(X, W) Γ(X', g ⁻¹ᵁ W)
      Γ((Scheme.Modules.pullback (Spec.map (g.app W))).obj
        ((Scheme.Modules.pullback hW.fromSpec).obj F), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let aff := affinePullbackSectionsIso Γ(X, W) Γ(X', g ⁻¹ᵁ W) (g.app W)
    ((Scheme.Modules.pullback hW.fromSpec).obj F)
  let affE : (Γ(X', g ⁻¹ᵁ W) ⊗[Γ(X, W)] Γ((Scheme.Modules.pullback hW.fromSpec).obj F, ⊤))
      ≃ₗ[Γ(X', g ⁻¹ᵁ W)] Γ((Scheme.Modules.pullback (Spec.map (g.app W))).obj
        ((Scheme.Modules.pullback hW.fromSpec).obj F), ⊤) := aff.toLinearEquiv
  let bₗ : Γ((Scheme.Modules.pullback hW.fromSpec).obj F, ⊤) →ₗ[Γ(X, W)]
      Γ((Scheme.Modules.pullback (Spec.map (g.app W))).obj
        ((Scheme.Modules.pullback hW.fromSpec).obj F), ⊤) :=
    (affE.toLinearMap.restrictScalars Γ(X, W)).comp
      (TensorProduct.mk Γ(X, W) Γ(X', g ⁻¹ᵁ W)
        Γ((Scheme.Modules.pullback hW.fromSpec).obj F, ⊤) 1)
  have hbc : IsBaseChange Γ(X', g ⁻¹ᵁ W) bₗ :=
    IsBaseChange.of_equiv affE fun _ => rfl
  have hbnorm : ∀ y, bₗ y = can (Spec.map (g.app W))
      ((Scheme.Modules.pullback hW.fromSpec).obj F) ⊤ ⊤ h_b y := fun y =>
    (affinePullbackSectionsIso_hom_one_tmul Γ(X, W) Γ(X', g ⁻¹ᵁ W) (g.app W)
        ((Scheme.Modules.pullback hW.fromSpec).obj F) y).trans
      (can_self (Spec.map (g.app W)) ((Scheme.Modules.pullback hW.fromSpec).obj F) ⊤ h_b y).symm
  let k₂ := (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullbackComp (Spec.map (g.app W)) hW.fromSpec).app F)).toLinearEquiv
  let kc := (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullbackCongr hsq).app F)).toLinearEquiv
  let k₁ := (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullbackComp hW'.fromSpec g).app F)).toLinearEquiv
  let eN : Γ((Scheme.Modules.pullback (Spec.map (g.app W))).obj
        ((Scheme.Modules.pullback hW.fromSpec).obj F), ⊤) ≃ₗ[Γ(X', g ⁻¹ᵁ W)]
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
    (k₂.trans (kc.trans k₁.symm)).trans cₗ.symm
  refine (IsBaseChange.iff_of_equiv_comm aₗ.symm eN (LinearMap.ext fun y => ?_)).mp hbc
  obtain ⟨m, rfl⟩ := aₗ.surjective y
  have hL : ((Scheme.Modules.pullbackComp hW'.fromSpec g).hom.app F).app ⊤
        (can hW'.fromSpec ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ W) ⊤ h_c
          (pullbackSections g F W m)) =
      can (hW'.fromSpec ≫ g) F W ⊤ h_c m := by
    rw [show (pullbackSections g F W m) = can g F W (g ⁻¹ᵁ W) le_rfl m from
      (can_self g F W le_rfl m).symm]
    exact can_comp hW'.fromSpec g F W (g ⁻¹ᵁ W) le_rfl ⊤ h_c h_c m
  have hR : ((Scheme.Modules.pullbackCongr hsq).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp (Spec.map (g.app W)) hW.fromSpec).hom.app F).app ⊤
          (can (Spec.map (g.app W)) ((Scheme.Modules.pullback hW.fromSpec).obj F) ⊤ ⊤ h_b
            (can hW.fromSpec F W ⊤ h_a m))) = can (hW'.fromSpec ≫ g) F W ⊤ h_c m := by
    rw [can_comp (Spec.map (g.app W)) hW.fromSpec F W ⊤ h_a ⊤ h_b hPQ m]
    exact can_congr hsq F W ⊤ hPQ h_c m
  have h1 : k₁ (cₗ (pullbackSections g F W m)) = kc (k₂ (bₗ (aₗ m))) := by
    rw [hbnorm]
    exact hL.trans hR.symm
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, aₗ.symm_apply_apply]
  change pullbackSections g F W m = cₗ.symm (k₁.symm (kc (k₂ (bₗ (aₗ m)))))
  rw [← h1]
  exact (Eq.trans (congrArg (fun z => cₗ.symm z)
    (k₁.symm_apply_apply (cₗ (pullbackSections g F W m)))) (cₗ.symm_apply_apply _)).symm

end Stacks.Cech

end

end
