module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The right-hand end of the conormal sequence of an immersion

For an immersion `i : Z ⟶ X` of schemes over `S`, [Stacks, Tag 01UZ] asserts that
`𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact. This file proves the right-hand end:
the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 01UV] is an epimorphism.

## Main results

* `Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap`: the canonical map
  `i^*Ω_{X/S} ⟶ Ω_{Z/S}` is an epimorphism as soon as `i` is surjective on stalks.
* `Stacks.ConormalSequenceRight.differentialsMapOver_epi`: the same for an immersion, which
  is the hypothesis [Stacks, Tag 01UZ] states it under. This is the assertion labelled
  *exactness at the right term*.
* `Stacks.ConormalSequenceRight.relativeDifferentials_hom_ext`: a morphism out of
  `Ω_{Z/S}` is determined by its values on the universal differentials of local sections.
* `Stacks.ConormalSequenceRight.exists_restrict_eq_app`: near every point, a local section
  of `𝒪_Z` is the pullback of a local section of `𝒪_X`.
* `Stacks.ConormalSequenceRight.app_d_app_eq_of_comp_eq`: two morphisms out of `Ω_{Z/S}`
  that agree after composition with the canonical map agree on the universal differential of
  every pulled-back section.
* `Stacks.ConormalSequenceRight.conormalDifferential`: the canonical map
  `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` induced by `d_{X/S}`. This is the *first arrow* of
  [Stacks, Tag 01UZ].
* `Stacks.ConormalSequenceRight.conormalComparison_comp_conormalDifferential` and
  `Stacks.ConormalSequenceRight.conormalDifferential_unique`: the first arrow is pinned down
  by its transpose, the map sending a section `f` of the ideal sheaf to `1 ⊗ d f`.
* `Stacks.ConormalSequenceRight.conormalDifferential_comp_relativeDifferentialsMap`: the two
  arrows form a complex, `𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S}` composing to zero.
* `Stacks.ConormalSequenceRight.conormalShortComplex` and
  `Stacks.ConormalSequenceRight.epi_conormalShortComplex_g`: that complex, packaged, and the
  fact that it ends in zero.

## Route

Surjectivity is *not* proved here by exhibiting local preimages, and in particular the
affine-local description of the sheaf of differentials is not used. Epimorphy is read off the
universal property instead, in three steps.

1. `Epi` is, by definition, left-cancellation. So let `g, g' : Ω_{Z/S} ⟶ F` satisfy
   `b ≫ g = b ≫ g'`, where `b` is the canonical map.
2. Transposing that equation across the pullback–pushforward adjunction and evaluating it on
   the universal differential of a section `x` of `𝒪_X` over an open `U` — which is exactly
   what `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d` computes — shows that
   `g` and `g'` agree on `d(i^♯ x)` over `i⁻¹U`. That is `app_d_app_eq_of_comp_eq`.
3. The universal property of `Ω_{Z/S}` (`SheafOfModules.universalDerivation_isUniversal`)
   says a morphism out of it is determined by its values on the universal differentials of
   *all* local sections of `𝒪_Z`, not only the pulled-back ones. The gap between the two is
   closed locally: an immersion is surjective on stalks, so every local section of `𝒪_Z` has,
   near each point of its domain, the same germ as a pulled-back one, hence agrees with one on
   a smaller open. Both values are then sections of the sheaf `F` which agree on a cover, so
   they are equal.

The only geometric input is therefore surjectivity on stalks, which is the field
`AlgebraicGeometry.SurjectiveOnStalks.stalkMap_surjective` that `IsImmersion` carries through
`IsPreimmersion`. Neither local closedness nor the embedding property of the immersion is used,
and the statement is proved at that weaker hypothesis before being specialized.

## Route for the first arrow

An immersion factors as the closed immersion `j = i.liftCoborder` into the open subscheme
`W = i.coborderRange` followed by the inclusion `ι : W ⟶ X`, and `𝒞_{Z/X}` is `j^*ℐ` for the
defining ideal sheaf `ℐ ⊆ 𝒪_W` of `j`. A morphism `j^*ℐ ⟶ F` is the same thing as a morphism
`ℐ ⟶ j_*F`, so the arrow is produced from its transpose, which is written down on sections.

On an open `V ⊆ W` the transpose sends `f ∈ ℐ(V)` to the image of `d_{W/S} f` under the unit
`Ω_{W/S} ⟶ j_* j^* Ω_{W/S}`, that is, to `1 ⊗ d f`. This assignment is additive because
`d_{W/S}` is, and it is `𝒪_W(V)`-linear although `d_{W/S}` is not: the Leibniz rule produces the
extra term `f · d a`, and `f` acts by zero on sections of a pushforward along `j` precisely
because `ℐ` is the kernel of `𝒪_W ⟶ j_*𝒪_Z`. That is
`Stacks.ConormalSequenceRight.derivation_d_mul_of_smul_eq_zero` together with
`Stacks.ConormalSequenceRight.smul_restrictScalars_eq_zero`, and the two are packaged as
`Stacks.ConormalSequenceRight.idealDerivationHom`.

The target is then moved from `j^*Ω_{W/S}` to `i^*Ω_{X/S}`: the canonical map
`ι^*Ω_{X/S} ⟶ Ω_{W/S}` of an open immersion is an isomorphism
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_id_base`), and pulling it back
along `j` and composing with the pseudofunctoriality isomorphism `j^*ι^* ≅ (j ≫ ι)^* = i^*`
gives `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`.

## Vocabulary

The statement of [Stacks, Tag 01UZ] is phrased in terms of the sheaf of relative differentials,
its universal derivation and the functorial map between sheaves of differentials. Over library
names these are:

* the module of differentials of the inverse-image structure map of `p`, which is
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials p`
  (`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/Relative.lean:45`), defined in exactly
  that way;
* its universal derivation, `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation` (same
  file, line 50);
* the functorial map of differentials, `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap`
  (`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/Functoriality.lean:122`). This is the
  second arrow of the sequence of Tag 01UZ, and the registration below records it under the
  label *the functorial second arrow*.

The two arguments beyond `i`, `p` and `i ≫ p` are the base morphism of the commutative square
and the proof that it commutes, and by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_eq_of_comm` the map does not depend on
either, so the reference statement's choice `(𝟙 S, by simp)` is not a restriction.

No hypothesis beyond those of the reference statement is used by either labelled assertion.

## What is not done here

[Stacks, Tag 01UZ] carries five labelled assertions and this file discharges three of them.

* **Exactness at the middle term is untouched.** The two arrows are known to compose to zero,
  but nothing here identifies the image of the first with the kernel of the second, and nothing
  here proves the first arrow is a monomorphism.
* **The epimorphism is not identified with a cokernel or with local surjectivity.** The proof
  gives left-cancellation directly; it does not produce a local preimage of a given section of
  `Ω_{Z/S}`, so it says nothing about the sections of `Ω_{Z/S}` over any particular open.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.ConormalSequenceRight

/-- A local section of the structure sheaf of the source of a morphism surjective on stalks
agrees, on a neighbourhood of any point of its domain, with the pullback of a local section
upstairs. -/
theorem exists_restrict_eq_app {Z X : Scheme.{u}} (i : Z ⟶ X)
    [SurjectiveOnStalks i] {V : Z.Opens} (t : Γ(Z, V)) (z : Z) (hz : z ∈ V) :
    ∃ (U : X.Opens) (W : Z.Opens) (hWV : W ≤ V) (hWU : W ≤ i ⁻¹ᵁ U) (x : Γ(X, U)),
      z ∈ W ∧
        Z.presheaf.map (homOfLE hWU).op ((i.app U) x) =
          Z.presheaf.map (homOfLE hWV).op t := by
  obtain ⟨y, hy⟩ := i.stalkMap_surjective z (Z.presheaf.germ V z hz t)
  obtain ⟨U, hU, x, hx⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf y
  have hgerm : Z.presheaf.germ (i ⁻¹ᵁ U) z hU ((i.app U) x) = Z.presheaf.germ V z hz t := by
    rw [← Scheme.Hom.germ_stalkMap_apply, hx, hy]
  obtain ⟨W, hzW, iU, iV, he⟩ := Z.presheaf.germ_eq z hU hz _ _ hgerm
  refine ⟨U, W, iV.le, iU.le, x, hzW, ?_⟩
  rwa [Subsingleton.elim (homOfLE iU.le) iU, Subsingleton.elim (homOfLE iV.le) iV]

/-- A morphism out of the sheaf of relative differentials is determined by its effect on the
universal differentials of local sections. This is the uniqueness half of the universal
property of [Stacks, Tag 08RM], read on sections. -/
theorem relativeDifferentials_hom_ext {Z S : Scheme.{u}} (q : Z ⟶ S) {F : Z.Modules}
    (g g' : Scheme.Hom.relativeDifferentials q ⟶ F)
    (h : ∀ (V : Z.Opens) (t : Γ(Z, V)),
      (g.val.app (op V)).hom ((Scheme.Hom.universalRelativeDerivation q).d t) =
        (g'.val.app (op V)).hom ((Scheme.Hom.universalRelativeDerivation q).d t)) :
    g = g' := by
  refine (SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap q) F
    ((Scheme.Hom.universalRelativeDerivation q).postcomp g.val)).unique rfl ?_
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext V t
  exact (h V.unop t).symm

section Transfer

variable {Z X S : Scheme.{u}}

/-- Sections of a pushforward over `U` are sections over the preimage of `U`, and the
pushforward of a morphism acts on them as the morphism does. -/
theorem pushforward_map_val_app_hom (i : Z ⟶ X) {M N : Z.Modules} (φ : M ⟶ N)
    (U : X.Opens) (y : M.val.obj (op (i ⁻¹ᵁ U))) :
    (((Scheme.Modules.pushforward i).map φ).val.app (op U)).hom y =
      (φ.val.app (op (i ⁻¹ᵁ U))).hom y :=
  rfl

/-- A composite of morphisms of sheaves of modules acts on a section as the composite of the
two actions. -/
theorem comp_val_app_hom {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens)
    (y : M.val.obj (op U)) :
    ((φ ≫ ψ).val.app (op U)).hom y = (ψ.val.app (op U)).hom ((φ.val.app (op U)).hom y) :=
  rfl

/-- Two morphisms out of `Ω_{Z/S}` that agree after composition with the canonical map
`i^*Ω_{X/S} ⟶ Ω_{Z/S}` agree on the universal differential of every section pulled back
from `X`. -/
theorem app_d_app_eq_of_comp_eq (i : Z ⟶ X) (p : X ⟶ S) {F : Z.Modules}
    (hcomm : i ≫ p = (i ≫ p) ≫ 𝟙 S)
    {g g' : Scheme.Hom.relativeDifferentials (i ≫ p) ⟶ F}
    (hgg : Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) hcomm ≫ g =
      Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) hcomm ≫ g')
    (U : X.Opens) (x : Γ(X, U)) :
    (g.val.app (op (i ⁻¹ᵁ U))).hom
        ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U) x)) =
      (g'.val.app (op (i ⁻¹ᵁ U))).hom
        ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U) x)) := by
  have h := congrArg (fun c => (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
    (Scheme.Hom.relativeDifferentials p) F c) hgg
  simp only [Adjunction.homEquiv_naturality_right] at h
  have h2 := congrArg (fun φ : Scheme.Hom.relativeDifferentials p ⟶
      (Scheme.Modules.pushforward i).obj F =>
      (φ.val.app (op U)).hom ((Scheme.Hom.universalRelativeDerivation p).d x)) h
  have key : ∀ gg : Scheme.Hom.relativeDifferentials (i ≫ p) ⟶ F,
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
            (Scheme.Hom.relativeDifferentials p) (Scheme.Hom.relativeDifferentials (i ≫ p))
            (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) hcomm)) ≫
          (Scheme.Modules.pushforward i).map gg).val.app (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d x) =
      (gg.val.app (op (i ⁻¹ᵁ U))).hom
        ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U) x)) := fun gg => by
    refine (comp_val_app_hom _ _ U _).trans ?_
    rw [Scheme.Hom.relativeDifferentialsMap_app_d]
    exact pushforward_map_val_app_hom i gg U _
  rwa [← key g, ← key g']

/-- **The canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` is an epimorphism** whenever `i : Z ⟶ X` is
surjective on stalks. -/
theorem epi_relativeDifferentialsMap (i : Z ⟶ X) [SurjectiveOnStalks i] (p : X ⟶ S)
    (hcomm : i ≫ p = (i ≫ p) ≫ 𝟙 S) :
    Epi (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) hcomm) := by
  refine ⟨fun {F} g g' hgg => relativeDifferentials_hom_ext (i ≫ p) g g' fun V t => ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf F) (U := op V) ?_
  intro z hz
  obtain ⟨U, W, hWV, hWU, x, hzW, he⟩ := exists_restrict_eq_app i t z hz
  refine ⟨W, hWV, hzW, ?_⟩
  have step : ∀ (gg : Scheme.Hom.relativeDifferentials (i ≫ p) ⟶ F) {V' : Z.Opens}
      (h : W ≤ V') (s : Γ(Z, V')),
      (F.val.map (homOfLE h).op).hom
          ((gg.val.app (op V')).hom ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d s)) =
        (gg.val.app (op W)).hom
          ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d
            (Z.presheaf.map (homOfLE h).op s)) := fun gg V' h s =>
    (PresheafOfModules.naturality_apply gg.val (homOfLE h).op _).symm.trans
      (congrArg (fun y => (gg.val.app (op W)).hom y)
        ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d_map (homOfLE h).op s).symm)
  have key : ∀ gg : Scheme.Hom.relativeDifferentials (i ≫ p) ⟶ F,
      (F.val.map (homOfLE hWV).op).hom
          ((gg.val.app (op V)).hom ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d t)) =
        (F.val.map (homOfLE hWU).op).hom
          ((gg.val.app (op (i ⁻¹ᵁ U))).hom
            ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U) x))) := fun gg => by
    rw [step gg hWV, step gg hWU, he]
  exact (key g).trans
    ((congrArg (fun y => (F.val.map (homOfLE hWU).op).hom y)
      (app_d_app_eq_of_comp_eq i p hcomm hgg U x)).trans (key g').symm)

/-- **[Stacks, Tag 01UZ], exactness at the right term.** For an immersion `i : Z ⟶ X` of
schemes over `S`, the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 01UV] is an
epimorphism, so the conormal sequence of `i` ends in zero. -/
@[stacks 01UZ "exactness at the right term", instance, ega "IV 16.4.21" "→ 0 (surjectivity)"]
theorem differentialsMapOver_epi (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) :
    Epi (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)) :=
  epi_relativeDifferentialsMap i p _

end Transfer

/-! ### The first arrow -/

section FirstArrow

open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.RegularIdealSheaf

universe v v₁ v₂ u₁ u₂

/-- A scalar that a change of rings sends to zero acts by zero after restriction of scalars:
the restricted action of `r` is the action of its image. -/
theorem smul_restrictScalars_eq_zero {C : Type u₁} [Category.{v₁} C]
    {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R') {M : PresheafOfModules.{v} R'} {V : Cᵒᵖ}
    (r : R.obj V) (hr : (α.app V).hom r = 0)
    (m : ((PresheafOfModules.restrictScalars α).obj M).obj V) : r • m = 0 := by
  have h : (((PresheafOfModules.restrictScalars α).obj M).obj V).smul r = 0 := by
    rw [show ((PresheafOfModules.restrictScalars α).obj M).obj V =
      (ModuleCat.restrictScalars (α.app V).hom).obj (M.obj V) from rfl,
      ModuleCat.smul_restrictScalars, hr, map_zero]
    rfl
  have h2 := congrArg (fun t => AddCommGrpCat.Hom.hom t.asHom m) h
  exact h2

/-- A derivation is linear in the first factor of a product whose second factor annihilates
the coefficient module: the Leibniz term `b · d a` of `d (a * b)` vanishes. -/
theorem derivation_d_mul_of_smul_eq_zero {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {O : Cᵒᵖ ⥤ CommRingCat.{u}} {G : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {M : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} {φ : O ⟶ G.op ⋙ R}
    (d : PresheafOfModulesOfCommRing.Derivation M φ) {V : Dᵒᵖ} (a b : R.obj V)
    (hb : ∀ m : M.obj V, b • m = 0) :
    d.d (a * b) = a • d.d b := by
  rw [d.d_mul, hb (d.d a), add_zero]

variable {Z W S : Scheme.{u}}

/-- **The restriction of a derivation to a defining ideal sheaf.** For a morphism of schemes
`j : Z ⟶ W` over `S` and a derivation `D` of `𝒪_W` with values in the pushforward of an
`𝒪_Z`-module, the assignment `f ↦ D f` is an `𝒪_W`-linear map out of the defining ideal sheaf
of `j`. -/
noncomputable def idealDerivationHom (j : Z ⟶ W) (q : W ⟶ S) (F : Z.Modules)
    (D : AlgebraicGeometry.SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      ((Scheme.Modules.pushforward j).obj F)) :
    ((definingIdealOfHom j).toSheafOfModules : W.Modules) ⟶
      (Scheme.Modules.pushforward j).obj F :=
  ⟨{ app := fun V => ModuleCat.ofHom
       (X := (definingIdealOfHom j).toSheafOfModules.val.obj V)
       (Y := ((Scheme.Modules.pushforward j).obj F).val.obj V)
       { toFun := fun f => D.d f.1
         map_add' := fun f g => D.d.map_add f.1 g.1
         map_smul' := fun r f =>
           derivation_d_mul_of_smul_eq_zero D r f.1
             (fun m => smul_restrictScalars_eq_zero _ f.1 f.2 m) }
     naturality := fun {V V'} α => by
       ext f
       exact D.d_map α f.1 }⟩

/-- On sections, the restriction of a derivation to the defining ideal sheaf is the
derivation. -/
theorem idealDerivationHom_val_app (j : Z ⟶ W) (q : W ⟶ S) (F : Z.Modules)
    (D : AlgebraicGeometry.SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      ((Scheme.Modules.pushforward j).obj F)) (V : (Opens W)ᵒᵖ)
    (f : (definingIdealOfHom j).toSheafOfModules.val.obj V) :
    ((idealDerivationHom j q F D).val.app V).hom f = D.d f.1 :=
  rfl

variable {X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **Differentials of the coborder neighbourhood, pulled back to `Z`, are `i^*Ω_{X/S}`.**
The canonical map `ι^*Ω_{X/S} ⟶ Ω_{W/S}` of the open immersion `ι : W ⟶ X` is an isomorphism;
pulling it back along the closed factor and using `j^*ι^* ≅ (j ≫ ι)^* = i^*` gives this
identification. -/
noncomputable def coborderPullbackDifferentialsIso :
    (Scheme.Modules.pullback i.liftCoborder).obj
        (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  (Scheme.Modules.pullback i.liftCoborder).mapIso
      (asIso (Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p
        (i.coborderRange.ι ≫ p) (𝟙 S) (by simp))).symm ≪≫
    (Scheme.Modules.pullbackComp i.liftCoborder i.coborderRange.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr i.liftCoborder_ι).app _

/-- **The derivation `a ↦ 1 ⊗ d a`** of the structure sheaf of the coborder neighbourhood with
values in the pushforward of `i^*Ω_{X/S}`: the universal derivation of `W` over `S`, followed
by the unit of `j^* ⊣ j_*` and the identification `j^*Ω_{W/S} ≅ i^*Ω_{X/S}`. -/
noncomputable def conormalDerivation :
    AlgebraicGeometry.SheafOfModules.SheafDerivation
      (inverseImageStructureMap (i.coborderRange.ι ≫ p))
      ((Scheme.Modules.pushforward i.liftCoborder).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p))) :=
  (Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).postcomp
    ((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app _ ≫
      (Scheme.Modules.pushforward i.liftCoborder).map
        (coborderPullbackDifferentialsIso i p).hom).val

/-- **The transpose of the first arrow**: the `𝒪_W`-linear map `ℐ ⟶ j_*(i^*Ω_{X/S})` sending a
section `f` of the defining ideal sheaf of the closed factor to `1 ⊗ d f`. -/
noncomputable def conormalDifferentialTranspose :
    ((definingIdeal i).toSheafOfModules : (i.coborderRange.toScheme).Modules) ⟶
      (Scheme.Modules.pushforward i.liftCoborder).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) :=
  idealDerivationHom i.liftCoborder (i.coborderRange.ι ≫ p) _ (conormalDerivation i p)

/-- On sections the transpose of the first arrow is `f ↦ 1 ⊗ d f`: the universal differential
of `f` over `S`, moved into `i^*Ω_{X/S}` by the unit of `j^* ⊣ j_*`. -/
theorem conormalDifferentialTranspose_val_app (V : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (f : (definingIdeal i).toSheafOfModules.val.obj V) :
    ((conormalDifferentialTranspose i p).val.app V).hom f =
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
          (Scheme.Modules.pushforward i.liftCoborder).map
            (coborderPullbackDifferentialsIso i p).hom).val.app V).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d f.1) :=
  rfl

/-- **[Stacks, Tag 01UZ], the first arrow.** For an immersion `i : Z ⟶ X` of schemes over `S`,
the canonical morphism `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` induced by `d_{X/S}`: the adjoint transpose of
the map carrying a section `f` of the defining ideal sheaf of the closed factor to `1 ⊗ d f`. -/
@[stacks 01UZ "the first arrow"]
noncomputable def conormalDifferential :
    (conormalSheaf i : Z.Modules) ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _).symm
    (conormalDifferentialTranspose i p)

/-- **The first arrow is pinned on sections of the ideal sheaf.** Composing it with the
canonical map `ℐ ⟶ j_*𝒞_{Z/X}` recovers the assignment `f ↦ 1 ⊗ d f`. -/
theorem conormalComparison_comp_conormalDifferential :
    conormalComparison i ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
        (conormalDifferential i p) =
      conormalDifferentialTranspose i p :=
  (conormalComparison_comp_map i (conormalDifferential i p)).trans
    (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _).apply_symm_apply
      (conormalDifferentialTranspose i p))

/-- **That pinning determines the first arrow.** A morphism out of the conormal sheaf whose
composite with the canonical map `ℐ ⟶ j_*𝒞_{Z/X}` is `f ↦ 1 ⊗ d f` is the first arrow. -/
theorem conormalDifferential_unique
    (h : (conormalSheaf i : Z.Modules) ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p))
    (hh : conormalComparison i ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map h =
      conormalDifferentialTranspose i p) :
    h = conormalDifferential i p :=
  (existsUnique_hom_conormalComparison i (conormalDifferentialTranspose i p)).unique hh
    (conormalComparison_comp_conormalDifferential i p)

/-- The closed factor of an immersion, followed by the restriction of the base morphism to the
coborder neighbourhood, is the immersion followed by the base morphism. -/
theorem liftCoborder_comp_coborderRange_ι_comp :
    i.liftCoborder ≫ (i.coborderRange.ι ≫ p) = (i ≫ p) ≫ 𝟙 S := by
  rw [← Category.assoc, i.liftCoborder_ι, Category.comp_id]

/-- **The comparison isomorphism carries the second arrow of the closed factor to the second
arrow of the immersion.** -/
theorem coborderPullbackDifferentialsIso_inv_comp :
    (coborderPullbackDifferentialsIso i p).inv ≫
        Scheme.Hom.relativeDifferentialsMap i.liftCoborder (i.coborderRange.ι ≫ p) (i ≫ p)
          (𝟙 S) (liftCoborder_comp_coborderRange_ι_comp i p) =
      Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp) := by
  have hι := Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap
    i.coborderRange.ι p (i.coborderRange.ι ≫ p) (𝟙 S) (by simp)
  have hj := Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap
    i.liftCoborder (i.coborderRange.ι ≫ p) (i ≫ p) (𝟙 S)
    (liftCoborder_comp_coborderRange_ι_comp i p)
  refine Eq.trans ?_ (((hι.comp hj).congr_left i.liftCoborder_ι).eq_relativeDifferentialsMap
    (𝟙 S) (by simp))
  simp [coborderPullbackDifferentialsIso]

/-- The same identity read on the other side of the comparison isomorphism. -/
theorem coborderPullbackDifferentialsIso_hom_comp :
    (coborderPullbackDifferentialsIso i p).hom ≫
        Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp) =
      Scheme.Hom.relativeDifferentialsMap i.liftCoborder (i.coborderRange.ι ≫ p) (i ≫ p)
        (𝟙 S) (liftCoborder_comp_coborderRange_ι_comp i p) := by
  rw [← coborderPullbackDifferentialsIso_inv_comp i p, Iso.hom_inv_id_assoc]

/-- The derivation defining the first arrow, followed by the second arrow, is the transpose of
the second arrow of the closed factor: both carry `d a` to `d (j^♯ a)`. -/
theorem unit_comp_coborderPullbackDifferentialsIso_comp :
    ((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
        (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
      (Scheme.Modules.pushforward i.liftCoborder).map
        (coborderPullbackDifferentialsIso i p).hom) ≫
      (Scheme.Modules.pushforward i.liftCoborder).map
        (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)) =
    (Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _
      (Scheme.Hom.relativeDifferentialsMap i.liftCoborder (i.coborderRange.ι ≫ p) (i ≫ p)
        (𝟙 S) (liftCoborder_comp_coborderRange_ι_comp i p)) := by
  rw [Category.assoc, ← Functor.map_comp, coborderPullbackDifferentialsIso_hom_comp,
    Adjunction.homEquiv_unit]

/-- **The transpose of the first arrow is killed by the second arrow, on every section of the
ideal sheaf.** The transpose sends `f` to `1 ⊗ d f`, and the second arrow sends that to
`d (j^♯ f)`, which is `d 0 = 0` because `f` lies in the defining ideal. -/
theorem conormalDifferentialTranspose_comp_val_app_eq_zero
    (V : Opens i.coborderRange.toScheme)
    (f : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    ((conormalDifferentialTranspose i p ≫ (Scheme.Modules.pushforward i.liftCoborder).map
        (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))).val.app
      (op V)).hom f = 0 := by
  have h1 : ((conormalDifferentialTranspose i p ≫
        (Scheme.Modules.pushforward i.liftCoborder).map
          (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))).val.app
        (op V)).hom f =
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _
        (Scheme.Hom.relativeDifferentialsMap i.liftCoborder (i.coborderRange.ι ≫ p) (i ≫ p)
          (𝟙 S) (liftCoborder_comp_coborderRange_ι_comp i p))).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d f.1) :=
    congrArg (fun m => (m.val.app (op V)).hom
      ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d f.1))
      (unit_comp_coborderPullbackDifferentialsIso_comp i p)
  rw [h1]
  refine Eq.trans (Scheme.Hom.relativeDifferentialsMap_app_d (f := i.liftCoborder)
    (p := i.coborderRange.ι ≫ p) (p' := i ≫ p) (𝟙 S)
    (liftCoborder_comp_coborderRange_ι_comp i p) V f.1) ?_
  rw [show (i.liftCoborder.app V).hom f.1 = 0 from f.2]
  exact map_zero _

/-- The transpose of the first arrow, followed by the second arrow, is the transpose of the
zero morphism. -/
theorem conormalDifferentialTranspose_comp_eq :
    conormalDifferentialTranspose i p ≫ (Scheme.Modules.pushforward i.liftCoborder).map
        (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)) =
      conormalComparison i ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
        (0 : (Scheme.Modules.pullback i.liftCoborder).obj ((definingIdeal i).toSheafOfModules) ⟶
          Scheme.Hom.relativeDifferentials (i ≫ p)) := by
  ext V f
  obtain ⟨V⟩ := V
  refine (conormalDifferentialTranspose_comp_val_app_eq_zero i p V f).trans ?_
  refine Eq.symm (Eq.trans (congrArg (fun m => ((conormalComparison i ≫ m).val.app (op V)).hom f)
    (Functor.map_zero (modulePushforward i.liftCoborder.toLRSHom.toShHom)
      ((Scheme.Modules.pullback i.liftCoborder).obj ((definingIdeal i).toSheafOfModules))
      (Scheme.Hom.relativeDifferentials (i ≫ p)))) ?_)
  rfl

/-- **[Stacks, Tag 01UZ], the two arrows form a complex.** The composite
`𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S}` vanishes: the first arrow carries the class of a section `f`
of the ideal sheaf to `1 ⊗ d f`, and the second carries that to `d (i^♯ f) = 0`. -/
theorem conormalDifferential_comp_relativeDifferentialsMap :
    conormalDifferential i p ≫
        Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp) =
      (0 : (Scheme.Modules.pullback i.liftCoborder).obj ((definingIdeal i).toSheafOfModules) ⟶
        Scheme.Hom.relativeDifferentials (i ≫ p)) :=
  (existsUnique_hom_conormalComparison i _).unique
    (by
      refine Eq.trans ?_ (conormalDifferentialTranspose_comp_eq i p)
      refine Eq.trans (congrArg (fun m => conormalComparison i ≫ m)
        ((modulePushforward i.liftCoborder.toLRSHom.toShHom).map_comp
          (conormalDifferential i p)
          (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg
        (fun m => m ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
          (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)))
        (conormalComparison_comp_conormalDifferential i p))
    rfl

/-- **[Stacks, Tag 01UZ], the conormal sequence of an immersion** `i : Z ⟶ X` over `S`, as a
short complex `𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S}` of `𝒪_Z`-modules. -/
noncomputable def conormalShortComplex : ShortComplex Z.Modules :=
  ShortComplex.mk (conormalDifferential i p)
    (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))
    (conormalDifferential_comp_relativeDifferentialsMap i p)

/-- **The conormal sequence ends in zero**: the second arrow of
`Stacks.ConormalSequenceRight.conormalShortComplex` is an epimorphism. -/
theorem epi_conormalShortComplex_g : Epi (conormalShortComplex i p).g :=
  differentialsMapOver_epi i p

end FirstArrow

/-! ### The functorial second arrow

[Stacks, Tag 01UZ] does not construct its second arrow: it is the canonical map of
[Stacks, Tag 01UV] for the commutative square whose base morphism is the identity, and the
reference statement registers that declaration itself under this label rather than wrapping it.
The registration below is the same move for the library name. -/

add_to_stacks 01UZ "the functorial second arrow"
  AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap

/-! ### Faithfulness

One `example` per discharged label, in the reference statement's binder order, stating its assertion
over library names. -/

/-- `01UZ "the first arrow"`: the first arrow of the conormal sequence is a morphism from the
conormal sheaf of the immersion to the pullback of the relative differentials of the ambient
scheme. -/
noncomputable example {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) :
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i : Z.Modules) ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  conormalDifferential i p

/-- `01UZ "the functorial second arrow"`: the second arrow of the conormal sequence is the
canonical map of [Stacks, Tag 01UV] for the square over the identity of `S`. -/
noncomputable example {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S) :
    (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ⟶
      Scheme.Hom.relativeDifferentials (i ≫ p) :=
  Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)

/-- `01UZ "exactness at the right term"`: the canonical map from pulled-back relative
differentials of `X` to relative differentials of `Z` is an epimorphism. -/
example {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) :
    Epi (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)) :=
  differentialsMapOver_epi i p

end Stacks.ConormalSequenceRight

end
