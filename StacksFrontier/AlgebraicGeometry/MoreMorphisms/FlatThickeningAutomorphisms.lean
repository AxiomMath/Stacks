module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatThickeningDifferentials
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheafModules
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceLiftUniqueness
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Automorphisms of a flat deformation across a first-order thickening

Let `S ⊂ S'` be a first order thickening of schemes, let `f : X ⟶ S` be a morphism, let
`f' : X' ⟶ S'` be flat and let `i : X ⟶ X'` make the square
```
X  --i-->  X'
|          |
f          f'
↓          ↓
S  --t-->  S'
```
cartesian, so that `i` identifies `X` with `X' ×_{S'} S` over `S`.  This file proves part (2) of
[Stacks Project, Tag 0D14]: the set of automorphisms `φ : X' ⟶ X'` over `S'` which reduce to the
identity on `X' ×_{S'} S` is

`Ext⁰_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`.

The flatness of `f` that the source also assumes is not used; it follows from the flatness of
`f'` and the cartesian square, and no step below needs it.

## Main definitions

* `Stacks.Thickenings.autOfHom`: the automorphism `φ_α` of `X'` attached to an `𝒪_X`-linear map
  `α : Ω_{X/S} ⟶ 𝒞_{X/X'}`.  Its comorphism is `g ↦ g + α(d_{X/S}(i^♯ g))`.
* `Stacks.Thickenings.homOfAut`: the inverse construction, the `𝒪_X`-linear map attached to an
  automorphism.
* `Stacks.Thickenings.derivationAutEquiv`: the bijection between `Hom_{𝒪_X}(Ω_{X/S}, 𝒞_{X/X'})`
  and the automorphisms in question.
* `Stacks.Thickenings.flatThickeningAutEquiv`: part (2) of [Stacks Project, Tag 0D14] itself,
  the previous bijection composed with the identification of the acting group
  `Stacks.Thickenings.flatThickeningActingGroupAddEquiv`.

## Main results

* `Stacks.Thickenings.autOfHom_appLE` and
  `Stacks.Thickenings.flatThickeningAutEquiv_apply_appLE` pin the bijection down: they give the
  comorphism of the automorphism attached to a map, resp. to a degree-zero `Ext`-class, over an
  arbitrary pair of opens.  Without them the type of `flatThickeningAutEquiv` would be satisfied
  by any other bijection too, for instance by the one obtained by negating every class.
* `Stacks.Thickenings.autOfHom_zero` and `Stacks.Thickenings.autOfHom_add`: the identity
  corresponds to `0` and composition to addition, so the bijection is an isomorphism of groups.
* `Stacks.Thickenings.isIso_of_comm_of_isPullback`: an *endomorphism* of `X'` over `S'` reducing
  to the identity on `X` is automatically an automorphism, so the set the source speaks of may
  be read either way.
* `Stacks.Thickenings.eq_autOfHom`: a morphism whose comorphism has the displayed form is
  `Stacks.Thickenings.autOfHom`, which is the uniqueness this file inherits from
  [Stacks Project, Tag 02H5].

## Route

The two directions of the bijection are the two tagged results this file composes.

* Forwards, `Stacks.Thickenings.autOfHom` is the action of [Stacks Project, Tag 02H5],
  `Stacks.Thickenings.derivationActionGlobal`, for the degenerate morphism of thickenings
  `(𝟙 X, 𝟙 X')` from `i` to itself over `S'`.  That action consumes a map out of
  `(𝟙 X)^*Ω_{X/S'}`, and `Stacks.Thickenings.pullbackCotangentComparison` — invertible because
  `S ⊂ S'` is formally unramified — turns a map out of `Ω_{X/S}` into one.  The resulting
  formula for the comorphism is
  `Stacks.Thickenings.derivationSection_pullbackCotangentComparison`.
* Backwards, `Stacks.Thickenings.homOfAut` is the difference map of
  [Stacks Project, Tag 04FL] for the pair `(φ, 𝟙 X')`,
  `Stacks.Thickenings.diagonalConormalSheafMap`, which is a map out of `i^*Ω_{X'/S'}`, read
  through the isomorphism `i^*Ω_{X'/S'} ≅ Ω_{X/S}` of
  `Stacks.Thickenings.isIso_relativeDifferentialsMapBase`.  That isomorphism is where the
  cartesian square enters, through the vanishing of the conormal differential.

That the two are mutually inverse is proved by two different mechanisms, and that asymmetry is
forced.  `Stacks.Thickenings.autOfHom_homOfAut` is the uniqueness clause of
[Stacks Project, Tag 02H5]: both `φ` and the action of its derivation have the same comorphism,
by [Stacks Project, Tag 04FL] and the injectivity of `𝒞_{X/X'} ⟶ 𝒪_{X'}`
(`Stacks.Thickenings.conormalSection_injective`).  `Stacks.Thickenings.homOfAut_autOfHom` cannot
be proved that way, because a map out of `Ω_{X/S}` is *not* determined by its values on the
differentials `d_{X/S}(i^♯ g)` of sections pulled back along `i^♯`: those sections do not
exhaust `𝒪_X`, the comorphism of a closed immersion being surjective only locally.  The
comparison is therefore made upstairs, between the two maps out of `Ω_{X'/S'}` obtained by
transposing along `i^* ⊣ i_*`, where the universal property of the sheaf of relative
differentials does apply — `Stacks.Thickenings.hom_ext_universalRelativeDerivation` — and the
cartesian square's isomorphism is cancelled afterwards.

The group law is `Stacks.Thickenings.autOfHom_add`: the cross term
`α(d_{X/S}(i^♯(β(d_{X/S}(i^♯ g))))) ` vanishes because the perturbation takes values in the
defining ideal of `i`, which `i^♯` kills, so the composite of the two actions is the action of
the sum.  Inverting an automorphism therefore costs nothing beyond negating its derivation, and
that is `Stacks.Thickenings.isIso_autOfHom`.

## Scope

Part (1) of [Stacks Project, Tag 0D14] — that the isomorphism classes of flat deformations of
`f` over `S'` form a principal homogeneous space under `Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})` — is
`Stacks.Thickenings.FlatDeformation.exists_addTorsor_classes`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/FlatDeformation/Torsor.lean`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5), a derivation acts in
  exactly one way on a lift
* [Stacks Project, Tag 04FL](https://stacks.math.columbia.edu/tag/04FL), the difference of two
  maps through the diagonal
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), the universal property
  of the sheaf of relative differentials
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Opposite

universe u

namespace Stacks.Thickenings

variable {X X' S S' : Scheme.{u}}

/-- The comorphism of the identity over a pair of opens is the restriction map. -/
theorem id_appLE_apply (W V : X'.Opens) (hA : V ≤ W) (g : Γ(X', W)) :
    ((𝟙 X' : X' ⟶ X').appLE W V hA).hom g = (X'.presheaf.map (homOfLE hA).op).hom g := by
  have h : (𝟙 X' : X' ⟶ X').appLE W V hA = X'.presheaf.map (homOfLE hA).op := by
    show (𝟙 X' : X' ⟶ X').app W ≫ X'.presheaf.map (homOfLE hA).op = _
    rw [Scheme.Hom.id_app]
    exact CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  exact congr($(h).hom g)

/-- Restriction of a section along a reflexive inclusion of opens does nothing: the opens of a
scheme form a poset, so that inclusion is the identity. -/
theorem presheaf_map_le_self {Z : Scheme.{u}} (W : Z.Opens) (h : W ≤ W) (g : Γ(Z, W)) :
    (Z.presheaf.map (homOfLE h).op).hom g = g := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The comorphism of the identity from an open to itself does nothing. -/
theorem id_appLE_self (W : X'.Opens) (h : W ≤ W) (g : Γ(X', W)) :
    ((𝟙 X' : X' ⟶ X').appLE W W h).hom g = g :=
  (id_appLE_apply W W h g).trans (presheaf_map_le_self W h g)

/-- Restricting the value of a comorphism to a smaller open is the comorphism over that open. -/
private theorem map_appLE_apply {U V V' : X'.Opens} (φ : X' ⟶ X') (e : V ≤ φ ⁻¹ᵁ U)
    (hV : V' ≤ V) (g : Γ(X', U)) :
    (X'.presheaf.map (homOfLE hV).op).hom ((φ.appLE U V e).hom g)
      = (φ.appLE U V' (hV.trans e)).hom g :=
  congrArg (fun z => z.hom g) (Scheme.Hom.appLE_map φ e (homOfLE hV).op)

/-- **Two morphisms out of `Ω_{X/S}` agreeing on every universal differential are equal**, the
corepresentability of relative derivations read on sections. -/
theorem hom_ext_universalRelativeDerivation {Z T : Scheme.{u}} (p : Z ⟶ T) {F : Z.Modules}
    {u v : Scheme.Hom.relativeDifferentials p ⟶ F}
    (h : ∀ (W : Z.Opens) (x : Γ(Z, W)),
      (Scheme.Modules.Hom.app u W).hom ((Scheme.Hom.universalRelativeDerivation p).d x)
        = (Scheme.Modules.Hom.app v W).hom ((Scheme.Hom.universalRelativeDerivation p).d x)) :
    u = v :=
  Scheme.Hom.eq_of_postcomp_eq_universalRelativeDerivation p
    (PresheafOfModulesOfCommRing.Derivation.ext (funext fun W => AddMonoidHom.ext fun x => h W.unop x))

section Action

variable {i : X ⟶ X'} {t : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}
variable [AlgebraicGeometry.IsClosedImmersion i] [IsImmersion t]
  (hsq : i.ker ^ 2 = ⊥) (hw : i ≫ f' = f ≫ t)

omit [AlgebraicGeometry.IsClosedImmersion i] in
/-- `i ≫ 𝟙 X' = 𝟙 X ≫ i`: the identity of `X'`, read as a morphism of thickenings from `i` to
itself whose restriction to `X` is the identity. -/
theorem comm_id_thickening : i ≫ (𝟙 X' : X' ⟶ X') = 𝟙 X ≫ i := by
  rw [Category.comp_id, Category.id_comp]

variable (α : Scheme.Hom.relativeDifferentials f ⟶ conormalModules i)

/-- **The automorphism of `X'` attached to `α : Ω_{X/S} ⟶ 𝒞_{X/X'}`.** -/
def autOfHom : X' ⟶ X' :=
  derivationActionGlobal (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq
    (pullbackCotangentComparison i t f f' hw ≫ α) comm_id_thickening

omit [IsImmersion t] in
/-- The automorphism `autOfHom hsq hw α` restricts to the identity on `X`:
`i ≫ autOfHom hsq hw α = i`. -/
theorem comm_autOfHom : i ≫ autOfHom hsq hw α = i :=
  (comm_derivationActionGlobal (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq _
    comm_id_thickening).trans (Category.id_comp i)

omit [IsImmersion t] in
/-- The automorphism `autOfHom hsq hw α` is a morphism over `S'`: `autOfHom hsq hw α ≫ f' = f'`. -/
theorem comp_autOfHom : autOfHom hsq hw α ≫ f' = f' :=
  comp_derivationActionGlobal (p := f') hsq _ comm_id_thickening (Category.id_comp f')

omit [IsImmersion t] in
/-- **The perturbation of `Stacks.Thickenings.derivationActionGlobal` at the datum
`pullbackCotangentComparison ≫ α`, read as a value of `α`.** -/
theorem derivationSection_pullbackCotangentComparison (W V : X'.Opens) (hA : V ≤ W)
    (hU : i ⁻¹ᵁ V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ (i ⁻¹ᵁ W)) (g : Γ(X', W)) :
    derivationSection (j := i) (a := 𝟙 X) (q := f') hsq
        (pullbackCotangentComparison i t f f' hw ≫ α) W V hU g
      = conormalSection hsq V ((Scheme.Modules.Hom.app α (i ⁻¹ᵁ V)).hom
          ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE (i.preimage_mono hA)).op
            ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g)))) := by
  refine congrArg (conormalSection hsq V) ?_
  show (Scheme.Modules.Hom.app α (i ⁻¹ᵁ V)).hom
      ((pullbackCotangentComparison i t f f' hw).val.app (op (i ⁻¹ᵁ V))
        (Stacks.Smooth.pullbackD (i ≫ f') (𝟙 X) (i ⁻¹ᵁ W) hU ((i.app W).hom g))) = _
  exact congrArg _ (pullbackCotangentComparison_pullbackD i t f f' hw (i ⁻¹ᵁ W) (i ⁻¹ᵁ V) _ _)

omit [IsImmersion t] in
/-- **The comorphism of the automorphism attached to `α`.** -/
theorem autOfHom_appLE (W V : X'.Opens) (hA : V ≤ W) (g : Γ(X', W)) :
    ((autOfHom hsq hw α).appLE W V hA).hom g
      = (X'.presheaf.map (homOfLE hA).op).hom g
        + conormalSection hsq V ((Scheme.Modules.Hom.app α (i ⁻¹ᵁ V)).hom
            ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE (i.preimage_mono hA)).op
              ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g)))) := by
  refine Eq.trans (derivationActionGlobal_appLE (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq
    (pullbackCotangentComparison i t f f' hw ≫ α) comm_id_thickening W V hA g) ?_
  rw [id_appLE_apply W V hA g,
    derivationSection_pullbackCotangentComparison hsq hw α W V hA _ g]

omit [IsImmersion t] in
/-- **Uniqueness of the automorphism attached to `α`.** -/
theorem eq_autOfHom {c : X' ⟶ X'} (comm_c : i ≫ c = i)
    (hc : ∀ (W V : X'.Opens) (hA : V ≤ W) (hB : V ≤ c ⁻¹ᵁ W) (g : Γ(X', W)),
      (c.appLE W V hB).hom g = (X'.presheaf.map (homOfLE hA).op).hom g
        + conormalSection hsq V ((Scheme.Modules.Hom.app α (i ⁻¹ᵁ V)).hom
            ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE (i.preimage_mono hA)).op
              ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g))))) :
    c = autOfHom hsq hw α := by
  refine eq_derivationActionGlobal (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq
    (pullbackCotangentComparison i t f f' hw ≫ α) comm_id_thickening
    (comm_c.trans (Category.id_comp i).symm) fun W V hA g => ?_
  rw [id_appLE_apply W V hA g,
    derivationSection_pullbackCotangentComparison hsq hw α W V hA _ g]
  exact hc W V hA _ g

omit [IsImmersion t] in
/-- **The automorphism attached to `0` is the identity.** -/
theorem autOfHom_zero :
    autOfHom hsq hw (0 : Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) = 𝟙 X' :=
  (eq_autOfHom hsq hw 0 (Category.comp_id i) fun W V hA hB g => by
    rw [id_appLE_apply W V hA g]
    refine (add_zero _).symm.trans (congrArg (fun z => _ + z) ?_).symm
    refine Eq.trans (congrArg (conormalSection hsq V) ?_) (conormalSection_zero hsq V)
    rw [Scheme.Modules.Hom.zero_app]
    rfl).symm

omit [IsImmersion t] in
/-- **The action of `α` is additive**: the automorphism attached to `α + β` is the composite of
those attached to `α` and to `β`.  The cross term vanishes because the perturbation takes values
in the defining ideal of `i`, which the universal differential kills. -/
theorem autOfHom_add (β : Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) :
    autOfHom hsq hw α ≫ autOfHom hsq hw β = autOfHom hsq hw (α + β) := by
  have hcomm : i ≫ (autOfHom hsq hw α ≫ autOfHom hsq hw β) = i := by
    rw [← Category.assoc, comm_autOfHom, comm_autOfHom]
  refine eq_autOfHom hsq hw (α + β) hcomm fun W V hA hB g => ?_
  have hidW : ((𝟙 X' : X' ⟶ X').app W).hom g = g := by
    rw [Scheme.Hom.id_app]; rfl
  have hker := RingHom.mem_ker.mp (derivationSection_mem_ker (i := i) (j := i) (a := 𝟙 X)
    (q := f') (hsq := hsq) (θ := pullbackCotangentComparison i t f f' hw ≫ β) W W
    (preimage_le_of_comm comm_id_thickening (le_refl W)) g)
  generalize hD : derivationSection (j := i) (a := 𝟙 X) (q := f') hsq
    (pullbackCotangentComparison i t f f' hw ≫ β) W W
    (preimage_le_of_comm comm_id_thickening (le_refl W)) g = D at hker
  have hβ : ((autOfHom hsq hw β).app W).hom g = g + D := by
    refine Eq.trans (derivationActionGlobal_app (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq
      (pullbackCotangentComparison i t f f' hw ≫ β) comm_id_thickening W g) ?_
    rw [hidW, ← hD]
    rfl
  have hαD : ((autOfHom hsq hw α).appLE W V hA).hom D
      = derivationSection (j := i) (a := 𝟙 X) (q := f') hsq
          (pullbackCotangentComparison i t f f' hw ≫ β) W V
          (preimage_le_of_comm comm_id_thickening hA) g := by
    refine Eq.trans (derivationActionGlobal_appLE (j := i) (a := 𝟙 X) (a' := 𝟙 X') (q := f') hsq
      (pullbackCotangentComparison i t f f' hw ≫ α) comm_id_thickening W V hA _) ?_
    rw [derivationSection_eq_zero_of_app_eq_zero (j := i) (a := 𝟙 X) (q := f') hsq
        (pullbackCotangentComparison i t f f' hw ≫ α) W V _ _ hker, add_zero,
      id_appLE_apply W V hA _, ← hD,
      map_derivationSection W hA (preimage_le_of_comm comm_id_thickening (le_refl W))
        (preimage_le_of_comm comm_id_thickening hA) g]
  have hsplit : ((autOfHom hsq hw α ≫ autOfHom hsq hw β).appLE W V hB).hom g
      = ((autOfHom hsq hw α).appLE W V hA).hom (((autOfHom hsq hw β).app W).hom g) := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [hsplit, hβ, map_add, hαD, autOfHom_appLE hsq hw α W V hA g,
    derivationSection_pullbackCotangentComparison hsq hw β W V hA _ g, add_assoc]
  refine congrArg (fun z => (X'.presheaf.map (homOfLE hA).op).hom g + z) ?_
  refine Eq.trans (conormalSection_add hsq V _ _).symm (congrArg (conormalSection hsq V) ?_)
  rw [Scheme.Modules.Hom.add_app]
  rfl

omit [IsImmersion t] in
/-- **The comorphism of the automorphism attached to `α`, over one open.** -/
theorem autOfHom_appLE_self (W : X'.Opens) (h : W ≤ W) (g : Γ(X', W)) :
    ((autOfHom hsq hw α).appLE W W h).hom g
      = g + conormalSection hsq W ((Scheme.Modules.Hom.app α (i ⁻¹ᵁ W)).hom
          ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g))) := by
  refine Eq.trans (autOfHom_appLE hsq hw α W W h g) ?_
  rw [presheaf_map_le_self W h g]
  have hself : ∀ x : Γ(Scheme.Hom.relativeDifferentials f, i ⁻¹ᵁ W),
      (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE (i.preimage_mono h)).op x = x := by
    intro x
    rw [Subsingleton.elim (homOfLE (i.preimage_mono h)) (𝟙 (i ⁻¹ᵁ W)), op_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact congrArg
    (fun z => g + conormalSection hsq W ((Scheme.Modules.Hom.app α (i ⁻¹ᵁ W)).hom z)) (hself _)

omit [IsImmersion t] in
/-- **The automorphism attached to `α` is invertible**, with inverse the one attached to `-α`. -/
theorem isIso_autOfHom : IsIso (autOfHom hsq hw α) :=
  ⟨⟨autOfHom hsq hw (-α),
    by rw [autOfHom_add, add_neg_cancel, autOfHom_zero],
    by rw [autOfHom_add, neg_add_cancel, autOfHom_zero]⟩⟩

/-- **The difference between a lift of the identity and the identity, read through the conormal
sheaf.**  For `φ : X' ⟶ X'` restricting to the identity on `X`, the conormal class of
`φ^♯ g - g` is carried by the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` back to `φ^♯ g - g`. -/
theorem conormalSection_conormalClass_liftDiffSection {φ : X' ⟶ X'} (cb : i ≫ φ = i)
    (W : X'.Opens) (hφ : W ≤ φ ⁻¹ᵁ W) (g : Γ(X', W)) :
    conormalSection hsq W (Stacks.Conormal.conormalClass i (liftPairOpen φ (𝟙 X') W)
        (le_preimage_liftPairOpen cb (Category.comp_id i) W)
        (liftDiffSection φ (𝟙 X') W g) (app_liftDiffSection cb (Category.comp_id i) W g))
      = (φ.appLE W W hφ).hom g - g := by
  have hWL : W ≤ liftPairOpen φ (𝟙 X') W := le_inf (le_refl W) hφ
  refine (conormalSection_conormalClass_of_le i hsq (liftPairOpen φ (𝟙 X') W) W hWL _ _).trans ?_
  exact (map_sub _ _ _).trans (congrArg₂ (· - ·) (map_appLE_apply φ inf_le_right hWL g)
    ((map_appLE_apply (𝟙 X') inf_le_left hWL g).trans (id_appLE_self W _ g)))

/-- `Stacks.Thickenings.conormalSection` is injective: the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` of a
first-order thickening is injective on sections. -/
theorem conormalSection_injective (V : X'.Opens) :
    Function.Injective (conormalSection (i := i) hsq V) :=
  injective_firstOrderImmersionConormalSheafι_val_app i hsq V

end Action

section Inverse

variable {i : X ⟶ X'} {t : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}
variable [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion t]
  (hsq : i.ker ^ 2 = ⊥) (hst : t.ker ^ 2 = ⊥) (sq : IsPullback i f f' t)

omit [AlgebraicGeometry.IsClosedImmersion t] in
/-- **The transpose of `i^*Ω_{X'/S'} ⟶ Ω_{X/S} ⟶ 𝒞_{X/X'}` on a universal differential.** -/
theorem homEquiv_relativeDifferentialsMap_comp_d
    (β : Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) (W : X'.Opens) (g : Γ(X', W)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
          (Scheme.Hom.relativeDifferentials f') (conormalModules i)
          (Scheme.Hom.relativeDifferentialsMap i f' f t sq.w ≫ β)) W).hom
        ((Scheme.Hom.universalRelativeDerivation f').d g)
      = (Scheme.Modules.Hom.app β (i ⁻¹ᵁ W)).hom
          ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g)) := by
  rw [Adjunction.homEquiv_naturality_right]
  show (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward i).map β) W).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
        (Scheme.Hom.relativeDifferentials f')
        (Scheme.Hom.relativeDifferentials f)
        (Scheme.Hom.relativeDifferentialsMap i f' f t sq.w)) W).hom
          ((Scheme.Hom.universalRelativeDerivation f').d g)) = _
  exact congrArg _ (Scheme.Hom.relativeDifferentialsMap_app_d t sq.w W g)

/-- **The derivation attached to an automorphism of `X'` over `S'` restricting to the identity
on `X`.** -/
def homOfAut (φ : X' ⟶ X') (hq : 𝟙 X' ≫ f' = φ ≫ f') (cb : i ≫ φ = i) :
    Scheme.Hom.relativeDifferentials f ⟶ conormalModules i :=
  haveI := isIso_relativeDifferentialsMapBase i t f f' hst sq
  inv (Scheme.Hom.relativeDifferentialsMap i f' f t sq.w) ≫
    diagonalConormalSheafMap hq cb (Category.comp_id i)

/-- Precomposing `homOfAut hst sq φ hq cb` with the comparison map
`Scheme.Hom.relativeDifferentialsMap i f' f t sq.w` recovers `diagonalConormalSheafMap`. -/
theorem relativeDifferentialsMap_comp_homOfAut (φ : X' ⟶ X') (hq : 𝟙 X' ≫ f' = φ ≫ f')
    (cb : i ≫ φ = i) :
    Scheme.Hom.relativeDifferentialsMap i f' f t sq.w ≫ homOfAut hst sq φ hq cb
      = diagonalConormalSheafMap hq cb (Category.comp_id i) := by
  have := isIso_relativeDifferentialsMapBase i t f f' hst sq
  delta homOfAut
  exact IsIso.hom_inv_id_assoc _ _

/-- **[Stacks Project, Tag 04FL] for the pair `(φ, 𝟙 X')`, read as a value of the derivation
attached to `φ`.** -/
theorem homOfAut_app_d (φ : X' ⟶ X') (hq : 𝟙 X' ≫ f' = φ ≫ f') (cb : i ≫ φ = i)
    (W : X'.Opens) (g : Γ(X', W)) :
    (Scheme.Modules.Hom.app (homOfAut hst sq φ hq cb) (i ⁻¹ᵁ W)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g))
      = Stacks.Conormal.conormalClass i (liftPairOpen φ (𝟙 X') W)
          (le_preimage_liftPairOpen cb (Category.comp_id i) W)
          (liftDiffSection φ (𝟙 X') W g)
          (app_liftDiffSection cb (Category.comp_id i) W g) := by
  rw [← homEquiv_relativeDifferentialsMap_comp_d sq (homOfAut hst sq φ hq cb) W g,
    relativeDifferentialsMap_comp_homOfAut]
  exact homEquiv_diagonalConormalSheafMap_d_modules hq cb (Category.comp_id i) W g

/-- **Every automorphism of `X'` over `S'` reducing to the identity on `X` is the action of its
own derivation.** -/
theorem autOfHom_homOfAut (φ : X' ⟶ X') (hq : 𝟙 X' ≫ f' = φ ≫ f') (cb : i ≫ φ = i) :
    autOfHom hsq sq.w (homOfAut hst sq φ hq cb) = φ := by
  refine (eq_autOfHom hsq sq.w (homOfAut hst sq φ hq cb) cb fun W V hA hB g => ?_).symm
  have hφ : W ≤ φ ⁻¹ᵁ W := le_preimage_of_comm hsq comm_id_thickening
    (cb.trans (Category.id_comp i).symm) (le_refl W)
  have hW : (φ.appLE W W hφ).hom g
      = g + conormalSection hsq W
          ((Scheme.Modules.Hom.app (homOfAut hst sq φ hq cb) (i ⁻¹ᵁ W)).hom
            ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g))) := by
    rw [homOfAut_app_d hst sq φ hq cb W g,
      conormalSection_conormalClass_liftDiffSection hsq cb W hφ g]
    ring
  have hnat := congr($((homOfAut hst sq φ hq cb).mapPresheaf.naturality
      (homOfLE (i.preimage_mono hA)).op)
    ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g)))
  refine (map_appLE_apply φ hφ hA g).symm.trans ?_
  rw [hW, map_add, conormalSection_map hsq hA]
  exact congrArg (fun z => (X'.presheaf.map (homOfLE hA).op).hom g + conormalSection hsq V z)
    hnat.symm

/-- **The derivation attached to the automorphism attached to `α` is `α` again.** -/
theorem homOfAut_autOfHom (α : Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) :
    homOfAut hst sq (autOfHom hsq sq.w α)
        ((Category.id_comp f').trans (comp_autOfHom hsq sq.w α).symm)
        (comm_autOfHom hsq sq.w α) = α := by
  have := isIso_relativeDifferentialsMapBase i t f f' hst sq
  refine (cancel_epi (Scheme.Hom.relativeDifferentialsMap i f' f t sq.w)).mp ?_
  rw [relativeDifferentialsMap_comp_homOfAut]
  refine ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
    (Scheme.Hom.relativeDifferentials f') (conormalModules i)).injective ?_
  refine hom_ext_universalRelativeDerivation f' fun W g => ?_
  rw [homEquiv_diagonalConormalSheafMap_d_modules
      ((Category.id_comp f').trans (comp_autOfHom hsq sq.w α).symm)
      (comm_autOfHom hsq sq.w α) (Category.comp_id i) W g,
    homEquiv_relativeDifferentialsMap_comp_d sq α W g]
  refine conormalSection_injective hsq W ?_
  rw [conormalSection_conormalClass_liftDiffSection hsq (comm_autOfHom hsq sq.w α) W
      (le_refl W) g,
    autOfHom_appLE_self hsq sq.w α W (le_refl W) g]
  ring

include hsq hst sq in
/-- **Every endomorphism of `X'` over `S'` reducing to the identity on `X` is an isomorphism.**
It is the action of its own derivation, and that action is invertible with inverse the action of
the negated derivation.  This is why the set of [Stacks Project, Tag 0D14] part (2) may be read
either as the endomorphisms or as the automorphisms of `X'` with those two properties. -/
@[sga "3 III 2.9" "special case"]
theorem isIso_of_comm_of_isPullback (φ : X' ⟶ X') (hq : φ ≫ f' = f') (cb : i ≫ φ = i) :
    IsIso φ := by
  rw [← autOfHom_homOfAut hsq hst sq φ ((Category.id_comp f').trans hq.symm) cb]
  exact isIso_autOfHom _ _ _

/-- **The automorphisms of `X'` over `S'` reducing to the identity on `X`, as `𝒪_X`-linear maps
`Ω_{X/S} ⟶ 𝒞_{X/X'}`.** -/
def derivationAutEquiv :
    (Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) ≃
      {φ : X' ≅ X' // i ≫ φ.hom = i ∧ φ.hom ≫ f' = f'} where
  toFun α := ⟨@asIso _ _ _ _ (autOfHom hsq sq.w α) (isIso_autOfHom hsq sq.w α),
    comm_autOfHom hsq sq.w α, comp_autOfHom hsq sq.w α⟩
  invFun φ := homOfAut hst sq φ.1.hom ((Category.id_comp f').trans φ.2.2.symm) φ.2.1
  left_inv α := homOfAut_autOfHom hsq hst sq α
  right_inv φ :=
    Subtype.ext (CategoryTheory.Iso.ext (autOfHom_homOfAut hsq hst sq φ.1.hom _ φ.2.1))

end Inverse

/-! ### [Stacks Project, Tag 0D14] part (2) -/

/-- **[Stacks Project, Tag 0D14], part (2).** Let `S ⊂ S'` be a first order thickening of
schemes, let `f : X ⟶ S` be a morphism, let `f' : X' ⟶ S'` be flat and let `i : X ⟶ X'` make the
square cartesian, so that `X = X' ×_{S'} S` over `S`.  Then the set of automorphisms
`φ : X' ⟶ X'` over `S'` which reduce to the identity on `X' ×_{S'} S` is

`Ext⁰_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`.

The bijection is not merely asserted: its value on a class `ξ` is the morphism
`Stacks.Thickenings.autOfHom` for the `𝒪_X`-linear map
`Stacks.Thickenings.flatThickeningActingGroupAddEquiv ... ξ : Ω_{X/S} ⟶ 𝒞_{X/X'}`, whose
comorphism is `g ↦ g + α(d_{X/S}(i^♯ g))` by
`Stacks.Thickenings.flatThickeningAutEquiv_apply_appLE`.  In particular the identity
automorphism corresponds to `0` (`Stacks.Thickenings.autOfHom_zero`) and composition to
addition (`Stacks.Thickenings.autOfHom_add`), so the bijection is an isomorphism of groups. -/
@[stacks 0D14]
def flatThickeningAutEquiv (i : X ⟶ X') (t : S ⟶ S')
    [AlgebraicGeometry.IsClosedImmersion t] (f : X ⟶ S) (f' : X' ⟶ S') [Flat f']
    (hst : t.ker ^ 2 = ⊥) (sq : IsPullback i f f' t) :
    AlgebraicGeometry.Scheme.naiveCotangentExt f (pullbackConormalModule f t) 0 ≃
      {φ : X' ≅ X' // i ≫ φ.hom = i ∧ φ.hom ≫ f' = f'} :=
  haveI : AlgebraicGeometry.IsClosedImmersion i :=
    MorphismProperty.of_isPullback sq.flip inferInstance
  (flatThickeningActingGroupAddEquiv i t f f' sq).toEquiv.trans
    (derivationAutEquiv (ker_pow_eq_bot_of_isPullback sq inferInstance hst) hst sq)

/-- **The comorphism of the automorphism that [Stacks Project, Tag 0D14] part (2) attaches to a
degree-zero `Ext`-class**, over an arbitrary pair of opens: it is the identity perturbed by the
derivation the class corresponds to under
`Stacks.Thickenings.flatThickeningActingGroupAddEquiv`. -/
theorem flatThickeningAutEquiv_apply_appLE (i : X ⟶ X') (t : S ⟶ S')
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion t]
    (f : X ⟶ S) (f' : X' ⟶ S') [Flat f'] (hsq : i.ker ^ 2 = ⊥) (hst : t.ker ^ 2 = ⊥)
    (sq : IsPullback i f f' t)
    (ξ : AlgebraicGeometry.Scheme.naiveCotangentExt f (pullbackConormalModule f t) 0)
    (W V : X'.Opens) (hA : V ≤ W) (g : Γ(X', W)) :
    ((flatThickeningAutEquiv i t f f' hst sq ξ).1.hom.appLE W V hA).hom g
      = (X'.presheaf.map (homOfLE hA).op).hom g
        + conormalSection hsq V ((Scheme.Modules.Hom.app
            (flatThickeningActingGroupAddEquiv i t f f' sq ξ) (i ⁻¹ᵁ V)).hom
          ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE (i.preimage_mono hA)).op
            ((Scheme.Hom.universalRelativeDerivation f).d ((i.app W).hom g)))) :=
  autOfHom_appLE hsq sq.w (flatThickeningActingGroupAddEquiv i t f f' sq ξ) W V hA g

end Stacks.Thickenings

end
