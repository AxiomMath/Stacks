module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSectionShrink

/-!
# The trivialized quotient is compatible with shrinking the open

`Stacks.RelativeProj.homOfLE_comp_localSection_of_trivializedQuotientHom_res` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSectionShrink.lean` reduces the
compatibility of `Stacks.RelativeProj.localSection` with shrinking an affine open `V` of the base
to `W ⊆ V` to a single equation of morphisms of sheaves of modules on `X`, its hypothesis `hκ`:

`trivializedQuotientHom V q e ≫ pushforwardUnitRes V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV)`
`= trivializedQuotientHom W q e''`

for *one* trivialization `e''` of `𝓛` over `W`. **This file proves that equation**, and with it
`Stacks.RelativeProj.homOfLE_comp_localSection_eq`: the local section over `V`, restricted to an
affine open `W ⊆ V`, is the local section over `W`, with no hypothesis left.

## How the equation is proved

`Stacks.RelativeProj.trivializedQuotientHom` takes a trivialization on the *restricted site*
`Over U` and crosses to the open subscheme by
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`. The equation is
about what happens after the crossing, so it is stated and proved for a trivialization already
on the open subscheme — `Stacks.RelativeProj.trivializedQuotientHomOf`, of which
`trivializedQuotientHom` is the special case at a crossed trivialization, by `rfl` — and then
transported back across the crossing. The transport is possible because **the crossing is
surjective on trivializations**: `Scheme.Modules.overEquiv U` is an equivalence and the other two
factors of `restrictIsoUnitOfOverIsoUnit` are fixed isomorphisms, so every trivialization on the
open subscheme is a crossed one
(`ProjInvertibleLocus.exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq`).
This is what makes the `over` site disappear from the problem; the comparison of
`restrictIsoUnitOfOverIsoUnit` at `V` and at `W` through
`AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv`, which had been
priced as the way in, is not needed.

On the open subscheme the restricted trivialization is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictTrivializationOfLE`, built from Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`,
`…Scheme.Modules.restrictFunctorCongr` and `…Scheme.Modules.restrictUnitIso` along
`X.homOfLE hWV`. The equation itself is then checked on sections, where every ingredient is
either `rfl` or one naturality square: the two `restrictFunctor` comparison isomorphisms are
presheaf restrictions along an equality of opens, `restrictUnitIso` is
`AlgebraicGeometry.Scheme.Hom.appIso`, and `AlgebraicGeometry.Scheme.Hom.map_appLE` identifies
`appIso` composed with a restriction as the `appLE` that
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitRes` contributes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictTrivializationOfLE`: **the restriction of
  a trivialization along `W ≤ V`**, on the open subschemes.
* `Stacks.RelativeProj.trivializedQuotientHomOf`: the trivialized quotient of a trivialization on
  the open subscheme — `Stacks.RelativeProj.trivializedQuotientHom` with the crossing taken out.

## Main results

* `ProjInvertibleLocus.exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq`:
  **every trivialization on the open subscheme comes from one on the restricted site.**
* `Stacks.RelativeProj.trivializedQuotientHomOf_restrict`: **`hκ`**, for the restricted
  trivialization.
* `Stacks.RelativeProj.exists_trivializedQuotientHom_res`: `hκ` in the form
  `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSectionShrink.lean` consumes.
* `Stacks.RelativeProj.homOfLE_comp_localSection_eq`: **the local section over `V`, restricted to
  an affine open `W ⊆ V`, is the local section over `W`.** This is the agreement on overlaps that
  a gluing argument consumes, with nothing left to assume.

## Implementation notes

`rw` and `simp` are unusable on the goals about isomorphisms of `AlgebraicGeometry.Scheme.Modules`:
that is a `def` carrying its own `Category` instance, and the goals are reported as not
type-correct at `implicit` transparency, so even `Iso.trans_hom` does not fire. The categorical
algebra of the surjectivity proof is therefore factored out into
`Stacks.CategoryTheory.trans_symm_trans_symm_trans`, stated in an arbitrary category where `simp`
works, and applied in one step.

Once the goal is about sections it leaves that category, and `rw` is usable again; the remaining
proofs are term-style only where a lemma's implicit ring sheaf has to be found up to the
difference between `X.Modules` and `SheafOfModules X.ringCatSheaf`, which unification solves at
default transparency but `rw` does not.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between the sections of
`π : 𝐏(ℰ) ⟶ X` and the invertible quotients of `ℰ`; the compatibility of a local construction
with shrinking the open it is built over is not a covering part of it.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u

namespace Stacks.CategoryTheory

/-- **Conjugating an isomorphism by two others and cancelling**:
`A ≪≫ (A.symm ≪≫ t ≪≫ B.symm) ≪≫ B` is `t`. Stated in an arbitrary category so that it can be
applied in one step inside a category whose instance `rw` and `simp` cannot see through. -/
public theorem trans_symm_trans_symm_trans {C : Type*}
    [_root_.CategoryTheory.Category C] {a b c d : C} (A : a ≅ b) (B : c ≅ d) (t : a ≅ d) :
    A ≪≫ (A.symm ≪≫ t ≪≫ B.symm) ≪≫ B = t := by
  ext
  simp

end Stacks.CategoryTheory

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}} (U : X.Opens)

/-- **Every trivialization of `M` on the open subscheme `U` is the crossing of one on the
restricted site `Over U`.** `AlgebraicGeometry.Scheme.Modules.overEquiv U` is an equivalence and
the two other factors of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit` are fixed
isomorphisms, so the required trivialization is the preimage, under the fully faithful functor of
that equivalence, of the evident composite.

This is what lets a statement about trivialized quotients be proved on the open subscheme and
then read back on the restricted site, where
`Stacks.RelativeProj.trivializedQuotientHom` takes its argument. -/
public theorem exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq (M : X.Modules)
    (t : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ∃ e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U),
      restrictIsoUnitOfOverIsoUnit U M e = t :=
  ⟨(Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
      ((restrictIsoOverEquiv U M).symm ≪≫ t ≪≫
        (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm),
    Eq.trans
      (congrArg (fun i => restrictIsoOverEquiv U M ≪≫ i ≪≫
          TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf)
        (Iso.ext ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage
          ((restrictIsoOverEquiv U M).symm ≪≫ t ≪≫
            (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm).hom)))
      (Stacks.CategoryTheory.trans_symm_trans_symm_trans _ _ t)⟩

/-- **The restriction of a trivialization along an inclusion of opens `W ≤ V`**, both read on the
open subschemes: restrict along `X.homOfLE hWV`, identify the iterated restriction with the
restriction along `W.ι` (`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`…restrictFunctorCongr`, using `X.homOfLE_ι`), and carry the structure sheaf to the structure
sheaf (`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`). -/
public def restrictTrivializationOfLE {W V : X.Opens} (hWV : W ≤ V) (M : X.Modules)
    (t : (Scheme.Modules.restrictFunctor V.ι).obj M ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor W.ι).obj M ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWV)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hWV) V.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hWV)).mapIso t ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE hWV)

/-- **The restricted trivialization on sections over `T`**: restrict the section from `W.ι ''ᵁ T`
to `V.ι ''ᵁ (X.homOfLE hWV ''ᵁ T)` — the same open, written the other way — apply the
trivialization over `V` there, and read the result on `W` through
`AlgebraicGeometry.Scheme.Hom.appIso`.

The last two factors of `restrictTrivializationOfLE` are already this on sections; the first two
are presheaf restrictions along an equality of opens, and compose into one because the
morphisms of opens with given endpoints are a subsingleton. -/
public theorem restrictTrivializationOfLE_hom_app {W V : X.Opens} (hWV : W ≤ V) (M : X.Modules)
    (t : (Scheme.Modules.restrictFunctor V.ι).obj M ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) (T : W.toScheme.Opens)
    (x : ((Scheme.Modules.restrictFunctor W.ι).obj M).val.obj (op T))
    (hle : V.ι ''ᵁ (X.homOfLE hWV ''ᵁ T) ≤ W.ι ''ᵁ T) :
    (restrictTrivializationOfLE hWV M t).hom.val.app (op T) x =
      ((X.homOfLE hWV).appIso T).hom
        (t.hom.val.app (op (X.homOfLE hWV ''ᵁ T)) (M.val.map (homOfLE hle).op x)) := by
  refine congrArg (fun z => ((X.homOfLE hWV).appIso T).hom
      (t.hom.val.app (op (X.homOfLE hWV ''ᵁ T)) z)) ?_
  have hcomp : (X.homOfLE hWV ≫ V.ι) ''ᵁ T = V.ι ''ᵁ (X.homOfLE hWV ''ᵁ T) :=
    Scheme.Hom.comp_image (X.homOfLE hWV) V.ι T
  have h1 : V.ι ''ᵁ (X.homOfLE hWV ''ᵁ T) ≤ (X.homOfLE hWV ≫ V.ι) ''ᵁ T := le_of_eq hcomp.symm
  have h2 : (X.homOfLE hWV ≫ V.ι) ''ᵁ T ≤ W.ι ''ᵁ T := (le_of_eq hcomp).trans hle
  exact (PresheafOfModules.map_comp_apply M.val (homOfLE h2).op (homOfLE h1).op x).symm

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

namespace Stacks.RelativeProj

open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}} {F L : X.Modules}

/-- **The trivialized quotient of a trivialization on the open subscheme.** This is
`Stacks.RelativeProj.trivializedQuotientHom` with the crossing from the restricted site taken
out: the restriction of `q` to `U`, followed by the trivialization there, transposed across the
adjunction between restriction and pushforward along `U.ι`. -/
public def trivializedQuotientHomOf (U : X.Opens) (q : F ⟶ L)
    (t : (Scheme.Modules.restrictFunctor U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) : F ⟶ pushforwardUnit U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).homEquiv F
      (SheafOfModules.unit U.toScheme.ringCatSheaf)
    ((Scheme.Modules.restrictFunctor U.ι).map q ≫ t.hom)

/-- `Stacks.RelativeProj.trivializedQuotientHom` is
`Stacks.RelativeProj.trivializedQuotientHomOf` at the crossed trivialization. True by `rfl`; the
crossing is the only difference between the two definitions. -/
public theorem trivializedQuotientHom_eq (U : X.Opens) (q : F ⟶ L)
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializedQuotientHom U q e =
      trivializedQuotientHomOf U q (restrictIsoUnitOfOverIsoUnit U L e) :=
  rfl

/-- **`κ` on sections over an open `S`**, read in the ring of functions of the open subscheme:
restrict from `S` to the part of `S` inside `U`, then apply `q` and the trivialization there.
Every factor of the adjunction's unit is a presheaf restriction map, so this holds by `rfl`. -/
public theorem ofPushforwardUnit_trivializedQuotientHomOf_app (U : X.Opens) (q : F ⟶ L)
    (t : (Scheme.Modules.restrictFunctor U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) (S : X.Opensᵒᵖ) (m : F.val.obj S) :
    ofPushforwardUnit U.ι ((trivializedQuotientHomOf U q t).val.app S m) =
      t.hom.val.app (op (U.ι ⁻¹ᵁ S.unop))
        (q.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ S.unop)))
          (F.val.map (homOfLE (U.ι.image_preimage_le S.unop)).op m)) :=
  rfl

/-- **The trivialized quotient over `V`, followed by restriction of functions along
`X.homOfLE hWV`, is the trivialized quotient over `W` of the restricted trivialization.**

Checked on sections. Both sides apply `q` and then the trivialization over `V`, the right-hand
side over the smaller open; the comparison is the naturality of the trivialization for the
inclusion `X.homOfLE hWV ''ᵁ (W.ι ⁻¹ᵁ S) ≤ V.ι ⁻¹ᵁ S`, that of `q` for the corresponding
inclusion of opens of `X`, and `AlgebraicGeometry.Scheme.Hom.map_appLE` for the structure
sheaves. -/
public theorem trivializedQuotientHomOf_restrict {W V : X.Opens} (hWV : W ≤ V) (q : F ⟶ L)
    (t : (Scheme.Modules.restrictFunctor V.ι).obj L ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) :
    trivializedQuotientHomOf V q t ≫
        pushforwardUnitRes V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) =
      trivializedQuotientHomOf W q (restrictTrivializationOfLE hWV L t) := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.Hom.ext ?_
  funext S
  ext m
  refine ofPushforwardUnit_injective W.ι ?_
  refine Eq.trans (ofPushforwardUnit_pushforwardUnitRes_app V.ι (X.homOfLE hWV)
      (X.homOfLE_ι hWV) S ((trivializedQuotientHomOf V q t).val.app S m)) ?_
  refine Eq.trans (congrArg (resAppLE V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) S.unop).hom
    (ofPushforwardUnit_trivializedQuotientHomOf_app V q t S m)) ?_
  refine Eq.trans ?_ (ofPushforwardUnit_trivializedQuotientHomOf_app W q
    (restrictTrivializationOfLE hWV L t) S m).symm
  have himg : V.ι ''ᵁ (X.homOfLE hWV ''ᵁ (W.ι ⁻¹ᵁ S.unop)) = W.ι ''ᵁ (W.ι ⁻¹ᵁ S.unop) := by
    simp [← Scheme.Hom.comp_image]
  have hBA : X.homOfLE hWV ''ᵁ (W.ι ⁻¹ᵁ S.unop) ≤ V.ι ⁻¹ᵁ S.unop := by
    rw [← Scheme.Hom.preimage_image_eq V.ι (X.homOfLE hWV ''ᵁ (W.ι ⁻¹ᵁ S.unop)), himg]
    exact fun x hx => W.ι.image_preimage_le S.unop hx
  refine Eq.trans ?_ (restrictTrivializationOfLE_hom_app hWV L t (W.ι ⁻¹ᵁ S.unop) _ himg.le).symm
  have hinner : (L.val.map (homOfLE himg.le).op)
        ((q.val.app (op (W.ι ''ᵁ W.ι ⁻¹ᵁ S.unop)))
          ((F.val.map (homOfLE (W.ι.image_preimage_le S.unop)).op) m)) =
      ((Scheme.Modules.restrictFunctor V.ι).obj L).val.map (homOfLE hBA).op
        ((q.val.app (op (V.ι ''ᵁ V.ι ⁻¹ᵁ S.unop)))
          ((F.val.map (homOfLE (V.ι.image_preimage_le S.unop)).op) m)) := by
    refine Eq.trans (PresheafOfModules.naturality_apply q.val (homOfLE himg.le).op
      ((F.val.map (homOfLE (W.ι.image_preimage_le S.unop)).op) m)).symm ?_
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply q.val
      (V.ι.opensFunctor.map (homOfLE hBA)).op
      ((F.val.map (homOfLE (V.ι.image_preimage_le S.unop)).op) m))
    refine congrArg (q.val.app (op (V.ι ''ᵁ (X.homOfLE hWV ''ᵁ W.ι ⁻¹ᵁ S.unop)))) ?_
    exact (PresheafOfModules.map_comp_apply F.val (homOfLE (W.ι.image_preimage_le S.unop)).op
        (homOfLE himg.le).op m).symm.trans
      (PresheafOfModules.map_comp_apply F.val (homOfLE (V.ι.image_preimage_le S.unop)).op
        (V.ι.opensFunctor.map (homOfLE hBA)).op m)
  have hmaps : V.toScheme.presheaf.map (homOfLE hBA).op ≫
      ((X.homOfLE hWV).appIso (W.ι ⁻¹ᵁ S.unop)).hom =
      resAppLE V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) S.unop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rfl
  refine Eq.trans ?_ (congrArg (fun z => ((X.homOfLE hWV).appIso (W.ι ⁻¹ᵁ S.unop)).hom
    (t.hom.val.app (op (X.homOfLE hWV ''ᵁ W.ι ⁻¹ᵁ S.unop)) z)) hinner).symm
  refine Eq.trans ?_ (congrArg ((X.homOfLE hWV).appIso (W.ι ⁻¹ᵁ S.unop)).hom
    (PresheafOfModules.naturality_apply t.hom.val (homOfLE hBA).op
      ((q.val.app (op (V.ι ''ᵁ V.ι ⁻¹ᵁ S.unop)))
        ((F.val.map (homOfLE (V.ι.image_preimage_le S.unop)).op) m)))).symm
  exact (congrArg (fun φ : V.toScheme.presheaf.obj (op (V.ι ⁻¹ᵁ S.unop)) ⟶
      W.toScheme.presheaf.obj (op (W.ι ⁻¹ᵁ S.unop)) =>
    (ConcreteCategory.hom φ)
      ((ConcreteCategory.hom (t.hom.val.app (op (V.ι ⁻¹ᵁ S.unop))))
        ((ConcreteCategory.hom (q.val.app (op (V.ι ''ᵁ V.ι ⁻¹ᵁ S.unop))))
          ((ConcreteCategory.hom (F.val.map (homOfLE (V.ι.image_preimage_le S.unop)).op))
            m)))) hmaps).symm

/-- **`hκ`**: there is a trivialization of `𝓛` over `W` whose trivialized quotient is the one
over `V` followed by restriction of functions. It is the restriction of the given trivialization,
read back on the restricted site through the surjectivity of the crossing.

This is the hypothesis of
`Stacks.RelativeProj.homOfLE_comp_localSection_of_trivializedQuotientHom_res`. -/
public theorem exists_trivializedQuotientHom_res {W V : X.Opens} (hWV : W ≤ V) (q : F ⟶ L)
    (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    ∃ e'' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W),
      trivializedQuotientHom V q e ≫
          pushforwardUnitRes V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) =
        trivializedQuotientHom W q e'' := by
  obtain ⟨e'', he''⟩ := exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq W L
    (restrictTrivializationOfLE hWV L (restrictIsoUnitOfOverIsoUnit V L e))
  refine ⟨e'', Eq.trans (trivializedQuotientHomOf_restrict hWV q
    (restrictIsoUnitOfOverIsoUnit V L e)) ?_⟩
  exact congrArg (trivializedQuotientHomOf W q) he''.symm

/-- **The local section of `π : 𝐏(ℰ) ⟶ X` over `V`, restricted to an affine open `W ⊆ V`, is the
local section over `W`.** No hypothesis beyond affineness of the two opens and surjectivity of
`q` on their sections: the trivializations over `V` and over `W` are arbitrary, the one over `W`
being absorbed by `Stacks.RelativeProj.localSection_congr`.

This is the agreement on overlaps that a gluing argument consumes. -/
public theorem homOfLE_comp_localSection_eq {W V : X.Opens} [F.IsQuasicoherent] (q : F ⟶ L)
    (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (e' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V)))
    (hq' : Function.Surjective (q.val.app (op W))) :
    X.homOfLE hWV ≫ localSection V q e hV hq = localSection W q e' hW hq' :=
  let ⟨e'', he''⟩ := exists_trivializedQuotientHom_res hWV q e
  homOfLE_comp_localSection_of_trivializedQuotientHom_res q e e' hWV hW hV hq hq' e'' he''

end Stacks.RelativeProj

end
