module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits

/-!
# Tensoring commutes with the coproduct model of extension from a slice

Let `O` be a presheaf of commutative rings on a category `C` and let `U` be an object of `C`.
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SliceAdjunctions.lean` builds extension of
presheaves of modules from the slice `C/U`, `j_{U!}`, as the objectwise coproduct
`(j_{U!}M)(X) = ∐_{p : X ⟶ U} M(p)`. This file proves that it commutes with tensoring by a
presheaf of modules on `C`:

`j_{U!} M ⊗ F ≅ j_{U!} (M ⊗ j_U^* F)`.

Objectwise this is the distributivity of the tensor product over that coproduct, and it holds
because `· ⊗ F(X)` is a left adjoint and therefore preserves the coproduct.

## Universes

Every universe is free: the objects of `C` lie in `u`, its morphisms in `v`, the sections of `O`
in `w`, and the modules in a **free parameter `a`**, subject only to `UnivLE.{v, a}` — which is
what the coproduct over the hom-set `X ⟶ U : Type v` needs, and is the only hypothesis the
coproduct model of `j_{U!}` itself carries.

That free parameter is the point of this file.
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SliceExtensionTensor.lean` already proves the
same comparison, `Stacks.Sites.OverModules.FormulaExtension.extensionTensorIso`, for the
`DirectSum` model of `j_{U!}`; but that model writes its sections as a `DFinsupp` over the
hom-set, so its module universe is pinned to the compound form `max v m` and cannot be a free
atom. A consumer that needs the module universe to stay a bare variable — so that instantiating
it leaves the syntactic form of the statement unchanged — has to use the coproduct model, and
this file is the comparison it was missing.

## Main definitions

* `Stacks.Sites.OverModules.extensionTensorPullback`: the presheaf of modules `M ⊗ j_U^* F` on
  the slice, whose extension the comparison lands in.
* `Stacks.Sites.OverModules.extensionTensorι`: the inclusion of one summand of the target into
  the sections of `j_{U!}M ⊗ F`.
* `Stacks.Sites.OverModules.extensionTensorFiberIso`: the comparison on sections over one
  object of `C`, which is where the colimit-preservation is spent.
* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.sectionTensorRightSigmaIso`: tensoring
  modules on the right by a fixed module commutes with a coproduct.

## Main results

* `Stacks.Sites.OverModules.extensionTensorObjIso`: the comparison isomorphism above.
* `Stacks.Sites.OverModules.extensionTensorObjIso_hom_ι`: its value on a pure tensor of an
  element of one summand, which is what a consumer computing with it needs.
* `Stacks.Sites.OverModules.extensionTensorIso`: the comparison as a natural isomorphism of
  functors, natural in the module on the slice.
* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.preservesColimit_sectionTensorRight`:
  tensoring modules on the right by a fixed module preserves every colimit.

## Implementation notes

The objectwise tensor product and the right tensor functor are the ones of
`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`, whose two module universes and ring
universe are independent, and the objectwise right tensor functor on modules is
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.sectionTensorRight` of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/ObjectwiseFlat.lean`, which is already stated
with the ring and module carriers in independent universes. Nothing here declares a third model
of the extension functor, a second objectwise tensor product, or a second right tensor functor
on modules.

**Every morphism whose source or target needs an identification between two spellings of one
carrier is given a name** — `extensionTensorι`, `extensionTensorRestriction`,
`extensionTensorMap`, `extensionTensorPullbackMap`, `extensionTensorExtensionMap` — so that the
identification is performed once, at definition time, where the elaborator can still see it. The
sections of `M ⊗ j_U^*F` over the slice object `p : X ⟶ U` carry the ring `O(p)` while the
sections of `j_{U!}M ⊗ F` over `X` carry `O(X)`, and the sections of `j_{U!}N` over `X` are the
coproduct of the extension formula only after `Adjunction.leftAdjointOfEquiv` is unfolded. Those
identifications are definitional, but they are not available to a `rw`, which matches
syntactically — a tactic goal that mixes the two spellings is not even type-correct at the
transparency `rw` works at. This is the same discipline, and for the same reason, as the one
recorded in the implementation notes of `SliceAdjunctions.lean`.

The one reusable step is `extensionTensor_hom_ext`: because `· ⊗ F(X)` preserves the coproduct,
a morphism out of `(j_{U!}M)(X) ⊗ F(X)` is determined by its restrictions along the summand
inclusions `extensionTensorι`. Both naturality squares below — the one making the objectwise
comparison a morphism of presheaves, and the one making it natural in `M` — are discharged
through it, so no element of a coproduct of modules is ever named.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe v u w a t t'

namespace AlgebraicGeometry.SheafOfModules.PresheafOfModules

open Stacks.SheafOfModules.TensorColimits (moduleTensorLeft moduleTensorAdjunction)

variable {R : Type w} [CommRing R]

/-- Tensoring modules on the right by `N` agrees with tensoring on the left by `N`, by the
symmetry of the tensor product of modules. -/
noncomputable def sectionTensorRightIsoLeft (N : ModuleCat.{a} R) :
    sectionTensorRight R N ≅ moduleTensorLeft N :=
  NatIso.ofComponents (fun M => (TensorProduct.comm R M N).toModuleIso)
    fun _ => ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

/-- **Tensoring modules on the right by a fixed module preserves every colimit.** It is the
symmetry of tensoring on the left, which is a left adjoint, its right adjoint being the hom
functor out of the fixed module. -/
instance preservesColimit_sectionTensorRight {J : Type t} [Category.{t'} J]
    (K : J ⥤ ModuleCat.{a} R) (N : ModuleCat.{a} R) :
    PreservesColimit K (sectionTensorRight R N) :=
  letI : PreservesColimitsOfSize.{t', t} (moduleTensorLeft N) :=
    (moduleTensorAdjunction N).leftAdjoint_preservesColimits
  preservesColimit_of_natIso K (sectionTensorRightIsoLeft N).symm

/-- **Tensoring modules on the right by `N` commutes with a coproduct**, since it preserves
colimits.

The index type lies in its own universe `t`, bounded by the module universe — which is what
makes both coproducts exist, and is the only hypothesis the coproduct model of extension from a
slice carries either. -/
noncomputable def sectionTensorRightSigmaIso {ι : Type t} [UnivLE.{t, a}]
    (fam : ι → ModuleCat.{a} R) (N : ModuleCat.{a} R) :
    (sectionTensorRight R N).obj (∐ fam) ≅ ∐ fun i => (sectionTensorRight R N).obj (fam i) :=
  preservesColimitIso (sectionTensorRight R N) (Discrete.functor fam) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- The comparison of `sectionTensorRightSigmaIso` carries the image of a summand inclusion to
the corresponding summand inclusion. -/
@[reassoc]
lemma map_ι_comp_sectionTensorRightSigmaIso_hom {ι : Type t} [UnivLE.{t, a}]
    (fam : ι → ModuleCat.{a} R) (N : ModuleCat.{a} R) (i : ι) :
    (sectionTensorRight R N).map (Sigma.ι fam i) ≫ (sectionTensorRightSigmaIso fam N).hom =
      Sigma.ι (fun j => (sectionTensorRight R N).obj (fam j)) i := by
  simp [sectionTensorRightSigmaIso]

/-- The inverse form of `map_ι_comp_sectionTensorRightSigmaIso_hom`. -/
@[reassoc]
lemma ι_comp_sectionTensorRightSigmaIso_inv {ι : Type t} [UnivLE.{t, a}]
    (fam : ι → ModuleCat.{a} R) (N : ModuleCat.{a} R) (i : ι) :
    Sigma.ι (fun j => (sectionTensorRight R N).obj (fam j)) i ≫
        (sectionTensorRightSigmaIso fam N).inv =
      (sectionTensorRight R N).map (Sigma.ι fam i) :=
  (Iso.comp_inv_eq _).2 (map_ι_comp_sectionTensorRightSigmaIso_hom fam N i).symm

end AlgebraicGeometry.SheafOfModules.PresheafOfModules

namespace Stacks.Sites.OverModules

open AlgebraicGeometry.SheafOfModules.PresheafOfModules (sectionTensorRight
  sectionTensorRightSigmaIso map_ι_comp_sectionTensorRightSigmaIso_hom
  ι_comp_sectionTensorRightSigmaIso_inv tensorRight)

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) [UnivLE.{v, a}]
  (F : PresheafOfModules.{a, v, u, w} (ringPresheaf O))

section Fixed

variable (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf (ringPresheaf O) U))

/-- The presheaf of modules `M ⊗ j_U^* F` on the slice over `U`, whose extension the tensor
product with `F` of the extension of `M` is compared to. -/
noncomputable abbrev extensionTensorPullback :
    PresheafOfModules.{a, v, max u v, w} (overRingPresheaf (ringPresheaf O) U) :=
  (tensorRight (O := (Over.forget U).op ⋙ O)
    ((restrictionFunctor (ringPresheaf O) U).obj F)).obj M

/-- The inclusion of the summand indexed by `p : X ⟶ U` into the sections of `j_{U!}M ⊗ F` over
`X`: the inclusion of the summand of `j_{U!}M`, tensored with the identity of `F(X)`, with its
source and target spelled as tensor products at `X`. -/
noncomputable def extensionTensorι (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (extensionSummands (ringPresheaf O) U M X p) ⟶
      (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) :=
  (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map
    (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p)

/-- The restriction map of `j_{U!}M ⊗ F`, with its source and target spelled through the
coproducts of the extension formula. -/
noncomputable def extensionTensorRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).obj
        ((sectionTensorRight ((ringPresheaf O).obj Y) (F.obj Y)).obj
          (∐ extensionSummands (ringPresheaf O) U M Y)) :=
  ((tensorRight (O := O) F).obj ((extensionFunctor (ringPresheaf O) U).obj M)).map f

/-- **Tensoring by `F(X)` distributes over the coproduct of the extension formula.** The
sections over `X` of `j_{U!}M ⊗ F` are the sections over `X` of the extension of
`M ⊗ j_U^* F`: both are the coproduct over the arrows `p : X ⟶ U` of `M(p) ⊗ F(X)`, and
tensoring commutes with that coproduct because it is a left adjoint. -/
noncomputable def extensionTensorFiberIso (X : Cᵒᵖ) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) ≅
      ∐ extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X :=
  sectionTensorRightSigmaIso (extensionSummands (ringPresheaf O) U M X) (F.obj X)

/-- The comparison on sections over `X`, precomposed with the inclusion of the summand indexed
by `p`, is the inclusion of the corresponding summand of the target. -/
@[reassoc]
lemma extensionTensorι_comp_extensionTensorFiberIso_hom (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    extensionTensorι O U F M X p ≫ (extensionTensorFiberIso O U F M X).hom =
      Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p :=
  map_ι_comp_sectionTensorRightSigmaIso_hom
    (extensionSummands (ringPresheaf O) U M X) (F.obj X) p

/-- The inverse form of `extensionTensorι_comp_extensionTensorFiberIso_hom`. -/
@[reassoc]
lemma ι_comp_extensionTensorFiberIso_inv (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p ≫
        (extensionTensorFiberIso O U F M X).inv =
      extensionTensorι O U F M X p :=
  ι_comp_sectionTensorRightSigmaIso_inv
    (extensionSummands (ringPresheaf O) U M X) (F.obj X) p

/-- **A morphism out of the sections of `j_{U!}M ⊗ F` over `X` is determined by its
restrictions to the summands.** Tensoring preserves the coproduct of the extension formula, so
the summand inclusions `extensionTensorι` are jointly epimorphic. Both naturality squares below
are discharged through this, which is why no element of a coproduct of modules is named. -/
lemma extensionTensor_hom_ext {X : Cᵒᵖ} {Z : ModuleCat.{a, w} ((ringPresheaf O).obj X)}
    (g₁ g₂ : (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
      (∐ extensionSummands (ringPresheaf O) U M X) ⟶ Z)
    (h : ∀ p : X.unop ⟶ U,
      extensionTensorι O U F M X p ≫ g₁ = extensionTensorι O U F M X p ≫ g₂) :
    g₁ = g₂ := by
  rw [← cancel_epi (extensionTensorFiberIso O U F M X).inv]
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [ι_comp_extensionTensorFiberIso_inv_assoc, ι_comp_extensionTensorFiberIso_inv_assoc]
  exact h p

/-- The comparison on sections over `X`, on a pure tensor of an element of one summand. -/
lemma extensionTensorFiberIso_hom_tmul (X : Cᵒᵖ) (p : X.unop ⟶ U)
    (x : extensionSummands (ringPresheaf O) U M X p) (y : F.obj X) :
    (extensionTensorFiberIso O U F M X).hom
        (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p x
          ⊗ₜ[(ringPresheaf O).obj X] y) =
      Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p
        (x ⊗ₜ[(ringPresheaf O).obj X] y) := by
  have h := congrArg (fun k : ModuleCat.Hom _ _ => k.hom (x ⊗ₜ[(ringPresheaf O).obj X] y))
    (extensionTensorι_comp_extensionTensorFiberIso_hom O U F M X p)
  exact h

/-- **Tensoring by `F` commutes with extension from the slice over `U`, for the coproduct model
of `j_{U!}`**: `j_{U!}M ⊗ F ≅ j_{U!}(M ⊗ j_U^* F)`.

Objectwise this is the distributivity of the tensor product over the coproduct of the extension
formula, `extensionTensorFiberIso`; the naturality square is checked on each summand, which
`extensionTensor_hom_ext` is enough for, and then on a pure tensor there, where the two
spellings of restriction of scalars are invisible because neither changes the carrier. -/
noncomputable def extensionTensorObjIso :
    (tensorRight (O := O) F).obj ((extensionFunctor (ringPresheaf O) U).obj M) ≅
      (extensionFunctor (ringPresheaf O) U).obj (extensionTensorPullback O U F M) :=
  PresheafOfModules.isoMk (extensionTensorFiberIso O U F M) (by
    intro X Y f
    change extensionTensorRestriction O U F M f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
          (extensionTensorFiberIso O U F M Y).hom =
      (extensionTensorFiberIso O U F M X).hom ≫
        extensionRestriction (ringPresheaf O) U (extensionTensorPullback O U F M) f
    refine extensionTensor_hom_ext O U F M _ _ fun p => ?_
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change (extensionTensorFiberIso O U F M Y).hom
        (extensionRestriction (ringPresheaf O) U M f
            (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p x)
          ⊗ₜ[(ringPresheaf O).obj Y] F.restrictₛₗ f y) =
      extensionRestriction (ringPresheaf O) U (extensionTensorPullback O U F M) f
        ((extensionTensorFiberIso O U F M X).hom
          (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p x
            ⊗ₜ[(ringPresheaf O).obj X] y))
    rw [extensionRestriction_ι_apply (ringPresheaf O) U M f p (f.unop ≫ p) rfl x,
      extensionTensorFiberIso_hom_tmul, extensionTensorFiberIso_hom_tmul,
      extensionRestriction_ι_apply (ringPresheaf O) U (extensionTensorPullback O U F M) f p
        (f.unop ≫ p) rfl (x ⊗ₜ[(ringPresheaf O).obj X] y)]
    rfl)

/-- The component of `extensionTensorObjIso` on a pure tensor of an element of one summand. -/
lemma extensionTensorObjIso_hom_ι (X : Cᵒᵖ) (p : X.unop ⟶ U)
    (x : extensionSummands (ringPresheaf O) U M X p) (y : F.obj X) :
    (extensionTensorObjIso O U F M).hom.app X
        (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p x
          ⊗ₜ[(ringPresheaf O).obj X] y) =
      Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p
        (x ⊗ₜ[(ringPresheaf O).obj X] y) :=
  extensionTensorFiberIso_hom_tmul O U F M X p x y

end Fixed

section Variable

variable {M N : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf (ringPresheaf O) U)}
  (α : M ⟶ N)

/-- `j_{U!}α` on sections over `X`, with its source and target spelled as the coproducts of the
extension formula. -/
noncomputable def extensionMapApp (X : Cᵒᵖ) :
    (∐ extensionSummands (ringPresheaf O) U M X) ⟶
      (∐ extensionSummands (ringPresheaf O) U N X) :=
  ((extensionFunctor (ringPresheaf O) U).map α).app X

/-- `extensionMapApp` on the summand indexed by `p` is the component of `α` there, followed by
the inclusion of that summand. -/
@[reassoc]
lemma ι_comp_extensionMapApp (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands (ringPresheaf O) U M X) p ≫ extensionMapApp O U α X =
      α.app (op (Over.mk p)) ≫ Sigma.ι (extensionSummands (ringPresheaf O) U N X) p :=
  ι_comp_extensionFunctor_map_app (ringPresheaf O) U α X p

/-- The map `j_{U!}M ⊗ F ⟶ j_{U!}N ⊗ F` induced by `α`, on sections over `X`, with its source
and target spelled through the coproducts of the extension formula. -/
noncomputable def extensionTensorMap (X : Cᵒᵖ) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) ⟶
      (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U N X) :=
  (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map (extensionMapApp O U α X)

/-- The map `M ⊗ j_U^*F ⟶ N ⊗ j_U^*F` induced by `α`, on the summand indexed by `p`, with its
source and target spelled as tensor products at `X`. -/
noncomputable def extensionTensorPullbackMap (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (extensionSummands (ringPresheaf O) U M X p) ⟶
      (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (extensionSummands (ringPresheaf O) U N X p) :=
  ((tensorRight (O := (Over.forget U).op ⋙ O)
    ((restrictionFunctor (ringPresheaf O) U).obj F)).map α).app (op (Over.mk p))

/-- The map `j_{U!}(M ⊗ j_U^*F) ⟶ j_{U!}(N ⊗ j_U^*F)` induced by `α`, on sections over `X`. -/
noncomputable def extensionTensorExtensionMap (X : Cᵒᵖ) :
    (∐ extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) ⟶
      (∐ extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F N) X) :=
  ((extensionFunctor (ringPresheaf O) U).map
    ((tensorRight (O := (Over.forget U).op ⋙ O)
      ((restrictionFunctor (ringPresheaf O) U).obj F)).map α)).app X

/-- `extensionTensorMap` on the summand indexed by `p` is `extensionTensorPullbackMap`, followed
by the inclusion of that summand. -/
@[reassoc]
lemma extensionTensorι_comp_extensionTensorMap (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    extensionTensorι O U F M X p ≫ extensionTensorMap O U F α X =
      extensionTensorPullbackMap O U F α X p ≫ extensionTensorι O U F N X p := by
  have h : (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map
        (Sigma.ι (extensionSummands (ringPresheaf O) U M X) p) ≫
      (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map (extensionMapApp O U α X) =
      (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map
          (α.app (op (Over.mk p))) ≫
        (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).map
          (Sigma.ι (extensionSummands (ringPresheaf O) U N X) p) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ι_comp_extensionMapApp]
  exact h

/-- `extensionTensorExtensionMap` on the summand indexed by `p` is
`extensionTensorPullbackMap`, followed by the inclusion of that summand. -/
@[reassoc]
lemma ι_comp_extensionTensorExtensionMap (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p ≫
        extensionTensorExtensionMap O U F α X =
      extensionTensorPullbackMap O U F α X p ≫
        Sigma.ι (extensionSummands (ringPresheaf O) U
          (extensionTensorPullback O U F N) X) p :=
  ι_comp_extensionFunctor_map_app (ringPresheaf O) U _ X p

end Variable

/-- **`extensionTensorObjIso` is natural in the module on the slice**, so the comparison is an
isomorphism of functors: tensoring by `F` after extending from `C/U` is extending from `C/U`
after tensoring by `j_U^* F`. -/
noncomputable def extensionTensorIso :
    extensionFunctor (ringPresheaf O) U ⋙ tensorRight.{v, u, w, a, a} (O := O) F ≅
      tensorRight.{v, max u v, w, a, a} (O := (Over.forget U).op ⋙ O)
          ((restrictionFunctor (ringPresheaf O) U).obj F) ⋙
        extensionFunctor (ringPresheaf O) U := by
  refine NatIso.ofComponents (fun M => extensionTensorObjIso O U F M) fun {M N} α => ?_
  refine PresheafOfModules.hom_ext fun X => ?_
  change extensionTensorMap O U F α X ≫ (extensionTensorFiberIso O U F N X).hom =
    (extensionTensorFiberIso O U F M X).hom ≫ extensionTensorExtensionMap O U F α X
  refine extensionTensor_hom_ext O U F M _ _ fun p => ?_
  rw [extensionTensorι_comp_extensionTensorMap_assoc,
    extensionTensorι_comp_extensionTensorFiberIso_hom,
    extensionTensorι_comp_extensionTensorFiberIso_hom_assoc]
  exact (ι_comp_extensionTensorExtensionMap O U F α X p).symm

end Stacks.Sites.OverModules

end
