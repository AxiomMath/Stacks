module

public import Mathlib.CategoryTheory.HomCongr
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localization of graded morphisms on a nonvanishing open

Let `L` be an invertible sheaf of modules on a scheme `X`, let `F` and `G` be sheaves of
modules, and let `s` be a global section of `L`. The graded module
`⨁_{n} Hom(F, G ⊗ L^{⊗ n})` carries an action of the section ring `⨁_{n} Γ(X, L^{⊗ n})`, and
`s` is a homogeneous element of degree one. This file constructs the degree-zero localization
of that graded module at `s` and the canonical map from it to morphisms `F|_{X_s} ⟶ G|_{X_s}`
on the open where `s` does not vanish, and identifies the map on homogeneous fractions.

## Main definitions

* `Stacks.SheafOfModules.homToTwistedSection` identifies a morphism `F ⟶ G ⊗ L^{⊗ n}` with a
  global section of `ℋom(F, G) ⊗ L^{⊗ n}`.
* `Stacks.SheafOfModules.gradedHom` is the graded group `⨁_{n} Hom(F, G ⊗ L^{⊗ n})`, with the
  action of the section ring and the grading transported along `homToTwistedSection`.
* `Stacks.SheafOfModules.homAtNonvanishingOpen` is its degree-zero localization at `s`.
* `Stacks.SheafOfModules.homFraction` regards a morphism `F ⟶ G ⊗ L^{⊗ n}` as the fraction
  with numerator that morphism and denominator `sⁿ`.
* `Stacks.SheafOfModules.homLocalizationMap` restricts such a fraction to `X_s` and divides by
  `sⁿ`.

## Main results

* `Stacks.SheafOfModules.tensorHomEvaluation_tmul_apply` and
  `Stacks.SheafOfModules.homToTwistedSection_evaluation` pin the degreewise comparison between
  twisted morphisms and twisted sections of the internal hom by evaluation on local sections.
* `Stacks.SheafOfModules.homFraction_surjective`: every degree-zero fraction has a
  homogeneous numerator coming from a global morphism `F ⟶ G ⊗ L^{⊗ n}`.
* `Stacks.SheafOfModules.homLocalizationMap_fraction`: the value on `f / sⁿ` is the unique
  morphism on `X_s` whose tensor product with `sⁿ` is the restriction of `f`.
* `Stacks.SheafOfModules.homFractionClass_eq_zero_iff`: the class of `f / sⁿ` is zero exactly
  when some power of `s` annihilates `f`. `Stacks.SheafOfModules.exists_hom_smul_pow` names that
  multiple as a morphism `F ⟶ G ⊗ L^{⊗ (e + n)}`, and
  `Stacks.SheafOfModules.of_eq_zero_iff` says when a homogeneous morphism vanishes.

## Implementation notes

Since `L` is invertible, tensoring with `L^{⊗ n}` is an equivalence, so the internal-hom
adjunction turns `Hom(F, G ⊗ L^{⊗ n})` into `Γ(X, ℋom(F, G) ⊗ L^{⊗ n})`. The comparison
morphism `tensorHomEvaluation` is the tensor--hom evaluation map, which is specified on pure
tensors and shown to be an isomorphism by `isIso_of_curry_tensor_equivalence`; the graded
structure on `gradedHom` is then the one transported from the section module of `ℋom(F, G)`,
so that the whole fraction calculus of Tag 0B5L applies verbatim.

The tensor product of two sheaves of modules has two spellings here: the hand-built one of
Tag 01CB, which the internal-hom adjunction `Stacks.SheafOfModules.tensorHomEquiv` uses, and
the monoidal product of Tag 05NA, which the section-level calculus of Tag 01CU uses. They are
definitionally equal, and `Stacks.SheafOfModules.TensorSheafification.structureSheaf`
together with the restriction-of-scalars
functors are made transparent at the `implicit` level so that the two can be identified
wherever both occur.

`Stacks.SheafOfModules.homFraction_surjective` and its helper
`homFraction_surjective_aux` are written in term mode, and must stay that way. Written as
tactic proofs built from `obtain`, `refine ... ?_` and `exact`, both cost just over
200000 heartbeats (208345 and 211077). Every individual step is cheap (7000-15000);
what is expensive is `rcases`/`refine` having to build a motive, or the type of a `?_` hole,
over `homAtNonvanishingOpen`, whose carrier is a localization of `gradedHom` at a
`Module.compHom` instance. Passing the same terms positionally, through `Exists.elim` and an
anonymous constructor, so that every type is known before it is checked, brings the two to 5474
and 8366. The cost comes from the sheaf of rings of a ringed space being a definition that is
`instance_reducible` rather than `reducible`, which makes the conversions in those motives
expensive; the budget cannot be raised here, since this project
forbids option overrides.

## References

* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget PresheafOfModules.restrictScalars
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf

section GradedHomLocalization

/- The sheafification of a presheaf of modules on the site of opens is computed by the
small-site machinery of Tag 01CB; the limits instance that `IsLocalSite` provides competes
with it and is not used here, so it is erased for this section. -/
attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

variable (X : Scheme.{u})
  (L F G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The graded commutative ring structure on the section ring `⨁_{n ≥ 0} Γ(X, L^{⊗ n})`. -/
local instance : DirectSum.GCommRing
    (fun n : ℕ => (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ)).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :=
  sectionRingGradedRing (sectionSiteRing X)
    (sectionSiteSheaf X) L

/-- The section ring acts on the graded section module of the internal hom `ℋom(F, G)`. -/
local instance : Module
    (sectionRing (sectionSiteRing X)
      (sectionSiteSheaf X) L)
    (sectionModule (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G)) :=
  sectionModuleModule (sectionSiteRing X)
    (sectionSiteSheaf X) L _

/-- The sections of the internal hom `ℋom(F, G)` over an open `U` are a module over the ring of
sections over `U`. -/
local instance internalHomSectionModule (U : Opens X.toRingedSpace) : Module
    ((sectionSiteRing X).obj (op U))
    ((sheafHomSpace X.toRingedSpace F G).val.obj (op U)) :=
  homModule X.toRingedSpace.presheaf F.val G.val U

/-- The sections of `F` over an open `U` are a module over the ring of sections over `U`. -/
local instance moduleSectionModule (U : Opens X.toRingedSpace) : Module
    ((sectionSiteRing X).obj (op U)) (F.val.obj (op U)) :=
  (F.val.obj (op U)).isModule

/-- Tensor--Hom evaluation: a local tensor `α ⊗ q` sends a local section `g`
to `α(g) ⊗ q`. -/
private noncomputable def sheafHomEvaluation :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj (F)) ⟶ G :=
  (tensorHomEquiv X.toRingedSpace
    (sheafHomSpace X.toRingedSpace F G) F G).symm
      (𝟙 (sheafHomSpace X.toRingedSpace F G))

private theorem sheafHomEvaluation_tmul_apply
    (U : Opens X.toRingedSpace)
    (a : (sheafHomSpace X.toRingedSpace F G).val.obj (op U))
    (g : F.val.obj (op U)) :
    ((sheafHomEvaluation X F G).val.app (op U)).hom
      (TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
        (sheafHomSpace X.toRingedSpace F G) F
        (op U) (a ⊗ₜ[(sectionSiteRing X).obj (op U)] g)) =
    (a.app (op (Over.mk (𝟙 U)))).hom g := by
  let _ : Module ((sectionSiteRing X).obj (op U)) (F.val.obj (op U)) :=
    (F.val.obj (op U)).isModule
  have h := (tensorHomEquiv_isTensorCurry X.toRingedSpace
      (sheafHomEvaluation X F G)) U a g
  have he : tensorHomEquiv X.toRingedSpace
      (sheafHomSpace X.toRingedSpace F G) F G
      (sheafHomEvaluation X F G) =
      𝟙 (sheafHomSpace X.toRingedSpace F G) :=
    (tensorHomEquiv X.toRingedSpace (sheafHomSpace X.toRingedSpace F G) F G).apply_symm_apply _
  rw [he] at h
  change (a.app (op (Over.mk (𝟙 U)))).hom g =
    ((sheafHomEvaluation X F G).val.app (op U)).hom
      (TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
        (sheafHomSpace X.toRingedSpace F G) F
        (op U) (a ⊗ₜ[(sectionSiteRing X).obj (op U)] g)) at h
  exact h.symm


open MonoidalCategory
private abbrev tp
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (M)).obj (N))

/-- The tensor product of two morphisms of sheaves of modules, spelled through the
Tag 01CU tensor bifunctor so that source and target are the same tensor product as `tp`. -/
private abbrev tmap {M M' N N' : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} (f : M ⟶ M') (g : N ⟶ N') :
    tp X M N ⟶ tp X M' N' :=
  (PresheafOfModules.sheafification (R := Tensor.ringSheaf X.sheaf)
    (𝟙 (Tensor.ringSheaf X.sheaf).obj)).map
      (PresheafOfModules.tensorHom (O := X.presheaf) f.val g.val)

private abbrev pure
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (U : Opens X.toRingedSpace)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) : (tp X M N).val.obj (op U) :=
  tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) M N m n

private lemma assoc_pure (M N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (U : Opens X.toRingedSpace)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) (p : P.val.obj (op U)) :
    (Invertible.tensorProductAssociator (sectionSiteRing X)
      (sectionSiteSheaf X) M N P).hom.val.app (op U)
        (pure X (tp X M N) P U (pure X M N U m n) p) =
      pure X M (tp X N P) U m (pure X N P U n p) :=
  tensorSections_associatorAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) M N P m n p

private lemma assoc_inv_pure (M N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (U : Opens X.toRingedSpace)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) (p : P.val.obj (op U)) :
    (Invertible.tensorProductAssociator (sectionSiteRing X)
      (sectionSiteSheaf X) M N P).inv.val.app (op U)
        (pure X M (tp X N P) U m (pure X N P U n p)) =
      pure X (tp X M N) P U (pure X M N U m n) p := by
  rw [← assoc_pure X M N P U m n p]
  exact congrArg (fun f => (f.val.app (op U)).hom
    (pure X (tp X M N) P U (pure X M N U m n) p))
      (Invertible.tensorProductAssociator (sectionSiteRing X)
        (sectionSiteSheaf X) M N P).hom_inv_id

private lemma braid_pure (M N : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (U : Opens X.toRingedSpace)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (Invertible.tensorProductBraiding (sectionSiteRing X)
      (sectionSiteSheaf X) M N).hom.val.app (op U)
        (pure X M N U m n) = pure X N M U n m :=
  tensorSections_braidingAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) M N m n

private lemma map_pure {M M' N N' : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} (f : M ⟶ M') (g : N ⟶ N')
    (U : Opens X.toRingedSpace) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (tmap X f g).val.app (op U)
      (pure X M N U m n) = pure X M' N' U (f.val.app (op U) m) (g.val.app (op U) n) :=
  tensorSections_tensorMapAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) M M' N N' f g m n

private lemma restrict_pure (M N : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) {U V : Opens X.toRingedSpace}
    (i : V ⟶ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (tp X M N).val.map i.op (pure X M N U m n) =
      pure X M N V (M.val.map i.op m) (N.val.map i.op n) :=
  (congrArg (fun f => f.hom (m ⊗ₜ[X.presheaf.obj (op U)] n))
    ((TensorSheafification.toSheafify (sectionSiteRing X)
      (sectionSiteSheaf X)
      ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) (M.val)
          (N.val)))).naturality i.op)).symm

private lemma internalHom_restrict_apply (M N : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace))
    {U : Opens X.toRingedSpace}
    (a : (sheafHomSpace X.toRingedSpace M N).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : M.val.obj (op V.unop.left)) :
    (((sheafHomSpace X.toRingedSpace M N).val.map
      V.unop.hom.op a).app (op (Over.mk (𝟙 V.unop.left)))).hom g =
      (a.app V).hom g := by
  change (a.app (op (Over.mk (𝟙 V.unop.left ≫ V.unop.hom)))).hom g = _
  rfl

private lemma curry_apply (A B C : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (t : tp X A B ⟶ C)
    (U : Opens X.toRingedSpace) (x : A.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : B.val.obj (op V.unop.left)) :
    (((tensorHomEquiv X.toRingedSpace A B C t).val.app (op U) x).app V).hom g =
      t.val.app (op V.unop.left)
        (pure X A B V.unop.left (A.val.map V.unop.hom.op x) g) := by
  let c := tensorHomEquiv X.toRingedSpace A B C t
  rw [← internalHom_restrict_apply X B C (c.val.app (op U) x) V g]
  have h := congrArg (fun f => f.hom x) (c.val.naturality V.unop.hom.op)
  change c.val.app (op V.unop.left) (A.val.map V.unop.hom.op x) =
    (sheafHomSpace X.toRingedSpace B C).val.map
      V.unop.hom.op (c.val.app (op U) x) at h
  rw [← h]
  exact tensorHomEquiv_isTensorCurry X.toRingedSpace t _ _ _

private lemma curry_naturality_left {A A' B C : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} (f : A' ⟶ A)
    (t : tp X A B ⟶ C) :
    f ≫ tensorHomEquiv X.toRingedSpace A B C t =
    tensorHomEquiv X.toRingedSpace A' B C
      (tmap X f (𝟙 B) ≫ t) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have hA : f.val.app (op V.unop.left) (A'.val.map V.unop.hom.op x) =
      A.val.map V.unop.hom.op (f.val.app U x) :=
    congrArg (fun k => k.hom x) (f.val.naturality V.unop.hom.op)
  change (((tensorHomEquiv X.toRingedSpace A B C t).val.app U
    (f.val.app U x)).app V).hom g =
      (((tensorHomEquiv X.toRingedSpace A' B C
        (tmap X f (𝟙 B) ≫ t)).val.app U x).app V).hom g
  refine (curry_apply X A B C t (unop U) (f.val.app U x) V g).trans ?_
  refine Eq.trans ?_ (curry_apply X A' B C
    (tmap X f (𝟙 B) ≫ t) (unop U) x V g).symm
  change t.val.app (op V.unop.left)
      (pure X A B V.unop.left (A.val.map V.unop.hom.op (f.val.app U x)) g) =
    t.val.app (op V.unop.left)
      ((tmap X f (𝟙 B)).val.app (op V.unop.left)
        (pure X A' B V.unop.left (A'.val.map V.unop.hom.op x) g))
  exact congrArg (fun y => (t.val.app (op V.unop.left)).hom y)
    ((congrArg (fun y => pure X A B V.unop.left y g) hA.symm).trans
      (map_pure X f (𝟙 B) V.unop.left (A'.val.map V.unop.hom.op x) g).symm)

private def tensorInterchange (M N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) :
    tp X (tp X M N) P ≅ tp X (tp X M P) N :=
  Invertible.tensorProductAssociator (sectionSiteRing X)
    (sectionSiteSheaf X) M N P ≪≫
  Invertible.tensorProductIso (sectionSiteRing X)
    (sectionSiteSheaf X) (Iso.refl M)
    (Invertible.tensorProductBraiding (sectionSiteRing X)
      (sectionSiteSheaf X) N P) ≪≫
  (Invertible.tensorProductAssociator (sectionSiteRing X)
    (sectionSiteSheaf X) M P N).symm


private lemma interchange_pure (M N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (U : Opens X.toRingedSpace)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) (p : P.val.obj (op U)) :
    (tensorInterchange X M N P).hom.val.app (op U)
      (pure X (tp X M N) P U (pure X M N U m n) p) =
    pure X (tp X M P) N U (pure X M P U m p) n := by
  change (Invertible.tensorProductAssociator (sectionSiteRing X)
      (sectionSiteSheaf X) M P N).inv.val.app _
    ((tmap X (𝟙 M)
      (Invertible.tensorProductBraiding (sectionSiteRing X)
        (sectionSiteSheaf X) N P).hom).val.app _
      ((Invertible.tensorProductAssociator (sectionSiteRing X)
      (sectionSiteSheaf X) M N P).hom.val.app _ _)) = _
  have h₁ := assoc_pure X M N P U m n p
  have h₂ := map_pure X (𝟙 M)
    (Invertible.tensorProductBraiding (sectionSiteRing X)
      (sectionSiteSheaf X) N P).hom U m (pure X N P U n p)
  have h₃ := braid_pure X N P U n p
  refine Eq.trans (congrArg (fun y => (Invertible.tensorProductAssociator (sectionSiteRing X)
    (sectionSiteSheaf X) M P N).inv.val.app (op U) y) ?_) (assoc_inv_pure X M P N U m p n)
  exact (congrArg (fun y => (tmap X (𝟙 M)
      (Invertible.tensorProductBraiding (sectionSiteRing X)
        (sectionSiteSheaf X) N P).hom).val.app (op U) y) h₁).trans
    (h₂.trans (congrArg (fun y => pure X M (tp X P N) U m y) h₃))


private lemma tensor_hom_ext {M N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} {f g : tp X M N ⟶ P}
    (h : ∀ (U : Opens X.toRingedSpace) (m : M.val.obj (op U)) (n : N.val.obj (op U)),
      f.val.app (op U) (pure X M N U m n) = g.val.app (op U) (pure X M N U m n)) : f = g := by
  apply ((TensorSheafification.sheafifyAdjunction (sectionSiteRing X)
    (sectionSiteSheaf X)).homEquiv _ P).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

private lemma tensor_triple_hom_ext {M N P Q : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)}
    {f g : tp X (tp X M N) P ⟶ Q}
    (h : ∀ (U : Opens X.toRingedSpace) (m : M.val.obj (op U))
      (n : N.val.obj (op U)) (p : P.val.obj (op U)),
      f.val.app (op U) (pure X (tp X M N) P U (pure X M N U m n) p) =
      g.val.app (op U) (pure X (tp X M N) P U (pure X M N U m n) p)) : f = g := by
  apply (tensorHomEquiv X.toRingedSpace (tp X M N) P Q).injective
  apply tensor_hom_ext X
  intro U m n
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  have hr := restrict_pure X M N V.unop.hom m n
  refine Eq.trans (curry_apply X (tp X M N) P Q f U (pure X M N U m n) V p) ?_
  refine Eq.trans ?_ (curry_apply X (tp X M N) P Q g U (pure X M N U m n) V p).symm
  exact (congrArg (fun y => f.val.app (op V.unop.left)
      (pure X (tp X M N) P V.unop.left y p)) hr).trans
    ((h V.unop.left (M.val.map V.unop.hom.op m) (N.val.map V.unop.hom.op n) p).trans
      (congrArg (fun y => g.val.app (op V.unop.left)
        (pure X (tp X M N) P V.unop.left y p)) hr.symm))

private lemma interchange_naturality {M M' N P : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} (f : M ⟶ M') :
    tmap X
      (tmap X f (𝟙 N)) (𝟙 P) ≫
        (tensorInterchange X M' N P).hom =
    (tensorInterchange X M N P).hom ≫
      tmap X
        (tmap X f (𝟙 P)) (𝟙 N) := by
  apply tensor_triple_hom_ext X (M := M) (N := N) (P := P)
  intro U m n p
  change (tensorInterchange X M' N P).hom.val.app (op U)
      ((tmap X
        (tmap X f (𝟙 N)) (𝟙 P)).val.app (op U) _) =
    (tmap X
        (tmap X f (𝟙 P)) (𝟙 N)).val.app (op U)
      ((tensorInterchange X M N P).hom.val.app (op U) _)
  have ha := map_pure X (tmap X f (𝟙 N)) (𝟙 P) U
    (pure X M N U m n) p
  have hb := map_pure X f (𝟙 N) U m n
  have hc := interchange_pure X M' N P U (f.val.app (op U) m) n p
  have hd := interchange_pure X M N P U m n p
  have he := map_pure X (tmap X f (𝟙 P)) (𝟙 N) U
    (pure X M P U m p) n
  have hf := map_pure X f (𝟙 P) U m p
  have hL := (congrArg (fun y => (tensorInterchange X M' N P).hom.val.app (op U) y) ha).trans
    ((congrArg (fun y => (tensorInterchange X M' N P).hom.val.app (op U)
      (pure X (tp X M' N) P U y p)) hb).trans hc)
  have hR := (congrArg (fun y => (tmap X
      (tmap X f (𝟙 P)) (𝟙 N)).val.app (op U) y) hd).trans
    (he.trans (congrArg (fun y => pure X (tp X M' P) N U y n) hf))
  exact hL.trans hR.symm


private lemma isIso_of_curry_tensor_equivalence
    {C : Type*} [Category C] (e : C ≌ C) (A : C ⥤ C) (G H H' : C)
    (h : ∀ Y, (A.obj Y ⟶ G) ≃ (Y ⟶ H))
    (h' : ∀ Y, (A.obj Y ⟶ e.functor.obj G) ≃ (Y ⟶ H'))
    (c : ∀ Y, A.obj (e.functor.obj Y) ≅ e.functor.obj (A.obj Y))
    (f : e.functor.obj H ⟶ H')
    (hf : ∀ Y (k : Y ⟶ H), e.functor.map k ≫ f =
      h' (e.functor.obj Y) ((c Y).hom ≫ e.functor.map ((h Y).symm k))) : IsIso f := by
  have hb (Y : C) : Function.Bijective (fun k : Y ⟶ H => e.functor.map k ≫ f) := by
    simp_rw [hf]
    have ht := (h' (e.functor.obj Y)).bijective.comp
      (((c Y).symm.homCongr (Iso.refl _)).bijective.comp
        (((Functor.FullyFaithful.ofFullyFaithful e.functor).map_bijective _ _).comp
          (h Y).symm.bijective))
    simpa only [Function.comp_def, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom,
      Category.comp_id] using ht
  apply isIso_of_yoneda_map_bijective
  intro Y
  have ht : Function.Bijective (fun k : e.functor.obj (e.inverse.obj Y) ⟶ e.functor.obj H =>
      k ≫ f) :=
    (Function.Bijective.of_comp_iff _
      ((Functor.FullyFaithful.ofFullyFaithful e.functor).map_bijective _ _)).mp
        (hb (e.inverse.obj Y))
  let i := e.counitIso.app Y
  constructor
  · intro a b hab
    apply (cancel_epi i.hom).mp
    apply ht.injective
    simpa only [Category.assoc] using congrArg (fun k => i.hom ≫ k) hab
  · intro k
    obtain ⟨g, hg⟩ := ht.surjective (i.hom ≫ k)
    exact ⟨i.inv ≫ g, by simp only [Category.assoc, hg, Iso.inv_hom_id_assoc]⟩

private lemma uncurry_eq {A F G : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)}
    (k : A ⟶ sheafHomSpace X.toRingedSpace F G) :
    tmap X k (𝟙 F) ≫ sheafHomEvaluation X F G =
      (tensorHomEquiv X.toRingedSpace A F G).symm k := by
  apply (tensorHomEquiv X.toRingedSpace A F G).injective
  refine Eq.trans (curry_naturality_left X k (sheafHomEvaluation X F G)).symm ?_
  have he : tensorHomEquiv X.toRingedSpace (sheafHomSpace X.toRingedSpace F G) F G
      (sheafHomEvaluation X F G) = 𝟙 (sheafHomSpace X.toRingedSpace F G) :=
    (tensorHomEquiv X.toRingedSpace (sheafHomSpace X.toRingedSpace F G) F G).apply_symm_apply _
  refine Eq.trans (congrArg (fun z => k ≫ z) he) ?_
  exact (Category.comp_id k).trans
    ((tensorHomEquiv X.toRingedSpace A F G).apply_symm_apply k).symm

private lemma tensor_map_comp {A B C : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)} (f : A ⟶ B) (g : B ⟶ C)
    (P : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    tmap X (f ≫ g) (𝟙 P) =
      tmap X f (𝟙 P) ≫
        tmap X g (𝟙 P) :=
  ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj P).map_comp f g

/-- The tensor--Hom evaluation map `ℋom(F, G) ⊗ L^{⊗ n} ⟶ ℋom(F, G ⊗ L^{⊗ n})`: the map adjoint to
evaluating a local homomorphism `F ⟶ G` on a local section of `F`. -/
public noncomputable def tensorHomEvaluation (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n))) ⟶
    sheafHomSpace X.toRingedSpace F
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L n)))) := by
  exact tensorHomEquiv X.toRingedSpace _ F _
    ((tensorInterchange X _ _ F).hom ≫
      tmap X (sheafHomEvaluation X F G) (𝟙 _))

private lemma tensorHomEvaluation_isIso (n : ℤ) : IsIso (tensorHomEvaluation X L F G n)  := by
  let P := TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L n
  let : ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj P).IsEquivalence :=
    TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) P
  let e := ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj P).asEquivalence
  refine isIso_of_curry_tensor_equivalence e
    ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F) G
    (sheafHomSpace X.toRingedSpace F G)
    (sheafHomSpace X.toRingedSpace F (tp X G P))
    (fun Y => tensorHomEquiv X.toRingedSpace Y F G)
    (fun Y => tensorHomEquiv X.toRingedSpace Y F (tp X G P))
    (fun Y => tensorInterchange X Y P F) (tensorHomEvaluation X L F G n) ?_
  intro Y k
  change tmap X k (𝟙 P) ≫
    tensorHomEquiv X.toRingedSpace _ F _
      ((tensorInterchange X _ P F).hom ≫
        tmap X (sheafHomEvaluation X F G) (𝟙 P)) =
    tensorHomEquiv X.toRingedSpace (tp X Y P) F (tp X G P)
      ((tensorInterchange X Y P F).hom ≫ tmap X
        ((tensorHomEquiv X.toRingedSpace Y F G).symm k) (𝟙 P))
  refine (curry_naturality_left X (tmap X k (𝟙 P))
    ((tensorInterchange X _ P F).hom ≫
      tmap X (sheafHomEvaluation X F G) (𝟙 P))).trans ?_
  congr 1
  have h2 := interchange_naturality X (M := Y) (M' := sheafHomSpace X.toRingedSpace F G)
    (N := P) (P := F) k
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ tmap X (sheafHomEvaluation X F G) (𝟙 P)) h2) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => (tensorInterchange X Y P F).hom ≫ z) ?_
  exact (tensor_map_comp X (tmap X k (𝟙 F)) (sheafHomEvaluation X F G) P).symm.trans
    (congrArg (fun z => tmap X z (𝟙 P)) (uncurry_eq X k))


private def globalHomEquiv (X : Scheme.{u}) (F G : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) :
    (F ⟶ G) ≃
      (sheafHomSpace X.toRingedSpace F G).val.obj
        (op (⊤_ (Opens X.toRingedSpace))) where
  toFun f := (restrFun X.toRingedSpace.presheaf _).map f.val
  invFun a := ⟨{
    app U := a.app (op (Over.mk (terminal.from U.unop)))
    naturality {U V} i := a.naturality ((Over.homMk i.unop :
      Over.mk (terminal.from V.unop) ⟶ Over.mk (terminal.from U.unop)).op) }⟩
  left_inv f := rfl
  right_inv a := by
    apply PresheafOfModules.hom_ext
    intro U
    change a.app (op (Over.mk (terminal.from U.unop.left))) = a.app U
    rw [show terminal.from U.unop.left = U.unop.hom from Subsingleton.elim _ _]
    rfl

/-- Componentwise evaluation fixes the tensor--Hom morphism on pure tensors. -/
public theorem tensorHomEvaluation_tmul_apply (n : ℤ)
    (U : Opens X.toRingedSpace)
    (a : (sheafHomSpace X.toRingedSpace F G).val.obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L n).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : ((restrFun X.toRingedSpace.presheaf U).obj F.val).obj V) :
    (((((tensorHomEvaluation X L F G n).val.app (op U)).hom
      (((TensorSheafification.toSheafify (sectionSiteRing X)
        (sectionSiteSheaf X)
        ((PresheafOfModules.tensorObj (O := (sectionSiteRing X))
            ((sheafHomSpace X.toRingedSpace F G).val) ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L n).val)))).app (op U)).hom
        (a ⊗ₜ[(sectionSiteRing X).obj (op U)] q))).app V).hom g =
      (((TensorSheafification.toSheafify (sectionSiteRing X)
        (sectionSiteSheaf X)
        ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) (G.val)
            ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L n).val)))).app
              (op V.unop.left)).hom
        (((a.app V).hom g) ⊗ₜ[(sectionSiteRing X).obj (op V.unop.left)]
          ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L n).val.map
              V.unop.hom.op).hom q))) :=
  by
    let P := TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L n
    let H := sheafHomSpace X.toRingedSpace F G
    change (((tensorHomEquiv X.toRingedSpace (tp X H P) F (tp X G P)
      ((tensorInterchange X H P F).hom ≫
        tmap X (sheafHomEvaluation X F G) (𝟙 P))).val.app
      (op U) (pure X H P U a q)).app V).hom g =
        pure X G P V.unop.left ((a.app V).hom g) (P.val.map V.unop.hom.op q)
    have hr := restrict_pure X H P V.unop.hom a q
    have hi := interchange_pure X H P F V.unop.left
      (H.val.map V.unop.hom.op a) (P.val.map V.unop.hom.op q) g
    have hm := map_pure X (sheafHomEvaluation X F G) (𝟙 P) V.unop.left
      (pure X H F V.unop.left (H.val.map V.unop.hom.op a) g)
      (P.val.map V.unop.hom.op q)
    have hs := sheafHomEvaluation_tmul_apply X F G V.unop.left
      (H.val.map V.unop.hom.op a) g
    have hb := internalHom_restrict_apply X F G a V g
    refine Eq.trans (curry_apply X (tp X H P) F (tp X G P)
      ((tensorInterchange X H P F).hom ≫ tmap X (sheafHomEvaluation X F G) (𝟙 P))
      U (pure X H P U a q) V g) ?_
    refine Eq.trans (congrArg (fun y =>
      ((tensorInterchange X H P F).hom ≫ tmap X (sheafHomEvaluation X F G) (𝟙 P)).val.app
        (op V.unop.left) (pure X (tp X H P) F V.unop.left y g)) hr) ?_
    change (tmap X (sheafHomEvaluation X F G) (𝟙 P)).val.app (op V.unop.left)
        ((tensorInterchange X H P F).hom.val.app (op V.unop.left)
          (pure X (tp X H P) F V.unop.left
            (pure X H P V.unop.left (H.val.map V.unop.hom.op a)
              (P.val.map V.unop.hom.op q)) g)) = _
    refine Eq.trans (congrArg (fun y =>
      (tmap X (sheafHomEvaluation X F G) (𝟙 P)).val.app (op V.unop.left) y) hi) ?_
    exact hm.trans (congrArg (fun y => pure X G P V.unop.left y
      (P.val.map V.unop.hom.op q)) (hs.trans hb))

private def tensorHomSectionEquiv (n : ℤ) (U : Opens X.toRingedSpace) := by
  letI := tensorHomEvaluation_isIso X L F G n
  letI : IsIso ((tensorHomEvaluation X L F G n).val.app (op U)) :=
    (_root_.SheafOfModules.evaluation _ (op U)).map_isIso (tensorHomEvaluation X L F G n)
  exact Equiv.ofBijective ((tensorHomEvaluation X L F G n).val.app (op U)).hom
    (ConcreteCategory.bijective_of_isIso _)

/-- The canonical degreewise identification of twisted morphisms with sections
of the corresponding twist of the internal Hom sheaf. -/
public noncomputable def homToTwistedSection (n : ℤ) :
    (F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n)))) ≃
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  (globalHomEquiv X F _).trans
    (tensorHomSectionEquiv X L F G n (⊤_ (Opens X.toRingedSpace))).symm

/-- The comparison evaluates to the original morphism on every object of the
slice site over the terminal open. This fixes the comparison, including when
`L` is trivial and `s = 1`. -/
public theorem homToTwistedSection_evaluation (n : ℤ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n))))
    (V : (Over (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))ᵒᵖ)
    (g : ((restrFun X.toRingedSpace.presheaf
      (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))).obj F.val).obj V) :
    (((((tensorHomEvaluation X L F G n).val.app
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))).hom
      (homToTwistedSection X L F G n f)).app V).hom g =
        ((f.val.app (op V.unop.left)).hom g)) :=
  by
    have h := (tensorHomSectionEquiv X L F G n (⊤_ (Opens X.toRingedSpace))).apply_symm_apply
      (globalHomEquiv X F _ f)
    exact congrArg (fun a => (a.app V).hom g) h

/-- The additive structure on a sheaf morphism group, transported through
the internal-Hom presentation. -/
public noncomputable instance (n : ℤ) : AddCommGroup
    (F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n)))) :=
  (homToTwistedSection X L F G n).addCommGroup

/-- The graded group `⊕ₙ Hom(F, G ⊗ Lⁿ)` appearing in Tag 0B5M. -/
public abbrev gradedHom :=
  ⨁ n : ℤ, (F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
      (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
      ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L n))))

/-- The direct sum of the degreewise internal-Hom identifications. -/
public noncomputable def gradedHomComparison :
    gradedHom X L F G ≃+
      sectionModule (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (sheafHomSpace X.toRingedSpace F G) :=
  DirectSum.congrAddEquiv (fun n =>
    Equiv.addEquiv (homToTwistedSection X L F G n))

/-- The graded comparison sends a homogeneous morphism to its associated
twisted internal-Hom section in the same degree. -/
public theorem gradedHomComparison_of (n : ℤ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n)))) :
    gradedHomComparison X L F G (DirectSum.of _ n f) =
      DirectSum.of _ n (homToTwistedSection X L F G n f) :=
  by
    change DirectSum.map (fun i =>
      (Equiv.addEquiv (homToTwistedSection X L F G i)).toAddMonoidHom)
      (DirectSum.of _ n f) = _
    rw [DirectSum.map_of]
    rfl

@[instance_reducible] private noncomputable def decomposition_comap_addEquiv
    {M N ι : Type*} [AddCommGroup M] [AddCommGroup N] [DecidableEq ι]
    (e : M ≃+ N) (B : ι → AddSubgroup N) [DirectSum.Decomposition B] :
    DirectSum.Decomposition (fun i => (B i).comap e.toAddMonoidHom) := by
  classical
  let e' (i : ι) : (B i).comap e.toAddMonoidHom ≃+ B i := {
    toFun x := ⟨e x, x.2⟩
    invFun y := ⟨e.symm y, by simp⟩
    left_inv x := by apply Subtype.ext; simp
    right_inv y := by apply Subtype.ext; simp
    map_add' x y := by apply Subtype.ext; exact e.map_add _ _ }
  let A : ι → AddSubgroup M := fun i => (B i).comap e.toAddMonoidHom
  let E : (⨁ i, B i) ≃+ ⨁ i, A i :=
    DirectSum.congrAddEquiv (fun i => (e' i).symm)
  have hcoeHom :
      (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom =
        e.symm.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom B) := by
    apply AddMonoidHom.ext
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i x =>
        change DirectSum.coeAddMonoidHom A
            (DirectSum.map (fun j => (e' j).symm.toAddMonoidHom)
              (DirectSum.of _ i x)) =
          e.symm (DirectSum.coeAddMonoidHom B (DirectSum.of _ i x))
        rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of,
          DirectSum.coeAddMonoidHom_of]
        rfl
    | add y z hy hz =>
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hy, hz]
  have hcoe (y : ⨁ i, B i) :
      DirectSum.coeAddMonoidHom A (E y) =
        e.symm (DirectSum.coeAddMonoidHom B y) :=
    congrArg (fun f => f y) hcoeHom
  let d : M →+ ⨁ i, A i :=
    E.toAddMonoidHom.comp
      ((DirectSum.decomposeAddEquiv B).toAddMonoidHom.comp e.toAddMonoidHom)
  refine DirectSum.Decomposition.ofAddHom
    (ℳ := A) d ?_ ?_
  · ext x
    change DirectSum.coeAddMonoidHom A
        (E ((DirectSum.decompose B) (e x))) = x
    rw [hcoe]
    have hleft : DirectSum.coeAddMonoidHom B ((DirectSum.decompose B) (e x)) = e x :=
      (DirectSum.decompose B).left_inv _
    rw [hleft]
    exact e.left_inv x
  · apply AddMonoidHom.ext
    intro y
    change E ((DirectSum.decompose B)
      (e (DirectSum.coeAddMonoidHom A y))) = y
    have heq : e (DirectSum.coeAddMonoidHom A y) =
        DirectSum.coeAddMonoidHom B (E.symm y) := by
      have h := hcoe (E.symm y)
      simpa using congrArg e h
    rw [heq]
    have hright : (DirectSum.decompose B)
        (DirectSum.coeAddMonoidHom B (E.symm y)) = E.symm y :=
      (DirectSum.decompose B).right_inv _
    rw [hright]
    exact E.apply_symm_apply y

/-- The section ring acts on twisted morphisms through the canonical
degreewise tensor--Hom identification. -/
public noncomputable instance gradedHomModule : Module
    (sectionRing (sectionSiteRing X)
      (sectionSiteSheaf X) L) (gradedHom X L F G) :=
  (gradedHomComparison X L F G).module _

/-- The subgroup of homogeneous morphisms of degree `n`. -/
public noncomputable def gradedHomGrading (n : ℤ) :
    AddSubgroup (gradedHom X L F G) :=
  (sectionModuleGrading (sectionSiteRing X)
    (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G) n).comap
      (gradedHomComparison X L F G).toAddMonoidHom

/-- The homogeneous components `gradedHomGrading` decompose `gradedHom`: the decomposition is
transported from that of the section module of `ℋom(F, G)`. -/
public theorem gradedHomDecomposition_exists :
    Nonempty (DirectSum.Decomposition (gradedHomGrading X L F G)) := by
  let T := sectionModuleGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G)
  let _ : DirectSum.Decomposition T := sectionModuleDecomposition
    (sectionSiteRing X) (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G)
  exact ⟨decomposition_comap_addEquiv (gradedHomComparison X L F G) T⟩

/-- The decomposition of `gradedHom` into its homogeneous components `gradedHomGrading`. -/
public noncomputable instance gradedHomDecomposition :
    DirectSum.Decomposition (gradedHomGrading X L F G) :=
  Classical.choice (gradedHomDecomposition_exists X L F G)

/-- The action of the section ring on `gradedHom` respects the gradings: a homogeneous section of
degree `i` sends a homogeneous morphism of degree `j` to one of degree `i + j`. -/
public theorem gradedHomGradedSMul_exists :
    SetLike.GradedSMul
      (sectionRingGrading (sectionSiteRing X)
        (sectionSiteSheaf X) L)
      (gradedHomGrading X L F G) := by
  let T := sectionModuleGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G)
  let _ : SetLike.GradedSMul
      (sectionRingGrading (sectionSiteRing X)
        (sectionSiteSheaf X) L) T :=
    sectionModuleGradedSMul (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G)
  constructor
  intro i j a b ha hb
  change (gradedHomComparison X L F G)
    ((gradedHomComparison X L F G).symm (a • (gradedHomComparison X L F G) b)) ∈
      T (i +ᵥ j)
  rw [AddEquiv.apply_symm_apply]
  exact SetLike.GradedSMul.smul_mem ha hb

/-- The graded action of the section ring on `gradedHom`, from `gradedHomGradedSMul_exists`. -/
public noncomputable instance gradedHomGradedSMul :
    SetLike.GradedSMul
      (sectionRingGrading (sectionSiteRing X)
        (sectionSiteSheaf X) L)
      (gradedHomGrading X L F G) :=
  gradedHomGradedSMul_exists X L F G

/-- The grading of the section ring by degree makes it a graded ring. -/
local instance : GradedRing
    (sectionRingGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L) :=
  sectionRingGradingGradedRing (sectionSiteRing X)
    (sectionSiteSheaf X) L

section LocalizedAction

/-- The degree-zero homogeneous localization of the section ring acts on the localization of
the graded Hom module through its embedding into the full localization. Mathlib keeps this
`Module.compHom` action out of instance search, and the submodule
`homAtNonvanishingOpen` is stated over it, so it has to be in scope for the additive
structure of that submodule to be found at all. -/
local instance gradedHomAwayModule (s : L.sections) :
    Module (HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s))
      (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s) (gradedHom X L F G)) :=
  Module.compHom (R := Localization.Away (homogeneousSection X L s))
    (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s) (gradedHom X L F G))
    (algebraMap (HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s))
      (Localization.Away (homogeneousSection X L s)))

/-- The degree-zero localization of the actual graded Hom module. -/
@[expose, stacks 0B5M "graded Hom localization"]
public noncomputable def homAtNonvanishingOpen (s : L.sections) :=
  GradedModuleDegreeZeroLocalization
    (sectionRingGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L)
    (gradedHomGrading X L F G)
    (homogeneousSection X L s)

/-- A homogeneous morphism regarded as a degree-zero fraction with denominator
`sⁿ` in the localization of the graded Hom module. -/
@[expose]
public noncomputable def homFraction (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) :
    homAtNonvanishingOpen X L F G s :=
  letI := Module.compHom (R := Localization.Away (homogeneousSection X L s))
    (LocalizedModule.Away (R := sectionRing
      (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s) (gradedHom X L F G))
    (algebraMap (HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X)
        (sectionSiteSheaf X) L) (homogeneousSection X L s))
      (Localization.Away (homogeneousSection X L s)))
  let x : gradedHom X L F G := DirectSum.of _ (n : ℤ) f
  ⟨LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
      x ⟨homogeneousSection X L s ^ n, by exact ⟨n, rfl⟩⟩,
    by
      change LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
          x ⟨homogeneousSection X L s ^ n, by exact ⟨n, rfl⟩⟩ ∈
        Submodule.span _ _
      apply Submodule.subset_span
      refine ⟨1, n, homogeneousSection_mem X L s, x, ?_, rfl⟩
      change gradedHomComparison X L F G x ∈
        sectionModuleGrading (sectionSiteRing X)
          (sectionSiteSheaf X) L
          (sheafHomSpace X.toRingedSpace F G)
          (n • (1 : ℤ))
      rw [show n • (1 : ℤ) = (n : ℤ) by simp]
      rw [gradedHomComparison_of]
      let T : ℤ → Type _ := fun k =>
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj
            ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L k)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
      let y : T (n : ℤ) := homToTwistedSection X L F G (n : ℤ) f
      change DirectSum.of T (n : ℤ) y ∈ (DirectSum.of T (n : ℤ)).range
      exact ⟨y, rfl⟩⟩

/-- The numerator of the fraction associated to a homogeneous morphism is
the degree-`n` morphism, and its denominator is `sⁿ`. -/
public theorem homFraction_val (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) :
    (homFraction X L F G s n f : LocalizedModule.Away
      (R := sectionRing (sectionSiteRing X)
        (sectionSiteSheaf X) L)
      (homogeneousSection X L s)
        (gradedHom X L F G)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (n : ℤ) f)
        ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ :=
  rfl

/-- A homogeneous numerator together with the power of `s` used as denominator. -/
public abbrev HomFractionData :=
  Σ n : ℕ, (F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
      (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
      ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ)))))

/-- Every element of the degree-zero localization has a homogeneous numerator
coming from a global morphism `F ⟶ G ⊗ Lⁿ`. -/
private lemma mem_degreeZero_iff
    {S : Type*} {M : Type*} {σ : Type*} {τ : Type*}
    [CommRing S] [AddCommGroup M] [Module S M]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒰 : ℕ → σ) [GradedRing 𝒰]
    [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
    [SetLike.GradedSMul 𝒰 𝒨]
    (f : S) (d : ℕ) (hf : f ∈ 𝒰 d)
    (y : LocalizedModule.Away f M) :
    y ∈ GradedModuleDegreeZeroLocalization 𝒰 𝒨 f ↔
      ∃ (n : ℕ) (x : M), x ∈ 𝒨 (n • (d : ℤ)) ∧
        y = LocalizedModule.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f) := by
  classical
  let _ := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒰 f) (Localization.Away f))
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨d', n, hf', x, hx, rfl⟩ := hy
        by_cases hfn : f ^ n = 0
        · have : Subsingleton (LocalizedModule.Away f M) :=
            LocalizedModule.subsingleton (S := Submonoid.powers f) (M := M)
              (by rw [← hfn]; exact ⟨n, rfl⟩)
          exact ⟨0, 0, by simp, Subsingleton.elim _ _⟩
        · have hdeg : n • d' = n • d :=
            DirectSum.degree_eq_of_mem_mem 𝒰
              (SetLike.pow_mem_graded n hf') (SetLike.pow_mem_graded n hf) hfn
          have hdeg' : n • (d' : ℤ) = n • (d : ℤ) := by
            simpa [nsmul_eq_mul] using congrArg (fun k : ℕ => (k : ℤ)) hdeg
          exact ⟨n, x, hdeg' ▸ hx, rfl⟩
    | zero => exact ⟨0, 0, by simp, by simp⟩
    | add y z _ _ hy hz =>
        obtain ⟨n, x, hx, rfl⟩ := hy
        obtain ⟨m, z, hz, rfl⟩ := hz
        refine ⟨n + m, (f ^ m) • x + (f ^ n) • z, ?_, ?_⟩
        · have hx' := SetLike.GradedSMul.smul_mem (A := 𝒰) (B := 𝒨)
            (SetLike.pow_mem_graded m hf) hx
          have hz' := SetLike.GradedSMul.smul_mem (A := 𝒰) (B := 𝒨)
            (SetLike.pow_mem_graded n hf) hz
          have h1 : (m • d : ℕ) +ᵥ (n • (d : ℤ)) = (n + m) • (d : ℤ) := by
            simp only [nsmul_eq_mul]; push_cast; change (m : ℤ) * d + n * d = _; ring
          have h2 : (n • d : ℕ) +ᵥ (m • (d : ℤ)) = (n + m) • (d : ℤ) := by
            simp only [nsmul_eq_mul]; push_cast; change (n : ℤ) * d + m * d = _; ring
          exact add_mem (h1 ▸ hx') (h2 ▸ hz')
        · rw [LocalizedModule.mk_add_mk]
          congr 1
          apply Subtype.ext
          simp [pow_add]
    | smul a y _ hy =>
        obtain ⟨n, x, hx, rfl⟩ := hy
        obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒰 hf a
        refine ⟨m + n, b • x, ?_, ?_⟩
        · have h := SetLike.GradedSMul.smul_mem (A := 𝒰) (B := 𝒨) hb hx
          have heq : (m • d : ℕ) +ᵥ (n • (d : ℤ)) = (m + n) • (d : ℤ) := by
            simp only [nsmul_eq_mul]; push_cast; change (m : ℤ) * d + n * d = _; ring
          exact heq ▸ h
        · change (HomogeneousLocalization.Away.mk 𝒰 hf m b hb).val •
              LocalizedModule.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f) = _
          rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
          congr 1
          apply Subtype.ext
          simp [pow_add]
  · rintro ⟨n, x, hx, rfl⟩
    exact Submodule.subset_span ⟨d, n, hf, x, hx, rfl⟩

private lemma gradedHom_mem_degree (n : ℤ) {x : gradedHom X L F G}
    (hx : x ∈ gradedHomGrading X L F G n) :
    ∃ f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L n))),
      x = DirectSum.of _ n f := by
  classical
  let T := sectionModuleGrading (sectionSiteRing X)
    (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G)
  change gradedHomComparison X L F G x ∈ T n at hx
  obtain ⟨q, hq⟩ := hx
  let f := (homToTwistedSection X L F G n).symm q
  refine ⟨f, ?_⟩
  apply (gradedHomComparison X L F G).injective
  calc
    gradedHomComparison X L F G x = DirectSum.of _ n q := hq.symm
    _ = gradedHomComparison X L F G (DirectSum.of _ n f) := by
      rw [gradedHomComparison_of]
      congr 1
      exact ((homToTwistedSection X L F G n).apply_symm_apply q).symm

private lemma exists_degreeZero_numerator (s : L.sections)
    (z : homAtNonvanishingOpen X L F G s) :
    ∃ (n : ℕ) (x : gradedHom X L F G), x ∈ gradedHomGrading X L F G (n • (1 : ℤ)) ∧
      (z : LocalizedModule.Away (homogeneousSection X L s) (gradedHom X L F G)) =
        LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s)) x
          ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ := by
  have hz_mem :
      (z : LocalizedModule.Away
        (homogeneousSection X L s) (gradedHom X L F G)) ∈
        GradedModuleDegreeZeroLocalization
          (sectionRingGrading (sectionSiteRing X)
            (sectionSiteSheaf X) L)
          (gradedHomGrading X L F G) (homogeneousSection X L s) :=
    z.2
  exact (mem_degreeZero_iff
    (S := sectionRing (sectionSiteRing X)
      (sectionSiteSheaf X) L)
    (M := gradedHom X L F G)
    (σ := AddSubgroup (sectionRing
      (sectionSiteRing X) (sectionSiteSheaf X) L))
    (τ := AddSubgroup (gradedHom X L F G))
    (𝒰 := sectionRingGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L)
    (𝒨 := gradedHomGrading X L F G)
    (homogeneousSection X L s) 1
    (homogeneousSection_mem X L s)
    (z : LocalizedModule.Away (homogeneousSection X L s)
      (gradedHom X L F G))).mp hz_mem

private lemma homFraction_surjective_aux (s : L.sections)
    (z : homAtNonvanishingOpen X L F G s) (n : ℕ) (x : gradedHom X L F G)
    (hx : x ∈ gradedHomGrading X L F G (n • (1 : ℤ)))
    (hz : (z : LocalizedModule.Away (homogeneousSection X L s) (gradedHom X L F G)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s)) x
        ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩) :
    ∃ a : HomFractionData X L F G, homFraction X L F G s a.1 a.2 = z := by
  have hdegree : n • (1 : ℤ) = (n : ℤ) := by simp
  exact (gradedHom_mem_degree X L F G (n : ℤ) (hdegree ▸ hx)).elim fun f hf =>
    ⟨⟨n, f⟩, Subtype.ext ((homFraction_val X L F G s n f).trans
      (hz.trans (congrArg (fun y => LocalizedModule.mk
        (S := Submonoid.powers (homogeneousSection X L s)) y
        ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩) hf)).symm)⟩

/-- Every element of the degree-zero localization has a homogeneous numerator
coming from a global morphism `F ⟶ G ⊗ Lⁿ`. -/
public theorem homFraction_surjective (s : L.sections) :
    Function.Surjective (fun a : HomFractionData X L F G =>
      homFraction X L F G s a.1 a.2) := fun z =>
  (exists_degreeZero_numerator X L F G s z).elim fun n hn =>
    hn.elim fun x hxz => homFraction_surjective_aux X L F G s z n x hxz.1 hxz.2

/-- The class of a homogeneous morphism divided by `sⁿ`. -/
public noncomputable def homFractionClass (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) :
    homAtNonvanishingOpen X L F G s :=
  homFraction X L F G s n f

/-- The class of a homogeneous morphism divided by `sⁿ` is the fraction itself. -/
public theorem homFractionClass_eq_homFraction (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) :
    homFractionClass X L F G s n f = homFraction X L F G s n f :=
  Eq.refl (homFraction X L F G s n f)

/-- **The degree-zero localization of a graded module is covariant in the graded module.** A
degree-preserving linear map `e : M ⟶ N` carries a degree-zero fraction `x / sⁿ` of `M` to
`e x / sⁿ`. Public because it is the map a naturality square over `Proj` is stated with — Stacks
Tag 0B5I asks its comparison `M̃ ⟶ f_* ℱ` to be natural in `ℱ`, and this is the map the graded
module of twisted sections contributes to that square. -/
@[expose]
public def degreeZeroLocalizationMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (A : ℕ → AddSubgroup R) [GradedRing A]
    (B : ℤ → AddSubgroup M) [DirectSum.Decomposition B]
    (C : ℤ → AddSubgroup N) [DirectSum.Decomposition C]
    [SetLike.GradedSMul A B] [SetLike.GradedSMul A C]
    (e : M →ₗ[R] N) (he : ∀ i x, x ∈ B i → e x ∈ C i) (s : R) :
    GradedModuleDegreeZeroLocalization A B s →+
      GradedModuleDegreeZeroLocalization A C s := by
  letI := Module.compHom (R := Localization.Away s)
    (LocalizedModule.Away s M)
    (algebraMap (HomogeneousLocalization.Away A s) (Localization.Away s))
  letI := Module.compHom (R := Localization.Away s)
    (LocalizedModule.Away s N)
    (algebraMap (HomogeneousLocalization.Away A s) (Localization.Away s))
  let f := LocalizedModule.map (Submonoid.powers s) e
  have hf : ∀ x ∈ GradedModuleDegreeZeroLocalization A B s,
      f x ∈ GradedModuleDegreeZeroLocalization A C s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, n, hs, m, hm, rfl⟩ := hx
        rw [LocalizedModule.map_mk]
        exact Submodule.subset_span ⟨d, n, hs, e m, he _ _ hm, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        change f ((algebraMap (HomogeneousLocalization.Away A s)
          (Localization.Away s) a) • x) ∈ _
        rw [map_smul]
        exact (GradedModuleDegreeZeroLocalization A C s).smul_mem a hx
  exact { toFun := fun x => ⟨f x, hf x x.2⟩
          map_zero' := Subtype.ext f.map_zero
          map_add' := fun x y => Subtype.ext (f.map_add x y) }

/-- The underlying fraction of `degreeZeroLocalizationMap` is the image of the fraction under
`LocalizedModule.map`. -/
public lemma degreeZeroLocalizationMap_coe
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (A : ℕ → AddSubgroup R) [GradedRing A]
    (B : ℤ → AddSubgroup M) [DirectSum.Decomposition B]
    (C : ℤ → AddSubgroup N) [DirectSum.Decomposition C]
    [SetLike.GradedSMul A B] [SetLike.GradedSMul A C]
    (e : M →ₗ[R] N) (he : ∀ i x, x ∈ B i → e x ∈ C i) (s : R)
    (x : GradedModuleDegreeZeroLocalization A B s) :
    (degreeZeroLocalizationMap A B C e he s x : LocalizedModule.Away s N) =
      LocalizedModule.map (Submonoid.powers s) e (x : LocalizedModule.Away s M) := rfl

private def gradedHomComparisonLinear : gradedHom X L F G →ₗ[
    sectionRing (sectionSiteRing X)
      (sectionSiteSheaf X) L]
    sectionModule (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G) :=
  { __ := (gradedHomComparison X L F G).toAddMonoidHom
    map_smul' := fun _ _ => (gradedHomComparison X L F G).apply_symm_apply _ }

private def homLocalizationComparison (s : L.sections) :
    homAtNonvanishingOpen X L F G s →+
      sectionAtNonvanishingOpen X L
        (sheafHomSpace X.toRingedSpace F G) s := by
  letI := sectionModuleDecomposition (sectionSiteRing X)
    (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G)
  letI := sectionModuleGradedSMul (sectionSiteRing X)
    (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G)
  exact degreeZeroLocalizationMap
    (sectionRingGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L)
    (gradedHomGrading X L F G)
    (sectionModuleGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G))
    (gradedHomComparisonLinear X L F G) (fun _ _ h => h)
    (homogeneousSection X L s)

private def internalHomSectionToOver (U : Opens X.toRingedSpace) :
    (sheafHomSpace X.toRingedSpace F G).val.obj
      (op U) →+ (F.over U ⟶ G.over U) where
  toFun t := ⟨t⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restrict a degree-zero localized graded morphism to the open where `s`
trivializes `L`, dividing its degree-`n` numerator by `sⁿ`. -/
@[stacks 0B5M]
public noncomputable def homLocalizationMap (s : L.sections) :
    homAtNonvanishingOpen X L F G s →+
      (F.over (nonvanishingOpen L s) ⟶
        G.over (nonvanishingOpen L s)) :=
  (internalHomSectionToOver X F G
    (nonvanishingOpen L s)).comp
    ((sectionLocalizationMap X L
      (sheafHomSpace X.toRingedSpace F G) s).comp
      (homLocalizationComparison X L F G s))

private lemma homLocalizationComparison_fraction_coe (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) :
    (homLocalizationComparison X L F G s (homFractionClass X L F G s n f) :
      LocalizedModule.Away (homogeneousSection X L s)
        (sectionModule (sectionSiteRing X)
          (sectionSiteSheaf X) L
          (sheafHomSpace X.toRingedSpace F G))) =
        LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
          (DirectSum.of _ (n : ℤ) (homToTwistedSection X L F G n f))
          ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ := by
  change LocalizedModule.map (Submonoid.powers (homogeneousSection X L s))
    (gradedHomComparisonLinear X L F G)
    (homFraction X L F G s n f : LocalizedModule.Away
      (homogeneousSection X L s) (gradedHom X L F G)) = _
  refine Eq.trans (congrArg (fun y => LocalizedModule.map
    (Submonoid.powers (homogeneousSection X L s)) (gradedHomComparisonLinear X L F G) y)
    (homFraction_val X L F G s n f)) ?_
  refine Eq.trans (LocalizedModule.map_mk (Submonoid.powers (homogeneousSection X L s))
    (gradedHomComparisonLinear X L F G) (DirectSum.of _ (n : ℤ) f)
    ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩) ?_
  exact congrArg (fun x => LocalizedModule.mk
    (S := Submonoid.powers (homogeneousSection X L s)) x
    ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩)
    (gradedHomComparison_of X L F G n f)

/-- A homogeneous morphism `f : F ⟶ G ⊗ Lⁿ`, divided by `sⁿ`, restricts
to the unique morphism on `X_s` whose tensor product with `sⁿ` is the
restriction of `f`. -/
@[stacks 0B5M "homogeneous fraction formula"]
public theorem homLocalizationMap_fraction (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ)))))
    (t : (sheafHomSpace X.toRingedSpace F G).val.obj
        (op (nonvanishingOpen L s)))
    (hdiv :
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj
          ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ))))).val.map
            (terminal.from _).op
              (homToTwistedSection X L F G n f) =
      tensorSectionAtOpen X L
        (sheafHomSpace X.toRingedSpace F G)
        (nonvanishingOpen L s) n t
        ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ)).val.map
            (terminal.from _).op (sectionPower X L s n))) :
    homLocalizationMap X L F G s (homFractionClass X L F G s n f) = ⟨t⟩ :=
  by
    let z := homLocalizationComparison X L F G s (homFractionClass X L F G s n f)
    have hz := homLocalizationComparison_fraction_coe X L F G s n f
    have h := sectionLocalizationMap_fraction X L
      (sheafHomSpace X.toRingedSpace F G)
      s n (homToTwistedSection X L F G n f) z t hz hdiv
    exact congrArg (fun t => (⟨t⟩ : F.over _ ⟶ G.over _)) h

/-! ### When a degree-zero fraction vanishes -/

/-- A fraction with denominator a power of `r` is zero in the localized module exactly when some
power of `r` annihilates its numerator. -/
@[ega "0 1.2.2" "special case"]
theorem localizedModule_mk_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (x : M) (t : Submonoid.powers r) :
    LocalizedModule.mk x t = 0 ↔ ∃ e : ℕ, r ^ e • x = 0 := by
  rw [show (0 : LocalizedModule (Submonoid.powers r) M) = LocalizedModule.mk 0 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨u, h⟩
    obtain ⟨e, he⟩ := u.2
    refine ⟨e, ?_⟩
    rw [show r ^ e = (u : R) from he]
    simpa [Submonoid.smul_def] using h
  · rintro ⟨e, h⟩
    exact ⟨⟨r ^ e, e, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

/-- A morphism `F ⟶ G ⊗ Lⁿ`, placed in degree `n`, is a homogeneous element of degree `n` of the
graded Hom module. -/
public theorem of_mem_gradedHomGrading (n : ℤ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n)))) :
    (DirectSum.of _ n f : gradedHom X L F G) ∈ gradedHomGrading X L F G n := by
  change gradedHomComparison X L F G (DirectSum.of _ n f) ∈
    sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G) n
  rw [gradedHomComparison_of]
  exact ⟨homToTwistedSection X L F G n f, rfl⟩

/-- Multiplying a homogeneous morphism of degree `n` by `sᵉ` gives a homogeneous morphism of
degree `e + n`: this is the morphism `f ⊗ sᵉ` of Tag 01XQ. -/
public theorem exists_hom_smul_pow (s : L.sections) (n : ℤ) (e : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n)))) :
    ∃ g : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L ((e : ℤ) + n)))),
      homogeneousSection X L s ^ e • (DirectSum.of _ n f : gradedHom X L F G) =
        DirectSum.of _ ((e : ℤ) + n) g := by
  have hs : homogeneousSection X L s ^ e ∈
      sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L e := by
    simpa using SetLike.pow_mem_graded e (homogeneousSection_mem X L s)
  exact gradedHom_mem_degree X L F G ((e : ℤ) + n)
    (SetLike.GradedSMul.smul_mem (A := sectionRingGrading (sectionSiteRing X)
      (sectionSiteSheaf X) L) (B := gradedHomGrading X L F G) hs
      (of_mem_gradedHomGrading X L F G n f))

/-- A homogeneous morphism placed in degree `n` is zero in the graded Hom module exactly when
the twisted internal-Hom section it corresponds to is zero. -/
public theorem of_eq_zero_iff (n : ℤ)
    (g : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n)))) :
    (DirectSum.of _ n g : gradedHom X L F G) = 0 ↔
      homToTwistedSection X L F G n g = 0 := by
  constructor
  · intro h
    have h0 : gradedHomComparison X L F G (DirectSum.of _ n g) = 0 := by
      rw [h]
      exact map_zero (gradedHomComparison X L F G)
    rw [gradedHomComparison_of] at h0
    exact DirectSum.of_injective n (h0.trans (AddMonoidHom.map_zero _).symm)
  · intro h
    apply (gradedHomComparison X L F G).injective
    rw [gradedHomComparison_of, h, map_zero (gradedHomComparison X L F G)]
    exact AddMonoidHom.map_zero _

/-- **The vanishing criterion for degree-zero fractions of twisted morphisms.** The fraction
`f / sⁿ` is zero in the degree-zero localization exactly when some power of `s` annihilates `f`,
that is when `f ⊗ sᵉ = 0` for some `e`. This is the step the injectivity half of Tag 01XQ turns
on. -/
public theorem homFraction_eq_zero_iff (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))) :
    homFraction X L F G s n f = 0 ↔
      ∃ e : ℕ, homogeneousSection X L s ^ e •
        (DirectSum.of _ (n : ℤ) f : gradedHom X L F G) = 0 := by
  refine Iff.trans ZeroMemClass.coe_eq_zero.symm ?_
  refine Iff.trans ?_ (localizedModule_mk_eq_zero_iff (homogeneousSection X L s)
    (DirectSum.of _ (n : ℤ) f : gradedHom X L F G)
    ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩)
  exact Eq.congr_left (homFraction_val X L F G s n f)

/-- `homFraction_eq_zero_iff` for the class of a homogeneous morphism: the class of `f / sⁿ`
vanishes exactly when some `s`-power multiple of `f` vanishes. -/
public theorem homFractionClass_eq_zero_iff (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))) :
    homFractionClass X L F G s n f = 0 ↔
      ∃ e : ℕ, homogeneousSection X L s ^ e •
        (DirectSum.of _ (n : ℤ) f : gradedHom X L F G) = 0 :=
  homFraction_eq_zero_iff X L F G s n f

end LocalizedAction

end GradedHomLocalization

end Stacks.SheafOfModules

end
