module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Limits.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf on the big étale site of an algebraic space

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `X` one of its objects.
The value at an algebraic space `U` over `S` of the structure presheaf of the big étale site
is the ring `Γ(U, 𝒪_U)` of global regular functions on `U`, that is, the ring of global
sections of the structure presheaf of `U`'s small étale site; its restriction maps are
pullback of regular functions. This file proves that this presheaf is a sheaf for the big
étale topology, and packages the result as a sheaf of rings on the big étale site of `X`.

The sheaf condition is representability. Global regular functions on `U` are the same thing as
morphisms `U ⟶ 𝔸¹_S` of algebraic spaces: by `AlgebraicGeometry.Space.globalFunctionsChartEquiv`
they are a compatible family of regular functions on *all* scheme charts of `U`, such a family
is a morphism of presheaves out of `U` by `CategoryTheory.Presheaf.costructuredArrowSectionsEquiv`,
and the presheaf of regular functions on the big fppf site over `S` is represented by the affine
line. So the structure presheaf is the presheaf represented by the affine line viewed as an
algebraic space, and what has to be proved is that the big étale topology of algebraic spaces is
subcanonical.

## Main definitions

* `CategoryTheory.Presheaf.costructuredArrowSectionsEquiv`: a compatible family of sections of
  `G` over the representable charts of a presheaf `F` is a morphism `F ⟶ G`.
* `AlgebraicGeometry.Space.affineLineBigFppfOver` and
  `AlgebraicGeometry.Space.affineLineSpace`: the affine line over `S` as an object of the big
  fppf site and as an algebraic space.
* `AlgebraicGeometry.Space.globalFunctionsHomEquiv`: global regular functions on an algebraic
  space are its morphisms to the affine line.
* `AlgebraicGeometry.BigEtaleSpaceSite.structurePresheaf` and
  `AlgebraicGeometry.BigEtaleSpaceSite.structureSheaf`: the structure presheaf and structure
  sheaf of rings on the big étale site of an object `X` of `T`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_desc_of_etaleCovering_representable`: morphisms into a
  representable algebraic space descend along an étale covering of algebraic spaces.
* `AlgebraicGeometry.BigEtaleSpaceSite.isSheaf_yoneda`: the big étale topology of algebraic
  spaces is subcanonical at representable objects.
* `AlgebraicGeometry.BigEtaleSpaceSite.globalFunctionsPresheaf_isSheaf` and
  `AlgebraicGeometry.BigEtaleSpaceSite.structurePresheaf_isSheaf`.

## Implementation notes

**Nothing here carries a Stacks attribute, deliberately.** The statement proved is the content
of Stacks 0DF9, a *remark* of Chapter 73 (Topologies on Algebraic Spaces); this file supplies
the helper. A formalization of Stacks 0DF9 should build its big étale structure sheaf from these
declarations rather than re-coin them. The same applies to Stacks 041F
(base change of étale coverings), whose étale case is proved here as
`AlgebraicGeometry.Space.isEtaleCovering_fibreProduct` alongside the registered fppf case
`AlgebraicGeometry.Space.isFppfCovering_fibreProduct`.

**Gabber's theorem is not needed, because the target is representable.** Descent of morphisms
of algebraic spaces along an fpqc covering, Stacks 04P2, is available here only conditionally on
Stacks 0APL — that every algebraic space satisfies the fpqc sheaf condition — which this
library does not have. But the proof of Stacks 04P2 asks for the fpqc sheaf condition for the
*target* alone, and the target here is the affine line, which is representable. So
`AlgebraicGeometry.BigFppfOver.subcanonical_fpqcTopology` discharges it outright: the fpqc
topology comapped to the big fppf site over `S` is subcanonical, by the same argument that makes
the fppf topology of the site subcanonical, pushed into the slice over `S`. That is why
`AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc` is stated with
the hypothesis on the target.

**Generality.** The sections-to-morphisms equivalence is stated for arbitrary presheaves on an
arbitrary category, and the affine-line descriptions of global functions for an arbitrary object
of the site; algebraicity enters only where the atlas equivalence of
`AlgebraicGeometry.Space.globalFunctionsChartEquiv` does.

**Three of the imports are retained as cosmetic.** `Mathlib.AlgebraicGeometry.AffineSpace`,
`Mathlib.CategoryTheory.Limits.Presheaf` and
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies` can each be removed without
changing a single signature, because the names they supply arrive transitively through the
remaining imports; they are kept because this file names `AlgebraicGeometry.AffineSpace`,
`CategoryTheory.Presheaf.isColimitTautologicalCocone` and
`AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering` directly, and a transitive route to
a name one uses directly is a dependency on somebody else's import list. The four declarations
`structurePresheaf_obj`, `structurePresheaf_map`, `structureSheaf_obj` and `structureSheaf_map`
are likewise unconsumed here on purpose: they are the rewriting interface a ringed-site
comparison needs.

## References

* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Presheaf

section

universe v' w'

variable {C : Type w'} [Category.{v'} C]

/-- A compatible family of sections of `G` over the representable charts of `F` is the same
thing as a morphism `F ⟶ G`: the charts of `F` present it as a colimit of representables, and
a section over a chart is a morphism out of that representable by Yoneda. -/
@[sga "3 I 1.7.0"]
noncomputable def costructuredArrowSectionsEquiv (F G : Cᵒᵖ ⥤ Type v') :
    ((CostructuredArrow.proj yoneda F).op ⋙ G).sections ≃ (F ⟶ G) where
  toFun s := (Presheaf.isColimitTautologicalCocone F).desc
    { pt := G
      ι :=
        { app j := (yonedaEquiv (C := C) (X := j.left) (F := G)).symm (s.val (op j))
          naturality := by
            intro j k f
            apply (yonedaEquiv (C := C) (X := j.left) (F := G)).injective
            simp only [Functor.comp_map, CostructuredArrow.proj_map,
              Functor.const_obj_map, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
            simpa using s.property f.op } }
  invFun η := by
    refine ⟨fun j => (yonedaEquiv (C := C) (X := j.unop.left) (F := G))
      (j.unop.hom ≫ η), ?_⟩
    intro j k f
    change G.map f.unop.left.op (yonedaEquiv (j.unop.hom ≫ η)) =
      yonedaEquiv (k.unop.hom ≫ η)
    rw [yonedaEquiv_naturality]
    congr 1
    rw [← Category.assoc, CostructuredArrow.w f.unop]
  left_inv s := by
    apply Subtype.ext
    funext j
    exact (congrArg (yonedaEquiv (C := C) (X := j.unop.left) (F := G))
      ((Presheaf.isColimitTautologicalCocone F).fac _ j.unop)).trans
        (yonedaEquiv.apply_symm_apply _)
  right_inv η := by
    apply (Presheaf.isColimitTautologicalCocone F).hom_ext
    intro j
    rw [(Presheaf.isColimitTautologicalCocone F).fac]
    exact yonedaEquiv.symm_apply_apply _

/-- The morphism attached to a compatible family of sections restricts on each chart to the
morphism Yoneda attaches to the section there. -/
theorem costructuredArrowSectionsEquiv_fac (F G : Cᵒᵖ ⥤ Type v')
    (s : ((CostructuredArrow.proj yoneda F).op ⋙ G).sections)
    (j : CostructuredArrow yoneda F) :
    j.hom ≫ costructuredArrowSectionsEquiv F G s =
      (yonedaEquiv (X := j.left) (F := G)).symm (s.val (op j)) :=
  (Presheaf.isColimitTautologicalCocone F).fac _ j

/-- The equivalence is natural in the source presheaf: restricting a compatible family along
`f : F' ⟶ F` corresponds to precomposing with `f`. -/
theorem costructuredArrowSectionsEquiv_natural
    {F F' G : Cᵒᵖ ⥤ Type v'} (f : F' ⟶ F)
    (s : ((CostructuredArrow.proj yoneda F).op ⋙ G).sections) :
    costructuredArrowSectionsEquiv F' G
      ⟨fun j => s.val ((CostructuredArrow.map f).op.obj j),
        fun _ => s.property ((CostructuredArrow.map f).op.map _)⟩ =
      f ≫ costructuredArrowSectionsEquiv F G s := by
  apply (Presheaf.isColimitTautologicalCocone F').hom_ext
  intro j
  show j.hom ≫ _ = j.hom ≫ _
  rw [costructuredArrowSectionsEquiv_fac, ← Category.assoc]
  exact (costructuredArrowSectionsEquiv_fac F G s ((CostructuredArrow.map f).obj j)).symm

end

end CategoryTheory.Presheaf

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high)
    AlgebraicGeometry.Space.hasPullback_presheaf_bigEtaleStructureSheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.Space

/-! ### Base change of étale coverings of algebraic spaces -/

/-- **Stacks 041F**, base change. Pulling an étale covering of algebraic spaces over `S` back
along a morphism of algebraic spaces gives an étale covering of the new target: the first
projections of the fibre products of Stacks 02X2 form an étale covering.

The attribute is withheld: Stacks 041F is a tag of Chapter 73, and its composition half is
already registered as
`AlgebraicGeometry.Space.isEtaleCovering_comp`. -/
theorem isEtaleCovering_fibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X X' : AlgebraicSpaces B S hS}
    (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (g : X' ⟶ X)
    (hf : IsEtaleCovering B S hS (fun i => (Xi i).1) (fun i => (f i).hom)) :
    IsEtaleCovering B S hS
      (fun i => (AlgebraicSpaces.fiberProduct B S hS g (f i)).1)
      (fun i => pullback.fst g.hom (f i).hom) := by
  refine ⟨X'.property, fun i => (AlgebraicSpaces.fiberProduct B S hS g (f i)).property,
    fun i => isEtale_of_isPullback B S hS _ _ (f i) g
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)).flip (hf.etale i), ?_⟩
  apply Set.eq_univ_of_forall
  intro x'
  have hcover : pointsMap B S hS X'.1 g.hom x' ∈
      ⋃ i, Set.range (fun y => pointsMap B S hS (Xi i).1 (f i).hom y) := by
    rw [hf.jointly_surjective]
    exact Set.mem_univ _
  rcases Set.mem_iUnion.mp hcover with ⟨i, y, hy⟩
  obtain ⟨w, hwp, _⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)) x' y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨w, hwp⟩⟩

/-! ### Descent of morphisms into a representable algebraic space -/

/-- Morphisms into a *representable* algebraic space descend along an étale covering of
algebraic spaces over `S`. This is Stacks 04P2 at a representable target, and unlike the
general case it needs no input from Stacks 0APL. -/
theorem existsUnique_desc_of_etaleCovering_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : IsEtaleCovering B S hS (fun i => (X i).1) (fun i => (f i).hom))
    (A : BigFppfOver B S hS)
    (g : ∀ i, X i ⟶ representedAlgebraicSpace B S hS A)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j) :
    ∃! h : Y ⟶ representedAlgebraicSpace B S hS A, ∀ i, f i ≫ h = g i :=
  existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc B S hS f
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hf) _
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS A) g hg

/-! ### The affine line over `S` -/

/-- Global regular functions on a scheme over `S` are its morphisms over `S` to the affine
line, for any one-element index type. -/
@[sga "3 IV 3.3.3.2"]
noncomputable def affineLinePoints (S : Scheme.{u}) (Y : Over S)
    (n : Type u) [Unique n] : Γ(Y.left, ⊤) ≃ (Y ⟶ Over.mk ((AffineSpace n S) ↘ S)) := by
  letI : (AffineSpace n S).Over S := OverClass.ofHom ((AffineSpace.over n S).hom)
  letI : Y.left.Over S := OverClass.fromOver Y
  let eVec : (n → Γ(Y.left, ⊤)) ≃ Γ(Y.left, ⊤) := Equiv.funUnique n _
  let e : Γ(Y.left, ⊤) ≃
      { f : Y.left ⟶ AffineSpace n S // f.IsOver S } :=
    eVec.symm.trans (AffineSpace.homOverEquiv S).symm
  let toOver : { f : Y.left ⟶ AffineSpace n S // f.IsOver S } →
      (Y ⟶ Over.mk ((AffineSpace n S) ↘ S)) := fun f =>
    Over.homMk f.1 ((Scheme.Hom.isOver_iff (S := S)).mp f.2)
  let fromOver : (Y ⟶ Over.mk ((AffineSpace n S) ↘ S)) →
      { f : Y.left ⟶ AffineSpace n S // f.IsOver S } := fun f =>
    ⟨f.left, (Scheme.Hom.isOver_iff (S := S)).mpr f.w⟩
  refine
    { toFun := toOver ∘ e
      invFun := e.symm ∘ fromOver
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    dsimp [toOver, fromOver]
    exact e.symm_apply_apply s
  · intro f
    calc
      toOver (e (e.symm (fromOver f))) = toOver (fromOver f) :=
        congrArg toOver (e.apply_symm_apply (fromOver f))
      _ = f := Over.homMk_eta f _

/-- The description of regular functions as morphisms to the affine line is natural. -/
theorem affineLinePoints_natural (S : Scheme.{u})
    {Y Z : Over S} (n : Type u) [Unique n] (f : Y ⟶ Z) (s : Γ(Z.left, ⊤)) :
    f ≫ affineLinePoints S Z n s = affineLinePoints S Y n (f.left.appTop s) := by
  ext
  show f.left ≫ AffineSpace.homOfVector (Z.left ↘ S) (uniqueElim s) =
    AffineSpace.homOfVector (Y.left ↘ S) (uniqueElim (f.left.appTop s))
  rw [AffineSpace.comp_homOfVector, show f.left ≫ (Z.left ↘ S) = Y.left ↘ S by simp]
  congr 1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine line over `S`, as an object of the big fppf site over `S`: it is of finite type
over `S`, hence small enough to belong to the site. -/
noncomputable def affineLineBigFppfOver : BigFppfOver B S hS := by
  have hA : B.Contains (AffineSpace PUnit.{u + 1} S) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (AffineSpace PUnit.{u + 1} S ↘ S) hS
  exact Over.mk (ObjectProperty.homMk (AffineSpace PUnit.{u + 1} S ↘ S) :
    B.obj hA ⟶ B.obj hS)

/-- The affine line over `S`, as an algebraic space over `S`. -/
noncomputable abbrev affineLineSpace : AlgebraicSpaces B S hS :=
  representedAlgebraicSpace B S hS (affineLineBigFppfOver B S hS)

/-- Global regular functions on an object of the big fppf site over `S` are its morphisms to
the affine line. -/
@[sga "3 IV 3.3.3.2" "special case"]
noncomputable def affineLineChartPoints (Y : BigFppfOver B S hS) :
    Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ≃ (Y ⟶ affineLineBigFppfOver B S hS) :=
  (affineLinePoints S ((Over.post B.inclusion).obj Y) PUnit.{u + 1}).trans
    ((Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).homEquiv
      (Y := affineLineBigFppfOver B S hS)).symm

/-- The morphism to the affine line attached to a regular function on an object of the site
has the expected image in the slice over `S` in all schemes. -/
theorem map_affineLineChartPoints
    (Y : BigFppfOver B S hS)
    (s : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)) :
    (Over.post B.inclusion).map (affineLineChartPoints B S hS Y s) =
      affineLinePoints S ((Over.post B.inclusion).obj Y) PUnit.{u + 1} s :=
  (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).map_preimage _

/-- The description of regular functions on the site as morphisms to the affine line is
natural. -/
theorem affineLineChartPoints_natural
    {Y Z : BigFppfOver B S hS} (f : Y ⟶ Z)
    (s : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :
    affineLineChartPoints B S hS Y
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom s) =
      f ≫ affineLineChartPoints B S hS Z s := by
  apply (Over.post B.inclusion).map_injective
  exact (map_affineLineChartPoints B S hS Y _).trans
    ((affineLinePoints_natural S PUnit.{u + 1} ((Over.post B.inclusion).map f) s).symm.trans
      ((congrArg (fun k => (Over.post B.inclusion).map f ≫ k)
        (map_affineLineChartPoints B S hS Z s)).symm.trans
          ((Over.post B.inclusion).map_comp f _).symm))

/-- The presheaf of regular functions on the big fppf site over `S` is represented by the
affine line. -/
@[sga "3 IV 3.3.3.2" "special case", sga "3 V 6.1" "(i)"]
noncomputable def gammaAffineLineIso :
    (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat ≅
      yoneda.obj (affineLineBigFppfOver B S hS) :=
  NatIso.ofComponents (fun Y => (affineLineChartPoints B S hS Y.unop).toIso) (by
    intro Y Z f
    ext s
    exact affineLineChartPoints_natural B S hS f.unop s)

/-! ### Global functions as morphisms to the affine line -/

/-- A compatible family of regular functions on all scheme charts of a presheaf `F` over `S` is
a morphism from `F` to the affine line. -/
noncomputable def chartFunctionsHomEquiv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    chartFunctions B S hS F ≃ (F ⟶ (affineLineSpace B S hS).obj) :=
  (Presheaf.costructuredArrowSectionsEquiv F
    ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat)).trans
      ((Iso.refl F).homCongr (gammaAffineLineIso B S hS))

/-- The description of compatible families of regular functions as morphisms to the affine line
is natural. -/
theorem chartFunctionsHomEquiv_natural
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : G ⟶ F)
    (s : chartFunctions B S hS F) :
    chartFunctionsHomEquiv B S hS G (chartFunctionsMap B S hS f s) =
      f ≫ chartFunctionsHomEquiv B S hS F s :=
  (congrArg (· ≫ (gammaAffineLineIso B S hS).hom)
    (Presheaf.costructuredArrowSectionsEquiv_natural
      (G := (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat) f s)).trans
    (Category.assoc _ _ _)

/-- Global regular functions on an algebraic space over `S` are its morphisms to the affine
line. -/
noncomputable def globalFunctionsHomEquiv (U : AlgebraicSpaces B S hS) :
    globalFunctions' B S hS U.obj ≃ (U ⟶ affineLineSpace B S hS) :=
  ((globalFunctionsChartEquiv B S hS U).val.toEquiv.trans
    (chartFunctionsHomEquiv B S hS U.obj)).trans
      { toFun := fun f => ObjectProperty.homMk f
        invFun := fun f => f.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The description of global regular functions as morphisms to the affine line is natural. -/
theorem globalFunctionsHomEquiv_natural
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U)
    (s : globalFunctions' B S hS U.obj) :
    globalFunctionsHomEquiv B S hS V (globalFunctionsMap B S hS f s) =
      f ≫ globalFunctionsHomEquiv B S hS U s := by
  apply ObjectProperty.hom_ext
  show chartFunctionsHomEquiv B S hS V.obj
    ((globalFunctionsChartEquiv B S hS V).val (globalFunctionsMap B S hS f s)) = _
  rw [globalFunctionsMap_chart]
  exact chartFunctionsHomEquiv_natural B S hS f.hom _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### The big étale topology is subcanonical at representable objects -/

/-- A presheaf represented by a representable algebraic space satisfies the sheaf condition for
an étale covering family of algebraic spaces. -/
private theorem isSheafFor_yoneda_of_etaleCovering
    {I : Type v} {Y : T.Spaces} (Xi : I → T.Spaces) (f : ∀ i, Xi i ⟶ Y)
    (hf : Space.IsEtaleCovering T.fppfSite S T.fppf_mem
      (fun i => (Xi i).obj) (fun i => (f i).hom))
    (A : BigFppfOver T.fppfSite S T.fppf_mem) :
    Presieve.IsSheafFor
      (yoneda.obj (Space.representedAlgebraicSpace T.fppfSite S T.fppf_mem A))
      (Presieve.ofArrows Xi f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  apply Space.existsUnique_desc_of_etaleCovering_representable
    T.fppfSite S T.fppf_mem f hf A x
  intro i j
  exact hx i j _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem (f i) (f j)).w

/-- The big étale topology of algebraic spaces over `S` is subcanonical at representable
objects: the presheaf represented by a representable algebraic space is a sheaf. -/
theorem isSheaf_yoneda (A : BigFppfOver T.fppfSite S T.fppf_mem) :
    Presieve.IsSheaf T.topology
      (yoneda.obj (Space.representedAlgebraicSpace T.fppfSite S T.fppf_mem A)) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y g R hR
  obtain ⟨E, rfl, hE⟩ := hR
  let P (i : E.I₀) := AlgebraicSpaces.fiberProduct T.fppfSite S T.fppf_mem g (E.f i)
  let p (i : E.I₀) : P i ⟶ Y := ObjectProperty.homMk (pullback.fst g.hom (E.f i).hom)
  let q (i : E.I₀) : P i ⟶ E.X i := ObjectProperty.homMk (pullback.snd g.hom (E.f i).hom)
  have hp (i : E.I₀) : IsPullback (p i) (q i) g (E.f i) :=
    AlgebraicSpaces.isPullback_fiberProduct T.fppfSite S T.fppf_mem g (E.f i)
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback E.f hp]
  exact (Presieve.isSheafFor_iff_generate (Presieve.ofArrows P p)).1
    (isSheafFor_yoneda_of_etaleCovering T P p
      (Space.isEtaleCovering_fibreProduct T.fppfSite S T.fppf_mem E.X E.f g hE.1) A)

/-! ### The structure sheaf -/

/-- The presheaf of global regular functions on algebraic spaces over `S` is a sheaf for the
big étale topology: it is the presheaf represented by the affine line. -/
theorem globalFunctionsPresheaf_isSheaf :
    Presheaf.IsSheaf T.topology
      (Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget T.topology
    (Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem) (forget CommRingCat.{u + 1})).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := yoneda.obj (Space.affineLineSpace T.fppfSite S T.fppf_mem))
    (fun {U} => Space.globalFunctionsHomEquiv T.fppfSite S T.fppf_mem U)
    (fun {U V} f s =>
      Space.globalFunctionsHomEquiv_natural T.fppfSite S T.fppf_mem f s)).2
  exact isSheaf_yoneda T _

/-- The structure presheaf on the big étale site of `X`: its value on an algebraic space `U`
over `X` is the ring of global regular functions on `U`. -/
noncomputable abbrev structurePresheaf (X : T.Spaces) :
    (Over X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Over.forget X).op ⋙ Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem

/-- The value of the structure presheaf on `U ⟶ X` is the ring of global sections of the small
étale structure sheaf of `U`. -/
@[simp] theorem structurePresheaf_obj (X : T.Spaces) (U : (Over X)ᵒᵖ) :
    (structurePresheaf T X).obj U =
      CommRingCat.of (Space.globalFunctions' T.fppfSite S T.fppf_mem U.unop.left.obj) := rfl

/-- Restriction on the big étale site is pullback of global regular functions. -/
@[simp] theorem structurePresheaf_map (X : T.Spaces)
    {U V : (Over X)ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf T X).map f =
      CommRingCat.ofHom
        (Space.globalFunctionsMap T.fppfSite S T.fppf_mem f.unop.left) := rfl

/-- Global regular functions satisfy étale descent on the big étale site of `X`. -/
theorem structurePresheaf_isSheaf (X : T.Spaces) :
    Presheaf.IsSheaf (T.bigEtaleTopology X) (structurePresheaf T X) :=
  (Over.forget X).op_comp_isSheaf_of_isSheaf
    (T.topology.over X) T.topology _ (globalFunctionsPresheaf_isSheaf T)

/-- The structure sheaf of rings on the big étale site of `X`. -/
noncomputable def structureSheaf (X : T.Spaces) :
    Sheaf (T.bigEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨structurePresheaf T X, structurePresheaf_isSheaf T X⟩

/-- The value of the structure sheaf on an object of the big étale site. -/
@[simp] theorem structureSheaf_obj (X : T.Spaces) (U : (Over X)ᵒᵖ) :
    (structureSheaf T X).obj.obj U =
      CommRingCat.of (Space.globalFunctions' T.fppfSite S T.fppf_mem U.unop.left.obj) := rfl

/-- The restriction maps of the structure sheaf. -/
@[simp] theorem structureSheaf_map (X : T.Spaces)
    {U V : (Over X)ᵒᵖ} (f : U ⟶ V) :
    (structureSheaf T X).obj.map f =
      CommRingCat.ofHom
        (Space.globalFunctionsMap T.fppfSite S T.fppf_mem f.unop.left) := rfl

end AlgebraicGeometry.BigEtaleSpaceSite

end
