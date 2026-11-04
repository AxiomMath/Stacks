module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf-hom of two sheaves of modules, the dual sheaf, and the evaluation pairing

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of
rings is a sheaf. For sheaves of `𝒪`-modules `F` and `G`, the *sheaf-hom*
`SheafHom(F, G)` is the sheaf of `𝒪`-modules whose sections over `U` are the `𝒪|_U`-linear
maps `F|_U ⟶ G|_U`. Its underlying presheaf is the internal-hom presheaf `internalHom` of
[Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), which that tag proves is a
sheaf as soon as the target is; this file packages it as an object of `SheafOfModules` and
builds the *evaluation pairing* `SheafHom(F, G) ⊗ F ⟶ G`.

The *dual* `F^∨ = SheafHom(F, 𝒪)` is the special case `G := 𝒪`, and its evaluation pairing
`F^∨ ⊗ F ⟶ 𝒪` is the pairing which [Stacks, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
consumes: `Stacks.SheafOfModules.isInvertible_of_pairing` turns a pairing that sheafification
inverts into invertibility of `F`.

## Main definitions

* `Stacks.SheafOfModules.evalSection` is the value of the evaluation pairing on a pair of
  sections: a section of the internal hom over `U` is a morphism `F|_U ⟶ G|_U` on the slice
  site `C/U`, and `evalSection` reads off its component at the terminal object `𝟙_U` of
  `C/U`, which is a map `F(U) ⟶ G(U)`.
* `Stacks.SheafOfModules.evalBilinear` bundles those values as a `Stacks.BilinearMap`, that
  is, as a pairing of presheaves of modules given on sections. This needs no sheaf condition
  at all.
* `Stacks.SheafOfModules.sheafHom` is the sheaf-hom `SheafHom(F, G)` as an object of
  `SheafOfModules`, and `Stacks.SheafOfModules.dualSheaf` is the dual `F^∨ = SheafHom(F, 𝒪)`.
* `Stacks.SheafOfModules.evalPresheaf` is the evaluation pairing as a morphism of presheaves
  of modules out of the pointwise tensor product, and
  `Stacks.SheafOfModules.evaluationPresheaf` is its dual special case `F^∨ ⊗ F ⟶ 𝒪`.
* `Stacks.SheafOfModules.evaluation` is the evaluation pairing of sheaves of modules
  `(F^∨ ⊗ F)^# ⟶ 𝒪`, obtained from `evaluationPresheaf` by the sheafification adjunction.
* `Stacks.SheafOfModules.DualBasisOne` is a rank-one dual basis for `L` over an object `U`: a
  section `e` of `L` over `U` which generates `L|_U`, together with its dual coordinate. This
  is the local data exhibiting `L|_U` as free of rank one.
* `Stacks.SheafOfModules.resSection`, `resRing`, `dualApp` and `dualEval` name the restriction
  maps and the components of a section of the dual with their types pinned down; see the
  implementation notes.

## Main results

* `Stacks.SheafOfModules.evalSection_naturality`: the evaluation values commute with the
  restriction maps. This is the one point where the slice sites interact, and it is what
  makes `evalBilinear` and `evalPresheaf` well defined.
* `Stacks.SheafOfModules.internalHom_map_app_apply`,
  `Stacks.SheafOfModules.internalHom_smul_app_apply` and
  `Stacks.SheafOfModules.internalHom_app_restrict`: the restriction maps, the module structure
  and the slice-site naturality of the internal hom, read off on components. The first two
  hold by `rfl`; they are stated so that consumers need not unfold `homRestr` or `smulHom`.
* `Stacks.SheafOfModules.bijective_evaluationPresheaf_app_of_dualBasisOne`: a rank-one dual
  basis over `U` makes the evaluation pairing bijective on sections over `U`.
* `Stacks.SheafOfModules.DualBasisOne.restrict`: rank-one dual bases restrict along any
  morphism of the site.
* `Stacks.SheafOfModules.isLocallyInjective_evaluationPresheaf` and
  `isLocallySurjective_evaluationPresheaf`: rank-one dual bases on a family of objects
  covering the final object make the pairing locally bijective, and
  `Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf` turns that into an
  isomorphism after sheafification.
* `Stacks.SheafOfModules.isInvertible_of_dualBasisOne`: such an `L` is invertible. This is the
  unconditional direction of Tag 0B8M with the local freeness of rank one presented as the
  dual-basis data; see the implementation notes for what is and is not claimed.

## Implementation notes

**What is reused rather than rebuilt.** The presheaf `internalHom` and the theorem that it is
a sheaf (`internalHom_isSheaf`, Tag 03EM) are already in this library, so nothing here
reconstructs them; the content added is the packaging as a `SheafOfModules` object, the
evaluation pairing, and the rank-one dual-basis criterion for invertibility. In particular the
structure `SheafHom` of Stacks Tag 01CO, which carries the sheaf-hom as
unconstructed data, is *not* used: it fixes the site to the opens of a topological space,
whereas everything here works over an arbitrary site.

**What `isInvertible_of_dualBasisOne` does and does not say.** Its hypothesis is a family of
objects covering the final object together with a rank-one dual basis on each — that is,
local freeness of rank one presented as explicit local data. It is therefore the unconditional
half of Tag 0B8M once a trivialising cover has been converted into dual bases. Deriving that
data from a `SheafOfModules.LocalGeneratorsData` whose generating families are indexed by a
one-element type is *not* done here, so no declaration *in this file* carries `@[stacks 0B8M]`.

The converse half of Tag 0B8M — invertible implies locally free of rank one when the stalks of
the structure sheaf are local rings — is proved:
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`
(`StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Sheaf.lean`) is the converse, and
the resulting equivalence carries the attribute there, as
`Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one`
(`@[stacks 0B8M "characterization for local stalks"]`), with the scheme form
`Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one` beside it. What
remains unproved is only the direction this file is about.

**Universes (forced, and reported).** The module universe is `max u v` for a site
`C : Type u` with `Category.{v} C`, and the ring universe is the same. Neither choice is
made here. `Stacks03EM.internalHom` is not stated at `PresheafOfModules.{max u v}`: its module
universe is a free parameter (`levelParams [v, u, t, u_1]`), so the restriction comes *only*
from `Stacks.SheafOfModules.TensorSheafification` identifying the ring universe with the module
universe (as Mathlib's monoidal structure on presheaves of modules requires). This forces
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}`. If that identification is ever lifted, this file's
universes should be revisited rather than assumed forced. This is a genuine restriction
relative to the `{w}` of the
Stacks Tag 05NA development, and it is recorded here rather than hidden; it costs
nothing for the intended consumers, because on the site of opens of a space `X : TopCat.{u}`
the hom universe is `0` and `max u v = u`, which is exactly the universe those statements
already use.

**Why the terminal object of the slice site.** A section of `internalHom 𝒪 F G` over `U` is a
morphism of presheaves of modules on `C/U`, so to evaluate it on a section of `F` over `U`
one must choose the object of `C/U` lying over `U` itself, namely `Over.mk (𝟙 U)`. On a
preorder site such as the opens of a space this is harmless, because `𝟙 ≫ i = i` holds
definitionally there; over a general site it does not, and `Over.map i` sends `Over.mk (𝟙 V)`
to `Over.mk (𝟙 V ≫ i)` rather than to `Over.mk i`. The naturality proof below therefore goes
through the morphism `Over.homMk i : Over.mk (𝟙 V ≫ i) ⟶ Over.mk (𝟙 U)` of `C/U`, whose
existence needs only `i ≫ 𝟙 = 𝟙 ≫ i`. This is why `evalSection_naturality` is a lemma about
one naturality square rather than a `rfl`.

**Why the operations on sections are named.** A section of `L|_U` over an object `V` of `C/U`,
an element of `L.val.obj (op V.left)`, and the value of a semilinear restriction map all have
the same carrier but carry different `ModuleCat` indices, and
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is
not reducible, so instance search cannot connect the spellings. `resSection`, `resRing`,
`dualApp` and `dualEval` fix one spelling for each operation once and for all; stating the
same facts with inline type ascriptions does not work, because an ascription elaborates to a
`have` which then blocks `rw`.

**No option overrides.** The tagged constructions of these objects, and Tag 03EM itself, use
a global transparency override. Nothing here does: the definitional
facts that option was covering are stated and checked as explicit `rfl` lemmas under the
default transparency.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v u

namespace Stacks.SheafOfModules

section Presheaf

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (F G : PresheafOfModules.{max u v} (Oforget 𝒪))

/-- The restriction map of the internal hom, read off on components: restricting a section
`α` of `internalHom 𝒪 F G` along `i` and taking the component at an object `W` of the slice
site is `α` evaluated at the image of `W` under relocalization. -/
lemma internalHom_map_app_apply {X Y : Cᵒᵖ} (i : X ⟶ Y) (α : (internalHom 𝒪 F G).obj X)
    (W : (Over Y.unop)ᵒᵖ) (x : ((restrFun 𝒪 Y.unop).obj F).obj W) :
    (((ConcreteCategory.hom ((internalHom 𝒪 F G).map i) α).app W).hom x) =
      ((α.app (op ((Over.map i.unop).obj W.unop))).hom x) := rfl

/-- The module structure of the internal hom, read off on components: the action of a section
`a` of `𝒪` over `U` on `α` multiplies the component of `α` at `W` by the restriction of `a`
to `W`. -/
lemma internalHom_smul_app_apply (U : C) (a : (Oforget 𝒪).obj (op U))
    (α : (internalHom 𝒪 F G).obj (op U)) (W : (Over U)ᵒᵖ)
    (x : ((restrFun 𝒪 U).obj F).obj W) :
    ((((a • α : (internalHom 𝒪 F G).obj (op U))).app W).hom x) =
      fRestr 𝒪 U a W • ((α.app W).hom x) := rfl

/-- **The evaluation pairing on sections.** A section of `internalHom 𝒪 F G` over `U` is a
morphism `F|_U ⟶ G|_U` of presheaves of modules on the slice site `C/U`; `evalSection`
applies it to a section of `F` over `U` by taking its component at the terminal object
`Over.mk (𝟙 U)` of `C/U`. -/
noncomputable def evalSection (U : Cᵒᵖ) (α : (internalHom 𝒪 F G).obj U) (x : F.obj U) : G.obj U :=
  (α.app (op (Over.mk (𝟙 U.unop)))).hom x

lemma evalSection_add_left (U : Cᵒᵖ) (α β : (internalHom 𝒪 F G).obj U) (x : F.obj U) :
    evalSection 𝒪 F G U (α + β) x =
      evalSection 𝒪 F G U α x + evalSection 𝒪 F G U β x := rfl

lemma evalSection_add_right (U : Cᵒᵖ) (α : (internalHom 𝒪 F G).obj U) (x y : F.obj U) :
    evalSection 𝒪 F G U α (x + y) =
      evalSection 𝒪 F G U α x + evalSection 𝒪 F G U α y :=
  map_add _ _ _

lemma evalSection_smul_right (U : Cᵒᵖ) (a : (Oforget 𝒪).obj U)
    (α : (internalHom 𝒪 F G).obj U) (x : F.obj U) :
    evalSection 𝒪 F G U α (a • x) = a • evalSection 𝒪 F G U α x :=
  (α.app (op (Over.mk (𝟙 U.unop)))).hom.map_smul a x

lemma evalSection_smul_left (U : Cᵒᵖ) (a : (Oforget 𝒪).obj U)
    (α : (internalHom 𝒪 F G).obj U) (x : F.obj U) :
    evalSection 𝒪 F G U (a • α) x = a • evalSection 𝒪 F G U α x := by
  have h : ((Oforget 𝒪).map (𝟙 U)).hom a = a := by
    rw [CategoryTheory.Functor.map_id]; rfl
  exact congrArg (fun r : (Oforget 𝒪).obj U => r • evalSection 𝒪 F G U α x) h

/-- **The evaluation pairing commutes with the restriction maps.**

This is the only place where the slice sites interact. The two sides differ because
relocalization along `i` sends the terminal object `Over.mk (𝟙 V)` of `C/V` to
`Over.mk (𝟙 V ≫ i)` rather than to `Over.mk i`, so the identification is the naturality
square of `α` along the morphism `Over.homMk i : Over.mk (𝟙 V ≫ i) ⟶ Over.mk (𝟙 U)` of
`C/U`, which exists because `i ≫ 𝟙 = 𝟙 ≫ i`. -/
lemma evalSection_naturality {U V : Cᵒᵖ} (i : U ⟶ V) (α : (internalHom 𝒪 F G).obj U)
    (x : F.obj U) :
    evalSection 𝒪 F G V (ConcreteCategory.hom ((internalHom 𝒪 F G).map i) α)
        ((F.map i).hom x) =
      (G.map i).hom (evalSection 𝒪 F G U α x) :=
  PresheafOfModules.naturality_apply α
    (Over.homMk i.unop (by simp) :
      Over.mk (𝟙 V.unop ≫ i.unop) ⟶ Over.mk (𝟙 U.unop)).op x

/-- The component of a section `α` of the internal hom at an object `V` of the slice site,
applied to a section restricted from `U`, is the restriction of `evalSection 𝒪 F G U α x`.
This is naturality of `α` inside the slice site `C/U`, as opposed to
`evalSection_naturality`, which is naturality in `U`. -/
lemma internalHom_app_restrict (U : C) (α : (internalHom 𝒪 F G).obj (op U))
    (V : (Over U)ᵒᵖ) (x : F.obj (op U)) :
    (α.app V).hom ((F.map V.unop.hom.op).hom x) =
      (G.map V.unop.hom.op).hom (evalSection 𝒪 F G (op U) α x) :=
  PresheafOfModules.naturality_apply α
    (Over.homMk V.unop.hom (Category.comp_id _) :
      V.unop ⟶ Over.mk (𝟙 U)).op x

/-- **The evaluation pairing as a bilinear map of presheaves of modules.** This is the
sectionwise form of the pairing `SheafHom(F, G) ⊗ F ⟶ G`, and it requires no sheaf condition
on `F` or `G`. -/
noncomputable def evalBilinear : Stacks.BilinearMap (internalHom 𝒪 F G) F G where
  app U :=
    AddMonoidHom.mk' (fun α => AddMonoidHom.mk' (fun x => evalSection 𝒪 F G U α x)
        (evalSection_add_right 𝒪 F G U α))
      (fun α β => by ext x; exact evalSection_add_left 𝒪 F G U α β x)
  map_smul_left U a α x := evalSection_smul_left 𝒪 F G U a α x
  map_smul_right U a α x := evalSection_smul_right 𝒪 F G U a α x
  naturality i α x := (evalSection_naturality 𝒪 F G i α x).symm

@[simp]
lemma evalBilinear_app (U : Cᵒᵖ) (α : (internalHom 𝒪 F G).obj U) (x : F.obj U) :
    (evalBilinear 𝒪 F G).app U α x = evalSection 𝒪 F G U α x := rfl

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- **The sheaf-hom of two sheaves of modules.** `SheafHom(F, G)` is the sheaf of
`𝒪`-modules whose sections over `U` are the `𝒪|_U`-linear maps `F|_U ⟶ G|_U`. Its underlying
presheaf is the internal-hom presheaf of Tag 03EM, and the sheaf condition is that tag's
theorem, which needs only that `G` is a sheaf. -/
noncomputable def sheafHom
    (F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) :
    SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) where
  val := internalHom 𝒪 F.val G.val
  isSheaf := internalHom_isSheaf 𝒪 F.val G.val G.isSheaf

@[simp]
lemma sheafHom_val (F G : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (sheafHom 𝒪 h𝒪 F G).val = internalHom 𝒪 F.val G.val := rfl

/-- **The dual of a sheaf of modules**, `F^∨ = SheafHom(F, 𝒪)`: the sheaf-hom into the
structure sheaf. -/
@[stacks 0FNV "dual_sheaf", stacks 0FNY "the dual `SheafHom(ℱ, 𝒪)` whose left-dual property is \
the content of the tag; the construction is for an arbitrary site, so the ringed-space and the \
ringed-site tags name the same object", sga "3 III 0.6"]
noncomputable def dualSheaf
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  sheafHom 𝒪 h𝒪 F (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪))

@[simp]
lemma dualSheaf_val (F : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (dualSheaf 𝒪 h𝒪 F).val =
      internalHom 𝒪 F.val
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val
          := rfl

/-- The sections of the structure sheaf form a commutative ring. Mathlib supplies this for the
spelling `(𝒪 ⋙ forget₂ _ RingCat).obj U`; the `ModuleCat` indices of a
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)` carry the
spelling `(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj U` instead, and
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is not
reducible, so instance search does not connect the two on its own. -/
local instance commRingStructureSheafObj (U : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj U) :=
  (𝒪.obj U).commRing

local instance moduleStructureSheafObj
    (moduleSheaf : SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) (sectionObj : Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj sectionObj)
      (moduleSheaf.val.obj sectionObj) :=
  (moduleSheaf.val.obj sectionObj).isModule

-- The monoidal structure on presheaves of modules over the structure sheaf. It is the
-- monoidal structure over the underlying presheaf of rings, which is literally the same
-- category; `TensorInvertible.lean` builds it and keeps it local, so it is re-enabled here.
attribute [local instance] monoidalCategoryPresheafOfModules

/-- **The evaluation pairing `SheafHom(F, G) ⊗ F ⟶ G`**, as a morphism out of the pointwise
tensor product of presheaves of modules. On sections it is `λ ⊗ f ↦ λ(f)`, where `λ(f)` is
`evalSection`. -/
noncomputable def evalPresheaf
    (F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) :
    (sheafHom 𝒪 h𝒪 F G).val ⊗ F.val ⟶ G.val := by
  letI (U : Cᵒᵖ) : CommRing ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).obj.obj U) :=
    (𝒪.obj U).commRing
  refine PresheafOfModules.Hom.mk (fun U ↦ ?_) ?_
  · exact ModuleCat.MonoidalCategory.tensorLift
      (fun (α : (sheafHom 𝒪 h𝒪 F G).val.obj U) (x : F.val.obj U) ↦
        evalSection 𝒪 F.val G.val U α x)
      (fun α β x => evalSection_add_left 𝒪 F.val G.val U α β x)
      (fun a α x => evalSection_smul_left 𝒪 F.val G.val U a α x)
      (fun α x y => evalSection_add_right 𝒪 F.val G.val U α x y)
      (fun a α x => evalSection_smul_right 𝒪 F.val G.val U a α x)
  · intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro α x
    exact evalSection_naturality 𝒪 F.val G.val i α x

@[simp]
lemma evalPresheaf_tmul
    (F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (U : Cᵒᵖ)
    (α : (sheafHom 𝒪 h𝒪 F G).val.obj U) (x : F.val.obj U) :
    ((evalPresheaf 𝒪 h𝒪 F G).app U).hom
        (α ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] x) =
      evalSection 𝒪 F.val G.val U α x := rfl

/-- **The evaluation pairing of a sheaf of modules with its dual**, `F^∨ ⊗ F ⟶ 𝒪`, as a
morphism of presheaves of modules. This is the pairing consumed by
`Stacks.SheafOfModules.isInvertible_of_pairing`. -/
noncomputable def evaluationPresheaf
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    (dualSheaf 𝒪 h𝒪 F).val ⊗ F.val ⟶
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val :=
  evalPresheaf 𝒪 h𝒪 F (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))

@[simp]
lemma evaluationPresheaf_tmul
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (U : Cᵒᵖ)
    (α : (dualSheaf 𝒪 h𝒪 F).val.obj U) (x : F.val.obj U) :
    ((evaluationPresheaf 𝒪 h𝒪 F).app U).hom
        (α ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] x) =
      evalSection 𝒪 F.val
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val U
          α x := rfl

/-! ### Rank-one dual bases

A *rank-one dual basis* for `L` over an object `U` exhibits `L|_U` as free of rank one: a
section `e` of `L` over `U` together with a dual coordinate `lam`. Such data makes the
evaluation pairing bijective on sections over `U`, which is the local input to invertibility.

The three abbreviations `resSection`, `resRing` and `dualApp` exist to pin down types. A
section of `L|_U` over an object `V` of `C/U`, an element of `L.val.obj (op V.left)`, and the
value of a restriction map all have the same carrier but are spelled with different
`ModuleCat` indices, and `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is not
  reducible, so instance search
cannot connect the spellings on its own. Naming the operations with explicit result types
fixes one spelling once and for all. -/

variable {𝒪 h𝒪} {L : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- The restriction of a section of `L` from `U` to an object `V` of the slice site `C/U`. -/
noncomputable def resSection {U : C} (V : (Over U)ᵒᵖ) (x : L.val.obj (op U)) :
    L.val.obj (op V.unop.left) :=
  (L.val.map V.unop.hom.op).hom x

/-- The restriction of a section of the structure sheaf from `U` to an object `V` of `C/U`. -/
noncomputable def resRing {U : C} (V : (Over U)ᵒᵖ)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left) :=
  ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.map V.unop.hom.op).hom r

/-- The component at `V` of a section of the dual `L^∨` over `U`, applied to a section of `L`
over `V.left`. -/
noncomputable def dualApp {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : L.val.obj (op V.unop.left)) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left) :=
  (lam.app V).hom g

/-- The value of a section of the dual `L^∨` over `U` on a section of `L` over `U`. -/
noncomputable def dualEval {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U))
    (x : L.val.obj (op U)) : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj.obj (op U) :=
  evalSection 𝒪 L.val (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val (op U) lam x

/-- Restricting to the terminal object of `C/U` does nothing. -/
lemma resSection_self {U : C} (x : L.val.obj (op U)) :
    resSection (L := L) (op (Over.mk (𝟙 U))) x = x := by
  have hop : ((𝟙 U).op : op U ⟶ op U) = 𝟙 (op U) := rfl
  show (L.val.map ((𝟙 U).op)).hom x = x
  rw [hop, PresheafOfModules.map_id]
  rfl

/-- At the terminal object of `C/U`, the component of a section of the dual is its value. -/
lemma dualApp_self {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (x : L.val.obj (op U)) :
    dualApp lam (op (Over.mk (𝟙 U))) x = dualEval lam x := rfl

/-- The components of a section of the dual are linear. -/
lemma dualApp_smul {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (c : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left))
    (g : L.val.obj (op V.unop.left)) :
    dualApp lam V (c • g) = c * dualApp lam V g :=
  (lam.app V).hom.map_smul c g

/-- A section of the dual whose components all vanish is zero. -/
lemma eq_zero_of_dualApp {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)), dualApp lam V g = 0) :
    lam = 0 :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun g => h V g)

/-- Evaluating a section of the dual on a restricted section is the restriction of its value:
this is `internalHom_app_restrict` in the pinned-down spellings. -/
lemma dualApp_resSection {U : C} (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : L.val.obj (op U)) :
    dualApp lam V (resSection V x) = resRing V (dualEval lam x) :=
  internalHom_app_restrict 𝒪 L.val
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val U lam
      V x

variable (𝒪 h𝒪)

/-- **A rank-one dual basis for `L` over an object `U` of the site.**

`e` is a section of `L` over `U` and `lam` a section of the dual `L^∨` over `U`; `span` says
that `e` generates `L|_U` with `lam` as the coordinate, and `eval_self` says that `lam` is
dual to `e`. Together they say exactly that `e` is a basis of the free rank-one module
`L|_U`. -/
structure DualBasisOne (L : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (U : C) where
  /-- The basis section of `L` over `U`. -/
  e : L.val.obj (op U)
  /-- The dual coordinate, a section of `L^∨` over `U`. -/
  lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)
  /-- `e` generates: every section of `L` over an object `V` of `C/U` is its own coordinate
  times the restriction of `e`. -/
  span (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp lam V g • resSection V e = g
  /-- `lam` is dual to `e`. -/
  eval_self : dualEval lam e = 1

namespace DualBasisOne

variable {𝒪 h𝒪} {U : C}

/-- `span` read off at the terminal object of `C/U`: a section of `L` over `U` is its own
coordinate times `e`. -/
lemma coord_smul (b : DualBasisOne 𝒪 h𝒪 L U) (g : L.val.obj (op U)) :
    dualEval b.lam g • b.e = g := by
  have h := b.span (op (Over.mk (𝟙 U))) g
  rw [resSection_self, dualApp_self] at h
  exact h

/-- A section of `L^∨` over `U` which kills `e` is zero: `e` generates `L|_U`, so a section of
the dual is determined by its value on `e`. -/
lemma eq_zero_of_eval_e (b : DualBasisOne 𝒪 h𝒪 L U)
    (μ : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (hμ : dualEval μ b.e = 0) : μ = 0 := by
  refine eq_zero_of_dualApp μ fun V g => ?_
  rw [← b.span V g, dualApp_smul, dualApp_resSection, hμ]
  show _ * ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.map
    V.unop.hom.op).hom 0 = 0
  rw [map_zero, mul_zero]

end DualBasisOne

/-- **A rank-one dual basis makes the evaluation pairing bijective on sections.**

Surjectivity pairs `r • lam` with `e`, which evaluates to `r` by `eval_self`. Injectivity is a
normal form: since `e` generates, every element of `L^∨(U) ⊗_{𝒪(U)} L(U)` has the shape
`μ ⊗ e`, and such an element is killed by the pairing only when `μ` kills `e`, hence only
when `μ = 0`. -/
theorem bijective_evaluationPresheaf_app_of_dualBasisOne {U : C}
    (b : DualBasisOne 𝒪 h𝒪 L U) :
    Function.Bijective ((evaluationPresheaf 𝒪 h𝒪 L).app (op U)).hom := by
  classical
  -- The pairing on sections over `U`, in the pinned-down spelling.
  have hpair : ∀ (μ : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (x : L.val.obj (op U)),
      ((evaluationPresheaf 𝒪 h𝒪 L).app (op U)).hom
        (μ ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] x) =
          dualEval μ x :=
    fun _ _ => rfl
  -- Since `e` generates, every element of the tensor product is `μ ⊗ e`.
  have hnormal : ∀ t : ((dualSheaf 𝒪 h𝒪 L).val ⊗ L.val).obj (op U),
      ∃ μ : (dualSheaf 𝒪 h𝒪 L).val.obj (op U),
        t = μ ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)]
          b.e := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
    | tmul μ g =>
      refine ⟨dualEval b.lam g • μ, ?_⟩
      simp only [TensorProduct.smul_tmul, b.coord_smul g]
      rfl
    | add t s ht hs =>
      obtain ⟨μ, hμ⟩ := ht
      obtain ⟨ν, hν⟩ := hs
      refine ⟨μ + ν, ?_⟩
      simp only [hμ, hν, TensorProduct.add_tmul]
      rfl
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨μ, hμ⟩ := hnormal t
    rw [hμ] at ht ⊢
    rw [hpair] at ht
    simp only [b.eq_zero_of_eval_e μ ht, TensorProduct.zero_tmul]
    rfl
  · -- Restate surjectivity with the scalar in the ring spelling, then pair `r • lam` with `e`.
    have key : ∀ r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
      U),
        ∃ t, ((evaluationPresheaf 𝒪 h𝒪 L).app (op U)).hom t = r := by
      intro r
      refine ⟨(r • b.lam) ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪).obj.obj (op U)] b.e, ?_⟩
      have h3 : dualEval (r • b.lam) b.e = r * dualEval b.lam b.e :=
        evalSection_smul_left 𝒪 L.val
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val
            (op U) r b.lam b.e
      show dualEval (r • b.lam) b.e = r
      exact h3.trans ((congrArg
        (fun coefficient :
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U) =>
            r * coefficient) b.eval_self).trans (mul_one r))
    exact fun r => key r

/-- Restricting a section twice is restricting along the relocalized object. -/
lemma resSection_map {U W : C} (k : W ⟶ U) (V : (Over W)ᵒᵖ) (x : L.val.obj (op U)) :
    resSection V ((L.val.map k.op).hom x) = resSection (op ((Over.map k).obj V.unop)) x := by
  show (L.val.map V.unop.hom.op).hom ((L.val.map k.op).hom x)
    = (L.val.map (k.op ≫ V.unop.hom.op)).hom x
  rw [PresheafOfModules.map_comp_apply]

/-- The components of a restricted section of the dual are the components of the original at
the relocalized objects. -/
lemma dualApp_map {U W : C} (k : W ⟶ U) (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U))
    (V : (Over W)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp (((dualSheaf 𝒪 h𝒪 L).val.map k.op).hom lam) V g
      = dualApp lam (op ((Over.map k).obj V.unop)) g := rfl

namespace DualBasisOne

variable {𝒪 h𝒪}

/-- **A rank-one dual basis restricts along any morphism of the site.** Being free of rank one
is stable under restriction, which is what lets a dual basis on a covering family be used over
every object admitting a morphism into a member of that family. -/
noncomputable def restrict {U : C} (b : DualBasisOne 𝒪 h𝒪 L U) {W : C} (k : W ⟶ U) :
    DualBasisOne 𝒪 h𝒪 L W where
  e := (L.val.map k.op).hom b.e
  lam := ((dualSheaf 𝒪 h𝒪 L).val.map k.op).hom b.lam
  span V g := by
    rw [dualApp_map, resSection_map]
    exact b.span (op ((Over.map k).obj V.unop)) g
  eval_self := by
    have h : dualEval (((dualSheaf 𝒪 h𝒪 L).val.map k.op).hom b.lam)
          ((L.val.map k.op).hom b.e)
        = ((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪)).val.map k.op).hom
            (dualEval b.lam b.e) :=
      evalSection_naturality 𝒪 L.val
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val
          k.op b.lam b.e
    rw [h, b.eval_self]
    change (𝒪.map k.op).hom 1 = 1
    exact (𝒪.map k.op).hom.map_one

end DualBasisOne

/-! ### Local bijectivity of the evaluation pairing

If `L` carries a rank-one dual basis over each member of a family of objects covering the
final object, the pairing is bijective on sections over every object admitting a morphism into
a member of that family, and the sieve of such morphisms is covering. -/

/-- The evaluation pairing is locally injective when `L` has rank-one dual bases on a family
covering the final object. -/
theorem isLocallyInjective_evaluationPresheaf {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, DualBasisOne 𝒪 h𝒪 L (X i)) :
    PresheafOfModules.IsLocallyInjective J (evaluationPresheaf 𝒪 h𝒪 L) := by
  constructor
  intro Z x y h
  refine J.superset_covering ?_ (hX Z.unop)
  rintro W p ⟨i, ⟨q⟩⟩
  have hbij := bijective_evaluationPresheaf_app_of_dualBasisOne 𝒪 h𝒪 ((b i).restrict q)
  have hn : ∀ t : ((dualSheaf 𝒪 h𝒪 L).val ⊗ L.val).obj Z,
      ((evaluationPresheaf 𝒪 h𝒪 L).app (op W)).hom
          ((((dualSheaf 𝒪 h𝒪 L).val ⊗ L.val).map p.op).hom t)
        = ((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪)).val.map p.op).hom
            (((evaluationPresheaf 𝒪 h𝒪 L).app Z).hom t) :=
    fun t => PresheafOfModules.naturality_apply (evaluationPresheaf 𝒪 h𝒪 L) p.op t
  apply hbij.injective
  show ((evaluationPresheaf 𝒪 h𝒪 L).app (op W)).hom
      ((((dualSheaf 𝒪 h𝒪 L).val ⊗ L.val).map p.op).hom x)
    = ((evaluationPresheaf 𝒪 h𝒪 L).app (op W)).hom
      ((((dualSheaf 𝒪 h𝒪 L).val ⊗ L.val).map p.op).hom y)
  rw [hn x, hn y]
  exact congrArg
    (fun z => (((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)).val.map p.op).hom z)) h

/-- The evaluation pairing is locally surjective when `L` has rank-one dual bases on a family
covering the final object. -/
theorem isLocallySurjective_evaluationPresheaf {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, DualBasisOne 𝒪 h𝒪 L (X i)) :
    PresheafOfModules.IsLocallySurjective J (evaluationPresheaf 𝒪 h𝒪 L) := by
  constructor
  intro Z s
  refine J.superset_covering ?_ (hX Z)
  rintro W p ⟨i, ⟨q⟩⟩
  exact (bijective_evaluationPresheaf_app_of_dualBasisOne 𝒪 h𝒪
    ((b i).restrict q)).surjective _

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-! ### Invertibility

A sheaf of modules with rank-one dual bases on a covering family is invertible: the evaluation
pairing with its dual is locally bijective, hence inverted by sheafification, which is exactly
the hypothesis of `Stacks.SheafOfModules.isInvertible_of_pairing` (Tag 0B8K). -/

/-- **Sheafification inverts the evaluation pairing** of `L` with its dual, when `L` has
rank-one dual bases on a family covering the final object. -/
theorem isIso_sheafify_map_evaluationPresheaf {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, DualBasisOne 𝒪 h𝒪 L (X i)) :
    IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map (evaluationPresheaf 𝒪 h𝒪
      L)) := by
  have hI := isLocallyInjective_evaluationPresheaf 𝒪 h𝒪 hX b
  have hS := isLocallySurjective_evaluationPresheaf 𝒪 h𝒪 hX b
  let := hI
  let := hS
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{max u v}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj).map
      (evaluationPresheaf 𝒪 h𝒪 L)))

/-- **A sheaf of modules with rank-one dual bases on a covering family is invertible.**

This is the unconditional direction of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) in the form in which the hypothesis
is the local data: the dual `L^∨` and its evaluation pairing are supplied by this file, the pairing
is locally bijective by `isLocallyInjective_evaluationPresheaf` and
`isLocallySurjective_evaluationPresheaf`, and `isInvertible_of_pairing` (Tag 0B8K) converts that
into invertibility. The opposite pairing is the same one composed with the braiding of presheaves
of modules. -/
theorem isInvertible_of_dualBasisOne {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, DualBasisOne 𝒪 h𝒪 L (X i)) : IsInvertible 𝒪 h𝒪 L := by
  have hev : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map
    (evaluationPresheaf 𝒪 h𝒪 L)) :=
    isIso_sheafify_map_evaluationPresheaf 𝒪 h𝒪 hX b
  have hbr : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map
      (braidingVal 𝒪 h𝒪 L (dualSheaf 𝒪 h𝒪 L)).inv) := inferInstance
  exact isInvertible_of_pairing L (dualSheaf 𝒪 h𝒪 L) (evaluationPresheaf 𝒪 h𝒪 L)
    ((braidingVal 𝒪 h𝒪 L (dualSheaf 𝒪 h𝒪 L)).inv ≫ evaluationPresheaf 𝒪 h𝒪 L) hev
    (isIso_sheafify_map_comp 𝒪 h𝒪 _ _ hbr hev)

section TensorSheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- **The evaluation pairing of sheaves of modules**, `F^∨ ⊗_𝒪 F ⟶ 𝒪`. The tensor product of
sheaves of modules is the sheafification of the pointwise one (Tag 05NA), so this is the
morphism which `evaluationPresheaf` induces through the sheafification adjunction. -/
@[stacks 0FNV "evaluation", stacks 0FNY "the evaluation map `ε : ℱ^∨ ⊗ ℱ ⟶ 𝒪`"]
noncomputable def evaluation
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
        (forget₂ CommRingCat RingCat) h𝒪⟩).obj (dualSheaf 𝒪 h𝒪 F)).obj F ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
    ((PresheafOfModules.tensorObj (O := 𝒪) ((dualSheaf 𝒪 h𝒪 F).val) (F.val)))
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))).symm
      (evaluationPresheaf 𝒪 h𝒪 F)

end TensorSheaf

end Sheafification

end Sheaf

end Stacks.SheafOfModules

end
