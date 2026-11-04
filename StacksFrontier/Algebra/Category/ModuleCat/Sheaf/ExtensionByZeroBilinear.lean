module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bilinear maps out of an extension by zero

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it and let `U : C`. The
extension by zero `j_{U!}` of sheaves of modules from the slice site at `U` is a left adjoint of
restriction `j_U^*`, so a *linear* map `j_{U!}P ⟶ F` is the same thing as a linear map
`P ⟶ F|_U`. The adjunction says nothing about *bilinear* maps, and a bilinear map
`j_{U!}P × F ⟶ G` is exactly what is needed to give an extension by zero the action of a sheaf
of graded algebras.

This file supplies the missing engine. The internal Hom of Tag 03EM turns a bilinear map into a
linear one: a bilinear map `P × F ⟶ G` is a linear map `P ⟶ 𝓗om_O(F, G)`, so the adjunction
applies to the curried form and transports it back. The resulting `extendBilinear` builds a
bilinear map out of `j_{U!}P`, `extendBilinear_unit` computes it on the local sections supplied
by the adjunction unit, and `extendedBilinear_ext` says that those values determine it. The same
three steps are then carried out one variable further up, for trilinear maps, which is what an
associativity law for such an action needs.

## Main definitions

* `SheafOfModules.TrilinearMap` is a trilinear map of sheaves of modules, presented on sections,
  and `SheafOfModules.trilinearCompLeft`, `SheafOfModules.trilinearCompRight` are the two ways
  of composing two bilinear maps into a trilinear one.
* `SheafOfModules.bilinearPostcomp` composes a bilinear map with a morphism out of its target
  and `SheafOfModules.bilinearApplySection` evaluates one at a global section of its second
  variable.
* `SheafOfModules.moduleHomSheaf` is the internal Hom `𝓗om_O(F, G)` as a sheaf of modules: the
  internal Hom presheaf of Tag 03EM, which that tag proves is a sheaf as soon as `G` is.
  `SheafOfModules.homSheafApp` reads off the component of one of its sections at an object of a
  slice site, and `SheafOfModules.homSheafEval` evaluates a section of it on a section of `F`.
* `SheafOfModules.bilinearCurry` and `SheafOfModules.bilinearUncurry` are the two directions of
  the identification of bilinear maps `P × F ⟶ G` with linear maps `P ⟶ 𝓗om_O(F, G)`, built out
  of `SheafOfModules.bilinearCurryHom`; `SheafOfModules.trilinearCurry` curries the last
  variable of a trilinear map, through `SheafOfModules.trilinearCurryHom`.
* `SheafOfModules.bilinearCurryOver` is the currying of a bilinear map of restricted sheaves of
  modules, landing in the restriction of `𝓗om_O(F, G)` to the slice site, and
  `SheafOfModules.overSliceHom` names the morphism of the slice site its components are
  restricted along.
* `SheafOfModules.extendBilinear` is the engine: a bilinear map `P × F|_U ⟶ G|_U` on the slice
  site extends to a bilinear map `j_{U!}P × F ⟶ G`.

## Main results

* `SheafOfModules.homSheafExt`: a section of `𝓗om_O(F, G)` is determined by its components.
* `SheafOfModules.bilinearUncurry_curry_app`: uncurrying undoes currying, on sections.
* `SheafOfModules.overBilinear_map_congr`: a bilinear map on the slice site does not see a
  rewriting of the structure morphism of the object a section is restricted to.
* `SheafOfModules.extendBilinear_unit`: the extended bilinear map agrees with the given one on
  the local sections provided by the unit of the adjunction.
* `SheafOfModules.extendedBilinear_ext`: two bilinear maps out of `j_{U!}P` which agree on the
  local sections provided by the unit are equal. This is the recognition principle the
  adjunction does not give.
* `SheafOfModules.extendedHom_hext` and `SheafOfModules.extendedTrilinear_hext`: the
  heterogeneous forms of the same principle, for a linear map out of `j_{U!}P` whose target is
  only known up to an equality of sheaves of modules, and for a trilinear map. These are the
  shapes in which the laws of a graded action over an extension by zero are stated, the degrees
  on the two sides of such a law agreeing only after rewriting an index.

## Implementation notes

The ambient setting is unbundled, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InternalHomVariance.lean`: a site `C : Type u`
with `Category.{v} C`, a sheaf of commutative rings `O` with sections in `Type w`, and sheaves
of modules over `Stacks.SheafOfModules.Tensor.ringSheaf O`, the structure sheaf with commutativity
forgotten. The
module universe is `max u v m` for an independent `m`. It cannot be left free: the extension by
zero assembles a section of `j_{U!}P` over `V` out of the morphisms `V ⟶ U` of the site, which
forces `max u v` into it. The ring universe `w` stays out of it, the internal Hom of Tag 03EM
leaving its module universe free.

Because `m` occurs in those statements only inside `max u v m`, it cannot be recovered by
unification from the type of an argument. Every declaration below that is stated at that module
universe therefore has to be *applied* with its universe arguments written out, in the order
`.{m, w, v, u}`; this is done throughout the file and consumers must do the same. The
declarations that need no internal Hom and no extension — `TrilinearMap` with its composition
constructions, `bilinearPostcomp` and `bilinearApplySection` — are stated instead over an
arbitrary sheaf of rings at a free module universe, where no such instantiation is needed.

Restriction to the slice site is Mathlib's `SheafOfModules.overFunctor`, whose value on `M` is
written `M.over U`. The sections of `M.over U` over `V : (Over U)ᵒᵖ` *are* the sections of `M`
over `op V.unop.left`, definitionally, and likewise for the scalars; the proofs below rely on
exactly that, and no `eqToHom` and no restriction of scalars is needed anywhere.

**Why the proofs are in term mode.** The restriction map of a presheaf of modules has type
`M.obj X ⟶ (ModuleCat.restrictScalars _).obj (M.obj Y)`, so `M.map f x` is a section of `M`
over `Y` only after `ModuleCat.restrictScalars` is unfolded, and sections over the slice site
are sections over the base only after `restrFun` is unfolded. Both are semireducible, so a goal
mentioning either is *not* type-correct at the reduced transparency at which `rw` re-checks its
motive, and rewriting in such a goal fails however true the equation is. Two devices avoid this
throughout, and no relaxation of the elaborator's transparency is needed. First, restriction of
a section is written `M.restrictₛₗ f x`, Mathlib's semilinear-map form, whose codomain is
`M.obj Y` on the nose; `PresheafOfModules.restrictₛₗ_id_apply`,
`restrictₛₗ_comp_apply` and `restrictₛₗ_naturality_apply` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationTensor.lean` are used in that
spelling, and the three `Stacks.BilinearMap` lemmas opening the file restate the bilinearity
clauses the same way. Second, the
crossings of the slice/base boundary are packaged once and for all as `homSheafApp` and
`homSheafEval`, which are definitions and therefore type-correct applications wherever they
occur. What remains is assembled with `Eq.trans` and the congruence lemmas rather than
with `rw`.

Bilinear maps are `SheafOfModules.BilinearMap`, that is, `Stacks.BilinearMap` on the underlying
presheaves of modules: bilinearity constrains only sections and restriction maps, so the sheaf
conditions play no part. Trilinear maps are written out as their own structure for the same
reason: the library has no tensor product of sheaves of modules to curry through, and a
sectionwise presentation is what the proofs consume. Restriction of a bilinear map in its first
variable is `Stacks.BilinearMap.compLeft` and in its second `Stacks.BilinearMap.compRight`;
neither is repeated here.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0FRA](https://stacks.math.columbia.edu/tag/0FRA)
-/

@[expose] public section

open CategoryTheory Opposite

universe t m w v u

namespace PresheafOfModules

variable {D : Type u} [Category.{v} D] {S : Dᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{t} S)

/-- Restriction of a section along equal morphisms agrees. -/
lemma restrictₛₗ_congr {X Y : Dᵒᵖ} {i j : X ⟶ Y} (h : i = j) (x : M.obj X) :
    M.restrictₛₗ i x = M.restrictₛₗ j x := by rw [h]

end PresheafOfModules

namespace Stacks.BilinearMap

variable {D : Type u} [Category.{v} D] {S : Dᵒᵖ ⥤ RingCat.{w}}
  {M N P : PresheafOfModules.{t} S}

/-- A bilinear map applied to equal sections in its first variable gives equal values. -/
lemma congr_left (β : BilinearMap M N P) (X : Dᵒᵖ) {x x' : M.obj X} (h : x = x')
    (y : N.obj X) : β.app X x y = β.app X x' y := by rw [h]

/-- A bilinear map applied to equal sections in its second variable gives equal values. -/
lemma congr_right (β : BilinearMap M N P) (X : Dᵒᵖ) (x : M.obj X) {y y' : N.obj X}
    (h : y = y') : β.app X x y = β.app X x y' := by rw [h]

/-- Compatibility of a bilinear map with the restriction maps, in the `restrictₛₗ` spelling. -/
lemma naturality_restrictₛₗ (β : BilinearMap M N P) {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : M.obj X)
    (y : N.obj X) :
    P.restrictₛₗ f (β.app X x y) = β.app Y (M.restrictₛₗ f x) (N.restrictₛₗ f y) :=
  β.naturality f x y

end Stacks.BilinearMap

namespace SheafOfModules

/-! ### Trilinear maps, and composing and evaluating bilinear maps

Everything in this section is stated over an arbitrary sheaf of rings on an arbitrary site, at
a free module universe; no internal Hom and no extension by zero occurs. -/

section Generic

variable {D : Type u} [Category.{v} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{w}}
  {P F G H Q : SheafOfModules.{t} R}

/-- An `R`-trilinear map of sheaves of modules, presented on sections: a family of triadditive
maps on sections over the objects of the site, linear in each of the three variables and
compatible with the restriction maps. This is the sectionwise form of a morphism out of a
triple tensor product, which the library does not have. -/
structure TrilinearMap (P F G H : SheafOfModules.{t} R) where
  /-- The triadditive map on sections over an object of the site. -/
  app (V : Dᵒᵖ) : P.val.obj V →+ F.val.obj V →+ G.val.obj V →+ H.val.obj V
  /-- Linearity in the first variable. -/
  smul₁ (V : Dᵒᵖ) (r : R.obj.obj V) (x : P.val.obj V) (y : F.val.obj V) (z : G.val.obj V) :
    app V (r • x) y z = r • app V x y z
  /-- Linearity in the second variable. -/
  smul₂ (V : Dᵒᵖ) (r : R.obj.obj V) (x : P.val.obj V) (y : F.val.obj V) (z : G.val.obj V) :
    app V x (r • y) z = r • app V x y z
  /-- Linearity in the third variable. -/
  smul₃ (V : Dᵒᵖ) (r : R.obj.obj V) (x : P.val.obj V) (y : F.val.obj V) (z : G.val.obj V) :
    app V x y (r • z) = r • app V x y z
  /-- Compatibility with the restriction maps. -/
  naturality {V W : Dᵒᵖ} (f : V ⟶ W) (x : P.val.obj V) (y : F.val.obj V) (z : G.val.obj V) :
    H.val.map f (app V x y z) = app W (P.val.map f x) (F.val.map f y) (G.val.map f z)

namespace TrilinearMap

variable (b : TrilinearMap P F G H)

/-- A trilinear map applied to equal sections in its first variable gives equal values. -/
lemma congr₁ (V : Dᵒᵖ) {x x' : P.val.obj V} (h : x = x') (y : F.val.obj V)
    (z : G.val.obj V) : b.app V x y z = b.app V x' y z := by rw [h]

/-- A trilinear map applied to equal sections in its second variable gives equal values. -/
lemma congr₂ (V : Dᵒᵖ) (x : P.val.obj V) {y y' : F.val.obj V} (h : y = y')
    (z : G.val.obj V) : b.app V x y z = b.app V x y' z := by rw [h]

/-- Additivity in the first variable. -/
lemma add₁ (V : Dᵒᵖ) (x x' : P.val.obj V) (y : F.val.obj V) (z : G.val.obj V) :
    b.app V (x + x') y z = b.app V x y z + b.app V x' y z := by rw [map_add]; rfl

/-- Additivity in the second variable. -/
lemma add₂ (V : Dᵒᵖ) (x : P.val.obj V) (y y' : F.val.obj V) (z : G.val.obj V) :
    b.app V x (y + y') z = b.app V x y z + b.app V x y' z := by rw [map_add]; rfl

/-- Compatibility of a trilinear map with the restriction maps, in the `restrictₛₗ`
spelling. -/
lemma naturality_restrictₛₗ {V W : Dᵒᵖ} (f : V ⟶ W) (x : P.val.obj V) (y : F.val.obj V)
    (z : G.val.obj V) :
    H.val.restrictₛₗ f (b.app V x y z) =
      b.app W (P.val.restrictₛₗ f x) (F.val.restrictₛₗ f y) (G.val.restrictₛₗ f z) :=
  b.naturality f x y z

end TrilinearMap

/-- **Postcomposition of a bilinear map with a morphism out of its target.** The two
restrictions of a bilinear map along morphisms in its variables are
`Stacks.BilinearMap.compLeft` and `Stacks.BilinearMap.compRight`; this is the remaining
composition. -/
noncomputable def bilinearPostcomp (b : BilinearMap P F G) (f : G ⟶ H) : BilinearMap P F H where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => (f.val.app V).hom (b.app V x y))
      (fun y y' => (congrArg (f.val.app V).hom (map_add (b.app V x) y y')).trans
        (map_add (f.val.app V).hom _ _)))
    (fun x x' => AddMonoidHom.ext fun y =>
      (congrArg (f.val.app V).hom (b.map_add_left V x x' y)).trans
        (map_add (f.val.app V).hom _ _))
  map_smul_left V r x y :=
    (congrArg (f.val.app V).hom (b.map_smul_left V r x y)).trans
      ((f.val.app V).hom.map_smul r (b.app V x y))
  map_smul_right V r x y :=
    (congrArg (f.val.app V).hom (b.map_smul_right V r x y)).trans
      ((f.val.app V).hom.map_smul r (b.app V x y))
  naturality {V W} g x y :=
    (PresheafOfModules.restrictₛₗ_naturality_apply f.val g (b.app V x y)).symm.trans
      (congrArg (f.val.app W).hom (b.naturality_restrictₛₗ g x y))

/-- **Evaluating a bilinear map at a global section of its second variable.** The result is a
morphism of sheaves of modules out of the first variable. -/
noncomputable def bilinearApplySection (b : BilinearMap P F G) (s : F.sections) : P ⟶ G where
  val :=
    { app V := ModuleCat.ofHom
        { toFun x := b.app V x (s.eval V)
          map_add' x x' := b.map_add_left V x x' (s.eval V)
          map_smul' r x := b.map_smul_left V r x (s.eval V) }
      naturality {V W} g := ModuleCat.hom_ext (LinearMap.ext fun x =>
        (b.congr_right W (P.val.restrictₛₗ g x) (s.property g).symm).trans
          (b.naturality_restrictₛₗ g x (s.eval V)).symm) }

/-- **Composing two bilinear maps in the first variable of the second.** Pairing with the result
of a bilinear map is trilinear. -/
noncomputable def trilinearCompLeft (b : BilinearMap P F Q) (c : BilinearMap Q G H) :
    TrilinearMap P F G H where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => AddMonoidHom.mk' (fun z => c.app V (b.app V x y) z)
        (fun z z' => map_add (c.app V (b.app V x y)) z z'))
      (fun y y' => AddMonoidHom.ext fun z =>
        (c.congr_left V (map_add (b.app V x) y y') z).trans (c.map_add_left V _ _ z)))
    (fun x x' => AddMonoidHom.ext fun y => AddMonoidHom.ext fun z =>
      (c.congr_left V (b.map_add_left V x x' y) z).trans (c.map_add_left V _ _ z))
  smul₁ V r x y z :=
    (c.congr_left V (b.map_smul_left V r x y) z).trans (c.map_smul_left V r (b.app V x y) z)
  smul₂ V r x y z :=
    (c.congr_left V (b.map_smul_right V r x y) z).trans (c.map_smul_left V r (b.app V x y) z)
  smul₃ V r x y z := c.map_smul_right V r (b.app V x y) z
  naturality {V W} f x y z :=
    (c.naturality_restrictₛₗ f (b.app V x y) z).trans
      (c.congr_left W (b.naturality_restrictₛₗ f x y) (G.val.restrictₛₗ f z))

/-- **Composing two bilinear maps in the second variable of the first.** Pairing a section with
the result of a bilinear map is trilinear. -/
noncomputable def trilinearCompRight (b : BilinearMap P Q H) (c : BilinearMap F G Q) :
    TrilinearMap P F G H where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => AddMonoidHom.mk' (fun z => b.app V x (c.app V y z))
        (fun z z' => (b.congr_right V x (map_add (c.app V y) z z')).trans
          (map_add (b.app V x) _ _)))
      (fun y y' => AddMonoidHom.ext fun z =>
        (b.congr_right V x (c.map_add_left V y y' z)).trans (map_add (b.app V x) _ _)))
    (fun x x' => AddMonoidHom.ext fun y => AddMonoidHom.ext fun z =>
      b.map_add_left V x x' (c.app V y z))
  smul₁ V r x y z := b.map_smul_left V r x (c.app V y z)
  smul₂ V r x y z :=
    (b.congr_right V x (c.map_smul_left V r y z)).trans (b.map_smul_right V r x (c.app V y z))
  smul₃ V r x y z :=
    (b.congr_right V x (c.map_smul_right V r y z)).trans (b.map_smul_right V r x (c.app V y z))
  naturality {V W} f x y z :=
    (b.naturality_restrictₛₗ f x (c.app V y z)).trans
      (b.congr_right W (P.val.restrictₛₗ f x) (c.naturality_restrictₛₗ f y z))

end Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O : Sheaf J CommRingCat.{w})

/-- **The internal Hom `𝓗om_O(F, G)` as a sheaf of modules.** Its sections over `V` are the
`O|_V`-linear maps `F|_V ⟶ G|_V`. The underlying presheaf of modules is the internal Hom
presheaf of Tag 03EM, and the sheaf condition is that tag's theorem, which needs only that `G`
is a sheaf. -/
@[sga "3 I 3.1.4" "special case", sga "4 IV 12.5"]
noncomputable def moduleHomSheaf
    (F G : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) where
  val := internalHom O.obj F.val G.val
  isSheaf := internalHom_isSheaf O.obj F.val G.val G.isSheaf

/-! ### Sections of the internal Hom

A section of `𝓗om_O(F, G)` over `V` is a morphism of presheaves of modules on the slice site
`C/V`. Its component at an object `W` of that site is a map on sections of `F` over `W.left`;
`homSheafApp` is that map and `homSheafEval` is its value at the terminal object of `C/V`, where
it becomes a map on sections over `V` itself. Both are definitions rather than abbreviations:
their whole purpose is to cross the boundary between a section over the slice site and a
section over the base once, in a term which is type-correct however little is unfolded. -/

section InternalHom

variable (F G : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- **The component of a section of `𝓗om_O(F, G)` at an object of a slice site.** A section `α`
over `V` is a morphism `F|_V ⟶ G|_V` on `C/V`; this is its component at `W : C/V`, as a map
from sections of `F` over `W.left` to sections of `G` over `W.left`. -/
noncomputable def homSheafApp (V : Cᵒᵖ) (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (y : F.val.obj (op W.unop.left)) : G.val.obj (op W.unop.left) :=
  ((α : (restrFun O.obj V.unop).obj F.val ⟶ (restrFun O.obj V.unop).obj G.val).app W).hom y

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A section of `𝓗om_O(F, G)` is determined by its components.** This is extensionality for
a morphism of presheaves of modules on the slice site, read through `homSheafApp`. -/
lemma homSheafExt (V : Cᵒᵖ) {α β : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V}
    (h : ∀ (W : (Over V.unop)ᵒᵖ) (y : F.val.obj (op W.unop.left)),
      homSheafApp.{m, w, v, u} O F G V α W y = homSheafApp.{m, w, v, u} O F G V β W y) :
    α = β :=
  PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => h W y)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of a sum of sections of `𝓗om_O(F, G)` are the sums of their components. -/
lemma homSheafApp_add_left (V : Cᵒᵖ) (α β : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (y : F.val.obj (op W.unop.left)) :
    homSheafApp.{m, w, v, u} O F G V (α + β) W y =
      homSheafApp.{m, w, v, u} O F G V α W y + homSheafApp.{m, w, v, u} O F G V β W y := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of a scalar multiple of a section of `𝓗om_O(F, G)` over `V`: the component
at `W` is multiplied by the restriction of the scalar to `W.left`. -/
lemma homSheafApp_smul_left (V : Cᵒᵖ)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.obj V)
    (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V) (W : (Over V.unop)ᵒᵖ)
    (y : F.val.obj (op W.unop.left)) :
    homSheafApp.{m, w, v, u} O F G V (r • α) W y =
      (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.map W.unop.hom.op).hom r •
        homSheafApp.{m, w, v, u} O F G V α W y := rfl

/-- **Evaluating a section of `𝓗om_O(F, G)` over `V` on a section of `F` over `V`.** It is the
component at the terminal object `𝟙_V` of the slice site `C/V`. -/
noncomputable def homSheafEval (V : Cᵒᵖ) (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V)
    (y : F.val.obj V) : G.val.obj V :=
  homSheafApp.{m, w, v, u} O F G V α (op (Over.mk (𝟙 V.unop))) y

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluation is additive in the section of the internal Hom. -/
lemma homSheafEval_add_left (V : Cᵒᵖ) (α β : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V)
    (y : F.val.obj V) :
    homSheafEval.{m, w, v, u} O F G V (α + β) y =
      homSheafEval.{m, w, v, u} O F G V α y + homSheafEval.{m, w, v, u} O F G V β y := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluation is additive in the section of `F`. -/
lemma homSheafEval_add_right (V : Cᵒᵖ) (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V)
    (y y' : F.val.obj V) :
    homSheafEval.{m, w, v, u} O F G V α (y + y') =
      homSheafEval.{m, w, v, u} O F G V α y + homSheafEval.{m, w, v, u} O F G V α y' :=
  map_add _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluation is linear in the section of `F`. -/
lemma homSheafEval_smul_right (V : Cᵒᵖ)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.obj V)
    (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V) (y : F.val.obj V) :
    homSheafEval.{m, w, v, u} O F G V α (r • y) = r • homSheafEval.{m, w, v, u} O F G V α y :=
  ((α : (restrFun O.obj V.unop).obj F.val ⟶ (restrFun O.obj V.unop).obj G.val).app
    (op (Over.mk (𝟙 V.unop)))).hom.map_smul r y

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluation is linear in the section of the internal Hom. The scalar is restricted along the
identity of `V`, which is why this is not the `rfl` that `homSheafApp_smul_left` is. -/
lemma homSheafEval_smul_left (V : Cᵒᵖ)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.obj V)
    (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V) (y : F.val.obj V) :
    homSheafEval.{m, w, v, u} O F G V (r • α) y = r • homSheafEval.{m, w, v, u} O F G V α y := by
  have h : (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.map (𝟙 V)).hom r = r := by
    rw [CategoryTheory.Functor.map_id]; rfl
  exact congrArg (fun s : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.obj V =>
    s • homSheafEval.{m, w, v, u} O F G V α y) h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Evaluation commutes with the restriction maps.** This is the one point where the slice
sites interact: relocalization along `i` sends the terminal object of `C/W` to `𝟙_W ≫ i` rather
than to `i`, so the identification is the naturality square of `α` along the morphism
`Over.homMk i : Over.mk (𝟙_W ≫ i) ⟶ 𝟙_V` of `C/V`. -/
lemma homSheafEval_naturality {V W : Cᵒᵖ} (i : V ⟶ W)
    (α : (moduleHomSheaf.{m, w, v, u} O F G).val.obj V) (y : F.val.obj V) :
    homSheafEval.{m, w, v, u} O F G W
        ((moduleHomSheaf.{m, w, v, u} O F G).val.restrictₛₗ i α) (F.val.restrictₛₗ i y) =
      G.val.restrictₛₗ i (homSheafEval.{m, w, v, u} O F G V α y) :=
  PresheafOfModules.naturality_apply
    (α : (restrFun O.obj V.unop).obj F.val ⟶ (restrFun O.obj V.unop).obj G.val)
    (Over.homMk i.unop (by simp) :
      Over.mk (𝟙 W.unop ≫ i.unop) ⟶ Over.mk (𝟙 V.unop)).op y

end InternalHom

/-! ### Currying -/

section Curry

variable
  {P F G H : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}

/-- **The section of `𝓗om_O(F, G)` produced by currying a bilinear map.** For a section `x` of
`P` over `V` it is the `O|_V`-linear map `F|_V ⟶ G|_V` whose component at `W : C/V` pairs the
restriction of `x` to `W.left` with a section of `F` over `W.left`. -/
noncomputable def bilinearCurryHom (b : BilinearMap P F G) (V : Cᵒᵖ) (x : P.val.obj V) :
    (moduleHomSheaf.{m, w, v, u} O F G).val.obj V :=
  show (restrFun O.obj V.unop).obj F.val ⟶ (restrFun O.obj V.unop).obj G.val from
    { app W := ConcreteCategory.ofHom
        { toFun y := b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x) y
          map_add' y y' :=
            map_add (b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)) y y'
          map_smul' r y := b.map_smul_right (op W.unop.left) r _ y }
      naturality {W Z} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        have hcomp : P.val.restrictₛₗ f.unop.left.op (P.val.restrictₛₗ W.unop.hom.op x) =
            P.val.restrictₛₗ Z.unop.hom.op x :=
          (P.val.restrictₛₗ_comp_apply W.unop.hom.op f.unop.left.op x).symm.trans
            (P.val.restrictₛₗ_congr (congrArg Quiver.Hom.op (Over.w f.unop)) x)
        exact ((b.naturality_restrictₛₗ f.unop.left.op
            (P.val.restrictₛₗ W.unop.hom.op x) y).trans
          (b.congr_left (op Z.unop.left) hcomp (F.val.restrictₛₗ f.unop.left.op y))).symm }

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of `bilinearCurryHom`, by definition. -/
lemma homSheafApp_bilinearCurryHom (b : BilinearMap P F G) (V : Cᵒᵖ) (x : P.val.obj V)
    (W : (Over V.unop)ᵒᵖ) (y : F.val.obj (op W.unop.left)) :
    homSheafApp.{m, w, v, u} O F G V (bilinearCurryHom.{m, w, v, u} O b V x) W y =
      b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x) y := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Currying is additive in the section of `P`. -/
lemma bilinearCurryHom_add (b : BilinearMap P F G) (V : Cᵒᵖ) (x x' : P.val.obj V) :
    bilinearCurryHom.{m, w, v, u} O b V (x + x') =
      bilinearCurryHom.{m, w, v, u} O b V x + bilinearCurryHom.{m, w, v, u} O b V x' :=
  homSheafExt.{m, w, v, u} O F G V fun W y =>
    (b.congr_left (op W.unop.left) (map_add (P.val.restrictₛₗ W.unop.hom.op) x x') y).trans
      (b.map_add_left (op W.unop.left) _ _ y)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Currying is linear in the section of `P`. -/
lemma bilinearCurryHom_smul (b : BilinearMap P F G) (V : Cᵒᵖ)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj.obj V) (x : P.val.obj V) :
    bilinearCurryHom.{m, w, v, u} O b V (r • x) =
      r • bilinearCurryHom.{m, w, v, u} O b V x :=
  homSheafExt.{m, w, v, u} O F G V fun W y =>
    (b.congr_left (op W.unop.left) (map_smulₛₗ (P.val.restrictₛₗ W.unop.hom.op) r x) y).trans
      (b.map_smul_left (op W.unop.left) _ _ y)

/-- **Currying a bilinear map.** A bilinear map `P × F ⟶ G` is a morphism of sheaves of modules
`P ⟶ 𝓗om_O(F, G)`, sending a section `x` of `P` to `bilinearCurryHom O b V x`. -/
noncomputable def bilinearCurry (b : BilinearMap P F G) :
    P ⟶ moduleHomSheaf.{m, w, v, u} O F G where
  val :=
    { app V := ConcreteCategory.ofHom
        { toFun := bilinearCurryHom.{m, w, v, u} O b V
          map_add' := bilinearCurryHom_add.{m, w, v, u} O b V
          map_smul' := bilinearCurryHom_smul.{m, w, v, u} O b V }
      naturality {V W} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        refine homSheafExt.{m, w, v, u} O F G W fun Z y => ?_
        have hcomp : P.val.restrictₛₗ Z.unop.hom.op (P.val.restrictₛₗ f x) =
            P.val.restrictₛₗ (Z.unop.hom ≫ f.unop).op x :=
          (P.val.restrictₛₗ_comp_apply f Z.unop.hom.op x).symm
        exact b.congr_left (op Z.unop.left) hcomp y }

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of `bilinearCurry`, by definition. -/
lemma bilinearCurry_val_app (b : BilinearMap P F G) (V : Cᵒᵖ) (x : P.val.obj V) :
    ((bilinearCurry.{m, w, v, u} O b).val.app V).hom x =
      bilinearCurryHom.{m, w, v, u} O b V x := rfl

/-- **Uncurrying a morphism into the internal Hom.** The inverse construction to
`SheafOfModules.bilinearCurry`: a morphism `P ⟶ 𝓗om_O(F, G)` is evaluated on sections by
`homSheafEval`. -/
noncomputable def bilinearUncurry (f : P ⟶ moduleHomSheaf.{m, w, v, u} O F G) :
    BilinearMap P F G where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => homSheafEval.{m, w, v, u} O F G V ((f.val.app V).hom x) y)
      (fun y y' => homSheafEval_add_right.{m, w, v, u} O F G V _ y y'))
    (fun x x' => AddMonoidHom.ext fun y =>
      (congrArg (fun α => homSheafEval.{m, w, v, u} O F G V α y)
          (map_add (f.val.app V).hom x x')).trans
        (homSheafEval_add_left.{m, w, v, u} O F G V _ _ y))
  map_smul_left V r x y :=
    (congrArg (fun α => homSheafEval.{m, w, v, u} O F G V α y)
        ((f.val.app V).hom.map_smul r x)).trans
      (homSheafEval_smul_left.{m, w, v, u} O F G V r _ y)
  map_smul_right V r x y :=
    homSheafEval_smul_right.{m, w, v, u} O F G V r ((f.val.app V).hom x) y
  naturality {V W} g x y :=
    (homSheafEval_naturality.{m, w, v, u} O F G g ((f.val.app V).hom x) y).symm.trans
      (congrArg (fun α => homSheafEval.{m, w, v, u} O F G W α (F.val.restrictₛₗ g y))
        (PresheafOfModules.restrictₛₗ_naturality_apply f.val g x).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The values of `bilinearUncurry`, by definition. -/
lemma bilinearUncurry_app (f : P ⟶ moduleHomSheaf.{m, w, v, u} O F G) (V : Cᵒᵖ)
    (x : P.val.obj V) (y : F.val.obj V) :
    (bilinearUncurry.{m, w, v, u} O f).app V x y =
      homSheafEval.{m, w, v, u} O F G V ((f.val.app V).hom x) y := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Uncurrying undoes currying**, on sections. -/
lemma bilinearUncurry_curry_app (b : BilinearMap P F G) (V : Cᵒᵖ) (x : P.val.obj V)
    (y : F.val.obj V) :
    (bilinearUncurry.{m, w, v, u} O (bilinearCurry.{m, w, v, u} O b)).app V x y = b.app V x y :=
  b.congr_left V (P.val.restrictₛₗ_id_apply _ x) y

/-- **The section of `𝓗om_O(G, H)` produced by currying the last variable of a trilinear
map.** For sections `x` of `P` and `y` of `F` over `V` it is the `O|_V`-linear map
`G|_V ⟶ H|_V` whose component at `W : C/V` pairs the restrictions of `x` and `y`. -/
noncomputable def trilinearCurryHom (b : TrilinearMap P F G H) (V : Cᵒᵖ) (x : P.val.obj V)
    (y : F.val.obj V) : (moduleHomSheaf.{m, w, v, u} O G H).val.obj V :=
  show (restrFun O.obj V.unop).obj G.val ⟶ (restrFun O.obj V.unop).obj H.val from
    { app W := ConcreteCategory.ofHom
        { toFun z := b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)
            (F.val.restrictₛₗ W.unop.hom.op y) z
          map_add' z z' := map_add (b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)
            (F.val.restrictₛₗ W.unop.hom.op y)) z z'
          map_smul' r z := b.smul₃ (op W.unop.left) r _ _ z }
      naturality {W Z} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
        have hP : P.val.restrictₛₗ f.unop.left.op (P.val.restrictₛₗ W.unop.hom.op x) =
            P.val.restrictₛₗ Z.unop.hom.op x :=
          (P.val.restrictₛₗ_comp_apply W.unop.hom.op f.unop.left.op x).symm.trans
            (P.val.restrictₛₗ_congr (congrArg Quiver.Hom.op (Over.w f.unop)) x)
        have hF : F.val.restrictₛₗ f.unop.left.op (F.val.restrictₛₗ W.unop.hom.op y) =
            F.val.restrictₛₗ Z.unop.hom.op y :=
          (F.val.restrictₛₗ_comp_apply W.unop.hom.op f.unop.left.op y).symm.trans
            (F.val.restrictₛₗ_congr (congrArg Quiver.Hom.op (Over.w f.unop)) y)
        exact ((b.naturality_restrictₛₗ f.unop.left.op (P.val.restrictₛₗ W.unop.hom.op x)
              (F.val.restrictₛₗ W.unop.hom.op y) z).trans
            ((b.congr₁ (op Z.unop.left) hP _ _).trans
              (b.congr₂ (op Z.unop.left) _ hF _))).symm }

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of `trilinearCurryHom`, by definition. -/
lemma homSheafApp_trilinearCurryHom (b : TrilinearMap P F G H) (V : Cᵒᵖ) (x : P.val.obj V)
    (y : F.val.obj V) (W : (Over V.unop)ᵒᵖ) (z : G.val.obj (op W.unop.left)) :
    homSheafApp.{m, w, v, u} O G H V (trilinearCurryHom.{m, w, v, u} O b V x y) W z =
      b.app (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)
        (F.val.restrictₛₗ W.unop.hom.op y) z := rfl

/-- **Currying the last variable of a trilinear map.** A trilinear map `P × F × G ⟶ H` is a
bilinear map `P × F ⟶ 𝓗om_O(G, H)`. -/
noncomputable def trilinearCurry (b : TrilinearMap P F G H) :
    BilinearMap P F (moduleHomSheaf.{m, w, v, u} O G H) where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => trilinearCurryHom.{m, w, v, u} O b V x y)
      (fun y y' => homSheafExt.{m, w, v, u} O G H V fun W z =>
        (b.congr₂ (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)
            (map_add (F.val.restrictₛₗ W.unop.hom.op) y y') z).trans
          (b.add₂ (op W.unop.left) _ _ _ z)))
    (fun x x' => AddMonoidHom.ext fun y =>
      homSheafExt.{m, w, v, u} O G H V fun W z =>
        (b.congr₁ (op W.unop.left) (map_add (P.val.restrictₛₗ W.unop.hom.op) x x')
            (F.val.restrictₛₗ W.unop.hom.op y) z).trans
          (b.add₁ (op W.unop.left) _ _ _ z))
  map_smul_left V r x y :=
    homSheafExt.{m, w, v, u} O G H V fun W z =>
      (b.congr₁ (op W.unop.left) (map_smulₛₗ (P.val.restrictₛₗ W.unop.hom.op) r x)
          (F.val.restrictₛₗ W.unop.hom.op y) z).trans
        (b.smul₁ (op W.unop.left) _ _ _ z)
  map_smul_right V r x y :=
    homSheafExt.{m, w, v, u} O G H V fun W z =>
      (b.congr₂ (op W.unop.left) (P.val.restrictₛₗ W.unop.hom.op x)
          (map_smulₛₗ (F.val.restrictₛₗ W.unop.hom.op) r y) z).trans
        (b.smul₂ (op W.unop.left) _ _ _ z)
  naturality {_V W} f x y :=
    homSheafExt.{m, w, v, u} O G H W fun Z z =>
      ((b.congr₁ (op Z.unop.left)
          (P.val.restrictₛₗ_comp_apply f Z.unop.hom.op x).symm _ z).trans
        (b.congr₂ (op Z.unop.left) _
          (F.val.restrictₛₗ_comp_apply f Z.unop.hom.op y).symm z)).symm

end Curry

/-! ### Currying over the slice site -/

section Slice

variable (U : C)

variable
  {P : SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)}
  {F G H : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two sections of `P` over the slice site which differ only by a rewriting of the structure
morphism of the object they are restricted to pair to the same value. This is the one place
where the structure morphism of a composite object of the slice site has to be identified with
the one obtained from `Over.w`. -/
lemma overBilinear_map_congr (b : BilinearMap P (F.over U) (G.over U))
    {V : Over U} {W : C} {φ ψ : W ⟶ U} (h : φ = ψ)
    (k : Over.mk φ ⟶ V) (l : Over.mk ψ ⟶ V) (hk : k.left = l.left)
    (x : P.val.obj (op V)) (y : F.val.obj (op W)) :
    b.app (op (Over.mk φ)) (P.val.restrictₛₗ k.op x) y =
      b.app (op (Over.mk ψ)) (P.val.restrictₛₗ l.op x) y := by
  subst ψ
  have e : k = l := by ext; exact hk
  subst e
  rfl

/-- The structure morphism of a composite object of the slice site: for `V` over `U` and `W`
over `V.left`, the object `W.hom ≫ V.hom` of `C/U` maps to `V` by `W.hom`. The slice site over
an object `V` of `C/U` is the slice site over `V.left`, and this is the comparison that
identification needs. -/
def overSliceHom (V : (Over U)ᵒᵖ) (W : (Over V.unop.left)ᵒᵖ) :
    Over.mk (W.unop.hom ≫ V.unop.hom) ⟶ V.unop :=
  Over.homMk W.unop.hom

/-- **The section of `𝓗om_O(F, G)` produced by currying a bilinear map on the slice site.** For
a section `x` of `P` over `V : C/U` it is the `O|_{V.left}`-linear map `F|_{V.left} ⟶
G|_{V.left}`, whose component at `W` over `V.left` pairs the restriction of `x` along
`overSliceHom U V W` with a section of `F`. -/
noncomputable def bilinearCurryOverHom (b : BilinearMap P (F.over U) (G.over U))
    (V : (Over U)ᵒᵖ) (x : P.val.obj V) :
    (moduleHomSheaf.{m, w, v, u} O F G).val.obj (op V.unop.left) :=
  show (restrFun O.obj V.unop.left).obj F.val ⟶ (restrFun O.obj V.unop.left).obj G.val from
    { app W := ConcreteCategory.ofHom
        { toFun y := b.app (op (Over.mk (W.unop.hom ≫ V.unop.hom)))
            (P.val.restrictₛₗ (overSliceHom U V W).op x) y
          map_add' y y' := map_add (b.app (op (Over.mk (W.unop.hom ≫ V.unop.hom)))
            (P.val.restrictₛₗ (overSliceHom U V W).op x)) y y'
          map_smul' r y := b.map_smul_right (op (Over.mk (W.unop.hom ≫ V.unop.hom))) r _ y }
      naturality {W Z} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        have hw : f.unop.left ≫ W.unop.hom ≫ V.unop.hom = Z.unop.hom ≫ V.unop.hom := by
          rw [← Category.assoc, Over.w]
        have hcomp : P.val.restrictₛₗ (Over.homMk f.unop.left hw :
              Over.mk (Z.unop.hom ≫ V.unop.hom) ⟶ Over.mk (W.unop.hom ≫ V.unop.hom)).op
              (P.val.restrictₛₗ (overSliceHom U V W).op x) =
            P.val.restrictₛₗ (overSliceHom U V Z).op x :=
          (P.val.restrictₛₗ_comp_apply (overSliceHom U V W).op _ x).symm.trans
            (P.val.restrictₛₗ_congr (congrArg Quiver.Hom.op (by ext; exact Over.w f.unop)) x)
        exact ((b.naturality_restrictₛₗ (Over.homMk f.unop.left hw :
              Over.mk (Z.unop.hom ≫ V.unop.hom) ⟶ Over.mk (W.unop.hom ≫ V.unop.hom)).op
              (P.val.restrictₛₗ (overSliceHom U V W).op x) y).trans
          (b.congr_left (op (Over.mk (Z.unop.hom ≫ V.unop.hom))) hcomp
            (F.val.restrictₛₗ f.unop.left.op y))).symm }

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The components of `bilinearCurryOverHom`, by definition. -/
lemma homSheafApp_bilinearCurryOverHom (b : BilinearMap P (F.over U) (G.over U))
    (V : (Over U)ᵒᵖ) (x : P.val.obj V) (W : (Over V.unop.left)ᵒᵖ)
    (y : F.val.obj (op W.unop.left)) :
    homSheafApp.{m, w, v, u} O F G (op V.unop.left)
        (bilinearCurryOverHom.{m, w, v, u} O U b V x) W y =
      b.app (op (Over.mk (W.unop.hom ≫ V.unop.hom)))
        (P.val.restrictₛₗ (overSliceHom U V W).op x) y := rfl

/-- **Currying a bilinear map of restricted sheaves of modules.** A bilinear map
`P × F|_U ⟶ G|_U` on the slice site at `U` is a morphism `P ⟶ 𝓗om_O(F, G)|_U`. This is
`SheafOfModules.bilinearCurry` for the slice site, written out: the slice site over an object
`V` of `C/U` is the slice site over `V.left`, and the structure morphism has to be composed in
by hand. -/
noncomputable def bilinearCurryOver (b : BilinearMap P (F.over U) (G.over U)) :
    P ⟶ (moduleHomSheaf.{m, w, v, u} O F G).over U where
  val :=
    { app V := ConcreteCategory.ofHom
        { toFun := bilinearCurryOverHom.{m, w, v, u} O U b V
          map_add' x x' := homSheafExt.{m, w, v, u} O F G (op V.unop.left) fun W y =>
            (b.congr_left (op (Over.mk (W.unop.hom ≫ V.unop.hom)))
                (map_add (P.val.restrictₛₗ (overSliceHom U V W).op) x x') y).trans
              (b.map_add_left (op (Over.mk (W.unop.hom ≫ V.unop.hom))) _ _ y)
          map_smul' r x := homSheafExt.{m, w, v, u} O F G (op V.unop.left) fun W y =>
            (b.congr_left (op (Over.mk (W.unop.hom ≫ V.unop.hom)))
                (map_smulₛₗ (P.val.restrictₛₗ (overSliceHom U V W).op) r x) y).trans
              (b.map_smul_left (op (Over.mk (W.unop.hom ≫ V.unop.hom))) _ _ y) }
      naturality {V W} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        refine homSheafExt.{m, w, v, u} O F G (op W.unop.left) fun Z y => ?_
        refine Eq.trans ?_ (overBilinear_map_congr.{m, w, v, u} O U b
          (φ := Z.unop.hom ≫ W.unop.hom)
          (ψ := (Z.unop.hom ≫ f.unop.left) ≫ V.unop.hom)
          (by rw [Category.assoc, Over.w])
          ((overSliceHom U W Z) ≫ f.unop)
          (Over.homMk (Z.unop.hom ≫ f.unop.left)) rfl x y)
        exact b.congr_left (op (Over.mk (Z.unop.hom ≫ W.unop.hom)))
          (P.val.restrictₛₗ_comp_apply f (overSliceHom U W Z).op x).symm y }

/-! ### Bilinear and trilinear maps out of an extension by zero -/

section Adjunction

variable [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]

/-- **The engine: extension by zero of a bilinear map.** A bilinear map `P × F|_U ⟶ G|_U` on the
slice site at `U` extends to a bilinear map `j_{U!}P × F ⟶ G`. The adjunction `j_{U!} ⊣ j_U^*`
is about linear maps only; currying through the internal Hom is what makes it apply to a
bilinear one. -/
noncomputable def extendBilinear (b : BilinearMap P (F.over U) (G.over U)) :
    BilinearMap ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P) F G :=
  bilinearUncurry.{m, w, v, u} O
    (((extensionByZeroAdjunction.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).homEquiv P
      (moduleHomSheaf.{m, w, v, u} O F G)).symm (bilinearCurryOver.{m, w, v, u} O U b))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The extended bilinear map on the sections supplied by the unit.** On the image of a section
of `P` under the unit of the adjunction `j_{U!} ⊣ j_U^*`, the extension agrees with the bilinear
map it was built from. -/
lemma extendBilinear_unit (b : BilinearMap P (F.over U) (G.over U)) (V : (Over U)ᵒᵖ)
    (x : P.val.obj V) (y : F.val.obj (op V.unop.left)) :
    (extendBilinear.{m, w, v, u} O U b).app (op V.unop.left)
        ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x) y =
      b.app V x y := by
  have h := ((extensionByZeroAdjunction.{m, w, v, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).homEquiv P
    (moduleHomSheaf.{m, w, v, u} O F G)).apply_symm_apply
      (bilinearCurryOver.{m, w, v, u} O U b)
  have h' := congrArg (fun s : P ⟶ (moduleHomSheaf.{m, w, v, u} O F G).over U =>
    homSheafEval.{m, w, v, u} O F G (op V.unop.left) ((s.val.app V).hom x) y) h
  refine h'.trans ?_
  refine (overBilinear_map_congr.{m, w, v, u} O U b (Category.id_comp V.unop.hom)
    (Over.homMk (𝟙 V.unop.left)) (𝟙 V.unop) rfl x y).trans ?_
  exact b.congr_left V (P.val.restrictₛₗ_id_apply _ x) y

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Recognition of a bilinear map out of an extension by zero.** Two bilinear maps out of
`j_{U!}P` which agree on the local sections supplied by the unit of the adjunction are equal.
This is what the adjunction alone does not give. -/
lemma extendedBilinear_ext
    (b c : BilinearMap ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P) F G)
    (h : ∀ (V : (Over U)ᵒᵖ) (x : P.val.obj V) (y : F.val.obj (op V.unop.left)),
      b.app (op V.unop.left) ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x) y =
        c.app (op V.unop.left) ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x) y)
    (V : Cᵒᵖ)
    (x : ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P).val.obj V)
    (y : F.val.obj V) : b.app V x y = c.app V x y := by
  have hc : bilinearCurry.{m, w, v, u} O b = bilinearCurry.{m, w, v, u} O c := by
    refine ((extensionByZeroAdjunction.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).homEquiv P
      (moduleHomSheaf.{m, w, v, u} O F G)).injective ?_
    refine hom_ext (PresheafOfModules.hom_ext fun W =>
      ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
    refine homSheafExt.{m, w, v, u} O F G (op W.unop.left) fun Z a => ?_
    have hn := PresheafOfModules.restrictₛₗ_naturality_apply
      ((extensionByZeroAdjunction.{m, w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val
      (overSliceHom U W Z).op z
    exact (b.congr_left (op Z.unop.left) hn.symm a).trans
      ((h (op (Over.mk (Z.unop.hom ≫ W.unop.hom))) _ a).trans
        (c.congr_left (op Z.unop.left) hn a))
  rw [← bilinearUncurry_curry_app.{m, w, v, u} O b V x y, hc,
    bilinearUncurry_curry_app.{m, w, v, u}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Recognition of a linear map out of an extension by zero, heterogeneously.** Two morphisms
out of `j_{U!}P` whose targets are known only to be equal, and which agree on the local sections
supplied by the unit, agree everywhere. The heterogeneous form is what a law whose two sides
live in differently indexed homogeneous pieces needs. -/
lemma extendedHom_hext (e : F = G)
    (f : (extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P ⟶ F)
    (g : (extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P ⟶ G)
    (h : ∀ (V : (Over U)ᵒᵖ) (x : P.val.obj V),
      HEq ((f.val.app (op V.unop.left)).hom ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x))
        ((g.val.app (op V.unop.left)).hom ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x)))
    (V : Cᵒᵖ)
    (x : ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P).val.obj V) :
    HEq ((f.val.app V).hom x) ((g.val.app V).hom x) := by
  subst e
  have he : f = g := by
    refine ((extensionByZeroAdjunction.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).homEquiv P
      F).injective ?_
    refine hom_ext (PresheafOfModules.hom_ext fun W =>
      ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    exact eq_of_heq (h W y)
  rw [he]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Recognition of a trilinear map out of an extension by zero, heterogeneously.** The
trilinear counterpart of `SheafOfModules.extendedBilinear_ext`, with the target known only up to
an equality of sheaves of modules. This is the shape in which an associativity law for a graded
action over an extension by zero is stated. -/
lemma extendedTrilinear_hext
    {H' : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (e : H = H')
    (b : TrilinearMap ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P) F G H)
    (c : TrilinearMap ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P) F G H')
    (h : ∀ (V : (Over U)ᵒᵖ) (x : P.val.obj V)
      (y : F.val.obj (op V.unop.left)) (z : G.val.obj (op V.unop.left)),
      HEq (b.app (op V.unop.left) ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x)
          y z)
        (c.app (op V.unop.left) ((((extensionByZeroAdjunction.{m, w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val.app V).hom x)
          y z))
    (V : Cᵒᵖ)
    (x : ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P).val.obj V)
    (y : F.val.obj V) (z : G.val.obj V) : HEq (b.app V x y z) (c.app V x y z) := by
  subst e
  have hn (W : (Over U)ᵒᵖ) (Z : (Over W.unop.left)ᵒᵖ) (a : P.val.obj W) :=
    PresheafOfModules.restrictₛₗ_naturality_apply
      ((extensionByZeroAdjunction.{m, w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).unit.app P).val
      (overSliceHom U W Z).op a
  have hc := extendedBilinear_ext.{m, w, v, u} O U
    (trilinearCurry.{m, w, v, u} O b) (trilinearCurry.{m, w, v, u} O c)
    (fun W a d => homSheafExt.{m, w, v, u} O G H (op W.unop.left) fun Z t =>
      (b.congr₁ (op Z.unop.left) (hn W Z a).symm
          (F.val.restrictₛₗ Z.unop.hom.op d) t).trans
        ((eq_of_heq (h (op (Over.mk (Z.unop.hom ≫ W.unop.hom))) _
            (F.val.restrictₛₗ Z.unop.hom.op d) t)).trans
          (c.congr₁ (op Z.unop.left) (hn W Z a) (F.val.restrictₛₗ Z.unop.hom.op d) t)))
    V x y
  have key (t : TrilinearMap ((extensionByZero.{m, w, v, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P) F G H) :
      t.app V x y z =
        homSheafEval.{m, w, v, u} O G H V ((trilinearCurry.{m, w, v, u} O t).app V x y) z :=
    (t.congr₁ V (((extensionByZero.{m, w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj P).val.restrictₛₗ_id_apply _
        x).symm y z).trans
      (t.congr₂ V _ (F.val.restrictₛₗ_id_apply _ y).symm z)
  exact heq_of_eq ((key b).trans ((congrArg
    (fun s => homSheafEval.{m, w, v, u} O G H V s z) hc).trans (key c).symm))

end Adjunction

end Slice

end SheafOfModules

end
