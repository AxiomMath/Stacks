module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Problem Description

Let `(X, O_X)` be a ringed space (a topological space `X` equipped with a sheaf of
commutative rings `O_X`). All modules below are sheaves of `O_X`-modules.

## Main Definitions

* (Stalk) For a sheaf of `O_X`-modules `F` and a point `x`, the stalk `F_x` is the
  colimit `colim_{x in U} F(U)` over open neighborhoods `U` of `x`. It is a module over
  the local ring `O_{X,x}` (the stalk of the structure sheaf).

* (Flat module over a ring) A module `M` over a commutative ring `R` is flat if the
  functor `N |-> N tensor_R M` is exact (equivalently, preserves injections).

* (Flat sheaf of modules) A sheaf of `O_X`-modules `F` is flat if for every point `x`,
  the stalk `F_x` is a flat module over the local ring `O_{X,x}`.

## Main Statements

Let `0 -> F_2 -> F_1 -> F_0 -> 0` be a short exact sequence of `O_X`-modules.

* Statement 1 (Extension of flat modules is flat). If `F_2` and `F_0` are flat, then
  `F_1` is flat.

* Statement 2 (Kernel of an epimorphism of flat modules is flat). If `F_1` and `F_0`
  are flat, then `F_2` is flat.

This is Stacks project Tag 05NK.

## Formalization notes

* A ringed space is modeled by Mathlib's bundled `AlgebraicGeometry.RingedSpace`:
  a topological space `X = X.carrier` together with a sheaf `O_X = X.presheaf` of commutative rings
  (`X.IsSheaf`).

* The structure sheaf, viewed as a sheaf of (possibly noncommutative) rings via the
  forgetful functor `CommRingCat ⥤ RingCat`, is `structureSheafRing X`, a genuine
  `CategoryTheory.Sheaf` for the open-cover Grothendieck topology on `X`.  Sheaves of
  `O_X`-modules are then modeled by Mathlib's `SheafOfModules (structureSheafRing X)`, which is an
  abelian category.  In particular a *short exact sequence of sheaves of `O_X`-modules* is
  encoded by the standard categorical notion `CategoryTheory.ShortComplex.ShortExact` in
  this abelian category of sheaves (not merely presheaf/sectionwise exactness): this is the
  faithful notion of exactness of sheaves of modules.

* The stalk of the structure sheaf at `x` is the local ring `O_{X,x} = X.presheaf.stalk x`
  (`IsLocalRing` holds for it), and the stalk of (the underlying abelian-group presheaf of)
  `F` at `x` is the colimit `F_x = (toAbPresheaf F).stalk x` in `Ab`.

* The canonical `O_{X,x}`-module structure on `F_x` is the unique module structure for
  which all germ maps `F(U) → F_x` are semilinear over the germ ring maps
  `O_X(U) → O_{X,x}` (this is exactly the standard description of the stalk
  `colim_{x ∈ U} O_{X,x} ⊗_{O_X(U)} F(U)`).  This compatibility is recorded by the
  predicate `GermCompatible`; since the germ maps are jointly surjective, such a structure
  is unique, and it always exists.  Existence and uniqueness are stated as the correctness
  theorems `germCompatibleModule_exists` and `germCompatibleModule_unique`, so that the
  definition of flatness below refers to *the* canonical stalk module structure.

* Flatness of `F` (`IsFlat F`) says: for every point `x` and every germ-compatible
  `O_{X,x}`-module structure on `F_x`, that module is flat over `O_{X,x}`.  By
  `germCompatibleModule_exists` this quantification is non-vacuous, and by
  `germCompatibleModule_unique` it pins down flatness of the single canonical stalk module,
  matching the informal definition "the stalk `F_x` is a flat `O_{X,x}`-module".
-/

/-!
## Implementation notes

The `stacks` Mathlib build ships `sorryAx`-tainted *instances* for the colimit-preservation /
right-exactness of `SheafOfModules.toSheaf` and of the
sheaf stalk functor `TopCat.Sheaf.forget ⋙ stalkFunctor` (they route through the unproved
`HasSheafify` / `HasColimits (TopCat.Sheaf AddCommGrpCat …)` instances).  We rebuild both
facts cleanly: `toSheaf`'s right-exactness is laundered through the *left adjoint*
`PresheafOfModules.sheafification` (clean colimit preservation) via `sheafificationNatIso`
and `sheafificationCompToSheaf` (see `toSheafColim`), and the sheaf stalk functor is the
left adjoint `stalkSkyscraperSheafAdjunction` (see `forgetStalkColim`).  These clean
witnesses are fed *explicitly* into the composite (`compPFC`) so that typeclass search never
re-substitutes the tainted global instances.
-/

open CategoryTheory TopologicalSpace Limits

namespace Stacks.SheafOfModules.FlatShortExact

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **Helper (clean colimit transfer through a preserved functor).**  If `F` preserves the
colimit of `K`, and `F ⋙ G` preserves the colimit of `K`, then `G` preserves the colimit of
`K ⋙ F`.  (The colimit cocone of `K ⋙ F` is `F.mapCocone (colimit.cocone K)`, and `G` maps
it to `(F ⋙ G).mapCocone (colimit.cocone K)`, a colimit by hypothesis.)  Used to launder the
right-exactness of `SheafOfModules.toSheaf` through the (clean) sheafification left adjoint. -/
theorem presComp' {C D E : Type*} [Category C] [Category D] [Category E]
    {Jc : Type*} [Category Jc] (K : Jc ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
    [Limits.HasColimit K] (h1 : Limits.PreservesColimit K F)
    (h2 : Limits.PreservesColimit K (F ⋙ G)) :
    Limits.PreservesColimit (K ⋙ F) G :=
  Limits.preservesColimit_of_preserves_colimit_cocone
    (@Limits.isColimitOfPreserves _ _ _ _ _ _ _ F _ (Limits.colimit.isColimit K) h1)
    (@Limits.isColimitOfPreserves _ _ _ _ _ _ _ (F ⋙ G) _ (Limits.colimit.isColimit K) h2)

/-- **`SheafOfModules.toSheaf` preserves finite colimits.**  In this `stacks` Mathlib build the
global instance for this fact is `sorryAx`-tainted (it routes through the
unproved `HasSheafify` colimit-preservation instances).  We rebuild it cleanly: `toSheaf` is
naturally isomorphic to `forget ⋙ toPresheaf ⋙ presheafToSheaf` (via `sheafificationNatIso`),
and right-exactness is laundered through the *left adjoint* `PresheafOfModules.sheafification`
(whose colimit preservation is clean as a left adjoint) together with the clean natural
isomorphism `sheafificationCompToSheaf` and the clean finite-colimit preservation of
`PresheafOfModules.toPresheaf` and of `presheafToSheaf` (obtained from the clean
`sheafificationAdjunction`, not from the tainted global instance). -/
theorem toSheafColim (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    Limits.PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u, u, u, u} (structureSheafRing X)) := by
  let Fsh := PresheafOfModules.sheafification (𝟙 (structureSheafRing X).obj)
  let adjSh : Fsh ⊣ _ := PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)
  let counitIso := asIso adjSh.counit
  have hFT : Limits.PreservesFiniteColimits
      (Fsh ⋙ SheafOfModules.toSheaf (structureSheafRing X)) := by
    let hpts : Limits.PreservesFiniteColimits
        (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) := by
      let : Limits.PreservesColimitsOfSize.{u, u}
          (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
        (sheafificationAdjunction (Opens.grothendieckTopology X.carrier)
          AddCommGrpCat.{u}).leftAdjoint_preservesColimits
      exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _
    let htp : Limits.PreservesFiniteColimits
        (PresheafOfModules.toPresheaf (structureSheafRing X).obj) :=
      inferInstance
    let : Limits.PreservesFiniteColimits (PresheafOfModules.toPresheaf (structureSheafRing X).obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
      Limits.comp_preservesFiniteColimits _ _
    exact Limits.preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 (structureSheafRing X).obj)).symm
  let : Limits.PreservesColimitsOfSize.{0, 0} Fsh := adjSh.leftAdjoint_preservesColimits
  refine ⟨fun {J} _ _ => ⟨fun {K₂} => ?_⟩⟩
  let Gsh := SheafOfModules.forget (structureSheafRing X) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)
  have e : (K₂ ⋙ Gsh) ⋙ Fsh ≅ K₂ :=
    NatIso.ofComponents (fun j => counitIso.app (K₂.obj j))
      (fun f => counitIso.hom.naturality (K₂.map f))
  have h1 : Limits.PreservesColimit (K₂ ⋙ Gsh) Fsh := inferInstance
  have h2 : Limits.PreservesColimit (K₂ ⋙ Gsh)
      (Fsh ⋙ SheafOfModules.toSheaf (structureSheafRing X)) :=
    (hFT.preservesFiniteColimits J).preservesColimit
  have hpc : Limits.PreservesColimit ((K₂ ⋙ Gsh) ⋙ Fsh)
      (SheafOfModules.toSheaf (structureSheafRing X)) :=
    presComp' (K₂ ⋙ Gsh) Fsh (SheafOfModules.toSheaf (structureSheafRing X)) h1 h2
  exact Limits.preservesColimit_of_iso_diagram _ e

/-- Composition of finite-colimit-preserving functors, taking the two preservation facts as
*explicit* arguments.  This is essential to avoid typeclass search silently substituting the
`sorryAx`-tainted global colimit-preservation instance for `SheafOfModules.toSheaf` / the
sheaf stalk functor: we feed the clean witnesses (`toSheafColim`, `forgetStalkColim`) directly. -/
theorem compPFC {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E)
    (hF : Limits.PreservesFiniteColimits F) (hG : Limits.PreservesFiniteColimits G) :
    Limits.PreservesFiniteColimits (F ⋙ G) :=
  @Limits.comp_preservesFiniteColimits _ _ _ _ _ _ F G hF hG

/-- **The sheaf stalk functor `forget ⋙ stalkFunctor` preserves finite colimits.**
The global instance for this is `sorryAx`-tainted (it routes through the unproved
`HasColimits (TopCat.Sheaf AddCommGrpCat …)`).  We rebuild it cleanly: the sheaf stalk
functor is the *left adjoint* `stalkSkyscraperSheafAdjunction` (right adjoint = skyscraper
sheaf), hence preserves all colimits; `AddCommGrpCat` has the required colimits/terminal
object cleanly. -/
theorem forgetStalkColim (x : X.carrier) :
    Limits.PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  classical
  let : Limits.PreservesColimitsOfSize.{0, 0}
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    (stalkSkyscraperSheafAdjunction x).leftAdjoint_preservesColimits
  exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- The underlying presheaf of abelian groups of a sheaf of `O_X`-modules, as a
`TopCat.Presheaf Ab X.carrier`. -/
noncomputable def toAbPresheaf (F : SheafOfModules (structureSheafRing X)) :
    TopCat.Presheaf Ab X.carrier :=
  (PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj F.val

/-- The stalk `F_x` of `F` at `x`, as an abelian group (the colimit
`colim_{x ∈ U} F(U)` of the sections over open neighbourhoods of `x`). -/
noncomputable def abStalk (F : SheafOfModules (structureSheafRing X)) (x : X.carrier) : Ab :=
  (toAbPresheaf F).stalk x

/-- The germ map `F(U) → F_x` on underlying abelian groups, applied to an element. -/
noncomputable def abGerm (F : SheafOfModules (structureSheafRing X)) {x : X.carrier}
    (U : Opens X.carrier) (hx : x ∈ U)
    (m : F.val.obj (Opposite.op U)) : abStalk F x :=
  (ConcreteCategory.hom ((toAbPresheaf F).germ U x hx)) m

/-- The scalar multiplication of `r : O_X(U)` on a section `m : F(U)`, using the
`O_X(U)`-module structure that `F.val.obj (op U)` carries as an object of
`ModuleCat (O_X(U))`. -/
noncomputable def sectionSMul (F : SheafOfModules (structureSheafRing X)) (U : Opens X.carrier)
    (r : X.presheaf.obj (Opposite.op U)) (m : F.val.obj (Opposite.op U)) :
    F.val.obj (Opposite.op U) :=
  (show (structureSheafRing X).obj.obj (Opposite.op U) from r) • m

/-- A module structure on the abelian-group stalk `F_x` over the local ring `O_{X,x}` is
*germ-compatible* when every germ map `F(U) → F_x` is semilinear over the germ ring map
`O_X(U) → O_{X,x}`, i.e. `germ (r • m) = (germ_ring r) • (germ m)`.  Since the germ maps
are jointly surjective there is at most one such structure (see
`germCompatibleModule_unique`); it always exists (see `germCompatibleModule_exists`), and is
the canonical `O_{X,x}`-module structure on `F_x`, namely
`colim_{x ∈ U} O_{X,x} ⊗_{O_X(U)} F(U)`. -/
def GermCompatible (F : SheafOfModules (structureSheafRing X)) (x : X.carrier)
    [Module (X.presheaf.stalk x) (abStalk F x)] : Prop :=
  ∀ (U : Opens X.carrier) (hx : x ∈ U) (r : X.presheaf.obj (Opposite.op U))
      (m : F.val.obj (Opposite.op U)),
    abGerm F U hx (sectionSMul F U r m)
      = (X.presheaf.germ U x hx) r • abGerm F U hx m

/-- **Flatness of a sheaf of modules** (Stacks Tag 05NK setup).  `F` is flat if at every
point `x`, the stalk `F_x`, equipped with its canonical (germ-compatible) `O_{X,x}`-module
structure, is a flat `O_{X,x}`-module.  This is phrased as a condition on every
germ-compatible module structure; by `germCompatibleModule_exists` this is non-vacuous and
by `germCompatibleModule_unique` it refers to the unique canonical structure. -/
def IsFlat (F : SheafOfModules (structureSheafRing X)) : Prop :=
  ∀ (x : X.carrier) (inst : Module (X.presheaf.stalk x) (abStalk F x)),
    @GermCompatible _ F x inst → @Module.Flat _ _ _ _ inst

/- ===========================================================================
   ALGEBRA LAYER.  Pure module theory over a commutative ring `R`: the two
   "two-out-of-three" flatness facts for a short exact sequence of `R`-modules.
   These are NOT in Mathlib (the `Module.Flat` ↔ `Tor` bridge is an explicit
   Mathlib TODO), so they are proved here by hand from the tensor-exactness
   characterisation `Module.Flat.iff_rTensor_exact` / `iff_rTensor_injective'`.
   They are stated on bare `R`-modules with a `Function.Exact` short exact
   sequence, which is the convenient interface for the stalkwise reduction. -/

/-- Tensoring on the right with `ι` commutes with tensoring on the left with `f`, pointwise. -/
private theorem rTensor_lTensor_apply_comm {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] P) (ι : N →ₗ[R] N') (z : TensorProduct R N M) :
    LinearMap.rTensor P ι (LinearMap.lTensor N f z)
      = LinearMap.lTensor N' f (LinearMap.rTensor M ι z) :=
  by rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

/-- **Algebra Fact 1 (extension of flats is flat).**  For a short exact sequence
of `R`-modules `0 → M₁ →[f] M₂ →[g] M₃ → 0` (`f` injective, exact at `M₂`, `g`
surjective), if `M₁` and `M₃` are flat then `M₂` is flat.

INFORMAL PROOF (rigorous).  Flatness is tested by tensoring with an arbitrary
injection of `R`-modules: by `Module.Flat.iff_rTensor_exact`, `M` is flat iff for
every short exact `0 → N → N' → N'' → 0` the sequence
`N ⊗ M → N' ⊗ M → N'' ⊗ M` is exact, and (combined with right-exactness of
tensor, which always holds) flatness is equivalent to *injectivity* of
`N ⊗ M → N' ⊗ M` for every injection `N ↪ N'`.  Fix an injection `ι : N ↪ N'`.
Tensoring the SES `0 → M₁ → M₂ → M₃ → 0` (on the right by `ι`) gives a 3×2
commutative diagram with exact rows (right-exactness of `· ⊗ N` and `· ⊗ N'`)
and `M₁,M₃` columns injective (flatness of `M₁`,`M₃`):
      N⊗M₁ → N⊗M₂ → N⊗M₃ → 0
       ↓ι₁    ↓ι₂    ↓ι₃
      N'⊗M₁→ N'⊗M₂→ N'⊗M₃→ 0
with the top and bottom rows also right-exact, and the left columns `ι₁`, `ι₃`
injective.  A diagram chase (the relevant half of the snake/four lemma: `ι₁`
injective + `ι₃` injective + exact rows ⇒ `ι₂` injective) shows the middle
column `ι₂ : N⊗M₂ → N'⊗M₂` is injective.  Hence `M₂` is flat.

SANITY CHECK PASSED: statement confirmed TRUE for all commutative `R` (Stacks
00HL); orientation correct (this is extension-of-flats, not the false
`M₁,M₂ flat ⇒ M₃ flat`). -/
theorem Module.Flat.of_shortExact_extension
    {R M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (h₁ : Module.Flat R M₁) (h₃ : Module.Flat R M₃) : Module.Flat R M₂ := by
  -- Test flatness of `M₂` against an arbitrary injection `ι : N ↪ N'`, i.e. show
  -- `rTensor M₂ ι` is injective (`Module.Flat.iff_rTensor_preserves_injective_linearMap`).
  -- Tensor the SES `0 → M₁ → M₂ → M₃ → 0` on the left by `N` and `N'`; the columns are
  -- `rTensor M_i ι`, the rows are right-exact (`LinearMap.lTensor_exact`), `rTensor M₁ ι`,
  -- `rTensor M₃ ι` are injective (`M₁`, `M₃` flat), and the bottom-left horizontal map
  -- `lTensor N' f` is injective because `M₃` is flat
  -- (`LinearMap.lTensor_injective_of_exact_of_flat`).  A four-lemma diagram chase gives
  -- `rTensor M₂ ι` injective.
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro z hz
  -- Step 1: `lTensor N g z = 0` (using `rTensor M₃ ι` injective).
  have h3inj : Function.Injective (LinearMap.rTensor M₃ ι) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have hgz : LinearMap.lTensor N g z = 0 := by
    apply h3inj
    rw [rTensor_lTensor_apply_comm, hz, map_zero, map_zero]
  -- Step 2: `z = lTensor N f w` (exactness of the tensored top row).
  obtain ⟨w, hw⟩ := (lTensor_exact N hfg hg z).mp hgz
  -- Step 3: `rTensor M₁ ι w = 0`, using `lTensor N' f` injective (`M₃` flat).
  have hf'inj : Function.Injective (LinearMap.lTensor N' f) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N'
  have h1inj : Function.Injective (LinearMap.rTensor M₁ ι) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have hw0 : LinearMap.rTensor M₁ ι w = 0 := by
    apply hf'inj
    rw [← rTensor_lTensor_apply_comm, hw, hz, map_zero]
  have : w = 0 := h1inj (by rw [hw0, map_zero])
  rw [← hw, this, map_zero]

/-- **Algebra Fact 2 (kernel of an epi of flats is flat).**  For a short exact
sequence `0 → M₁ →[f] M₂ →[g] M₃ → 0` of `R`-modules, if `M₂` and `M₃` are flat
then `M₁` is flat.

INFORMAL PROOF (rigorous).  Test flatness of `M₁` against an arbitrary injection
`ι : N ↪ N'`.  Tensor the SES by `ι` to get the commutative diagram with exact
rows (top and bottom rows right-exact; moreover, since `M₃` is flat the top and
bottom rows are *fully* exact including injectivity on the left):
      0 → N⊗M₁ → N⊗M₂ → N⊗M₃ → 0
           ↓ι₁    ↓ι₂    ↓ι₃
      0 → N'⊗M₁→ N'⊗M₂→ N'⊗M₃→ 0
Flatness of `M₃` makes the rows short exact (left `0`'s present), flatness of
`M₂` makes `ι₂` injective.  A diagram chase (the relevant half of the four
lemma: `ι₂` injective + left squares commute + top row exact at `N⊗M₁` ⇒ `ι₁`
injective) gives that `ι₁ : N⊗M₁ → N'⊗M₁` is injective.  Hence `M₁` is flat.
Concretely: `M₃` flat ⇒ `Tor₁(N''/N, M₃)`-type obstruction vanishes so the
connecting maps make `0 → N⊗M₁ → N⊗M₂` exact; combined with `ι₂` injective and a
chase, `ι₁` is injective.  Hence `M₁` is flat.

SANITY CHECK PASSED: statement confirmed TRUE for all commutative `R` (Stacks
05NJ); orientation correct (kernel of an epi between flats; NOT the false
`M₁,M₂ flat ⇒ M₃ flat`).  Tor view of the key step: the segment
`Tor₂(M₃,N) → Tor₁(M₁,N) → Tor₁(M₂,N)` has both ends `0` (M₃ flat ⇒ all higher
Tor vanish, in particular `Tor₂(M₃,N)=0`; M₂ flat ⇒ `Tor₁(M₂,N)=0`), forcing
`Tor₁(M₁,N)=0`.  The diagram-chase proof above is the Tor-free incarnation. -/
@[ega "0 20.6.21" "more general", sga "4 XVII 4.1.1" "(i), special case"]
theorem Module.Flat.of_shortExact_kernel
    {R M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (h₂ : Module.Flat R M₂) (h₃ : Module.Flat R M₃) : Module.Flat R M₁ := by
  -- Test flatness of `M₁` against an arbitrary injection `ι : N ↪ N'`: show
  -- `rTensor M₁ ι` injective.  Square `rTensor M₂ ι ∘ lTensor N f =
  -- lTensor N' f ∘ rTensor M₁ ι`.  If `rTensor M₁ ι w = 0` then
  -- `rTensor M₂ ι (lTensor N f w) = 0`; `M₂` flat ⇒ `rTensor M₂ ι` injective ⇒
  -- `lTensor N f w = 0`; `M₃` flat ⇒ `lTensor N f` injective
  -- (`LinearMap.lTensor_injective_of_exact_of_flat`) ⇒ `w = 0`.
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro w hw
  have h2inj : Function.Injective (LinearMap.rTensor M₂ ι) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have hflf : Function.Injective (LinearMap.lTensor N f) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N
  -- `lTensor N f w = 0`
  have hlf : LinearMap.lTensor N f w = 0 := by
    apply h2inj
    rw [rTensor_lTensor_apply_comm, hw, map_zero, map_zero]
  exact hflf (by rw [hlf, map_zero])

/- ===========================================================================
   BRIDGE LAYER.  Transport a short exact sequence of sheaves of modules to a
   short exact sequence of the stalk `O_{X,x}`-modules, and relate the abstract
   `IsFlat` predicate to flatness of the canonical stalk module.  This rests on
   exactness of the stalk functor (`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`),
   the canonical stalk module structure (`PresheafOfModules.instModule…`) and
   germ-semilinearity (`PresheafOfModules.germ_smul`). -/

/-- The canonical germ-compatible `O_{X,x}`-module structure on the stalk
`F_x = (toAbPresheaf F).stalk x`, supplied by Mathlib's stalk-module instance for
presheaves of modules (`PresheafOfModules.instModule…CommRingCat`).  We package
it as a `def` so the bridge and main theorems can name *the* canonical structure.

INFORMAL/CONSTRUCTION.  `F.val : PresheafOfModules ((structureSheafRing X).obj)` where
`(structureSheafRing X).obj = X.presheaf ⋙ forget₂ CommRingCat RingCat`.  Mathlib endows
`F.val.presheaf.stalk x` with a `Module (X.presheaf.stalk x)`-structure.  The
abelian group `abStalk F x = (toAbPresheaf F).stalk x` is, up to the
`Ab = AddCommGrpCat` and `toPresheaf`/`.presheaf` identifications, the same
object, so the instance transports along that identification. -/
@[reducible] noncomputable def stalkModule (F : SheafOfModules (structureSheafRing X))
    (x : X.carrier) :
    Module (X.presheaf.stalk x) (abStalk F x) := by
  -- `infer_instance` after unfolding `abStalk`/`toAbPresheaf` to expose
  -- `F.val.presheaf.stalk x` and bridging `Ab`/`AddCommGrpCat`,
  -- `PresheafOfModules.toPresheaf … .obj F.val` vs `F.val.presheaf`.
  -- The relevant Mathlib instance is
  -- `PresheafOfModules.instModule…CommRingCat` from `Mathlib.Algebra.Category.ModuleCat.Stalk`.
  exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The canonical stalk module structure is germ-compatible: this is exactly
`PresheafOfModules.germ_smul`, after unfolding `abGerm`/`sectionSMul`. -/
theorem stalkModule_germCompatible (F : SheafOfModules (structureSheafRing X)) (x : X.carrier) :
    @GermCompatible _ F x (stalkModule F x) := by
  -- SANITY CHECK PASSED (statement is `germ_smul`, a Mathlib lemma).  Unfold
  -- `GermCompatible`, `abGerm`, `sectionSMul`; the goal becomes
  -- `germ (r • m) = (germ_ring r) • germ m`, which is
  -- `PresheafOfModules.germ_smul F.val x U hx r m` (modulo the `stalkModule`
  -- definitional bridge). -/
  intro U hx r m
  simp only [abGerm, sectionSMul]
  exact PresheafOfModules.germ_smul F.val x U hx r m

/-- **Correctness theorem (existence).** There is a germ-compatible `O_{X,x}`-module
structure on the stalk `F_x` (namely the canonical one,
`colim_{x ∈ U} O_{X,x} ⊗_{O_X(U)} F(U)`).  This guarantees `IsFlat` is non-vacuous. -/
theorem germCompatibleModule_exists (F : SheafOfModules (structureSheafRing X)) (x : X.carrier) :
    ∃ inst : Module (X.presheaf.stalk x) (abStalk F x), @GermCompatible _ F x inst :=
  ⟨stalkModule F x, stalkModule_germCompatible F x⟩

/-- **Correctness theorem (uniqueness).** Any two germ-compatible `O_{X,x}`-module
structures on the stalk `F_x` coincide.  Hence the canonical stalk module structure is
well-defined and `IsFlat` refers to flatness of that single module.

Proof.
Two `O_{X,x}`-module structures agree iff their scalar multiplications agree.
Every `(ρ, s) ∈ O_{X,x} × F_x` lifts: `ρ = germ r` and `s = germ m` for sections
`r, m` over a common neighbourhood `U` (filteredness of the stalk colimit,
`TopCat.Presheaf.germ_exist`).  Germ-compatibility forces, for *either* module
structure, `ρ • s = germ(r • m)` — a value independent of the structure.  Hence
the two `SMul`s agree, and `Module.ext` concludes. -/
theorem germCompatibleModule_unique (F : SheafOfModules (structureSheafRing X)) (x : X.carrier)
    (inst₁ inst₂ : Module (X.presheaf.stalk x) (abStalk F x))
    (h₁ : @GermCompatible _ F x inst₁) (h₂ : @GermCompatible _ F x inst₂) :
    inst₁ = inst₂ := by
  apply Module.ext
  funext ρ s
  obtain ⟨Ur, hxr, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf ρ
  obtain ⟨Um, hxm, m, hm⟩ := TopCat.Presheaf.exists_germ_eq (toAbPresheaf F) s
  set U : Opens X.carrier := Ur ⊓ Um with hU
  have hxU : x ∈ U := ⟨hxr, hxm⟩
  have iUr : U ⟶ Ur := homOfLE inf_le_left
  have iUm : U ⟶ Um := homOfLE inf_le_right
  set r' : X.presheaf.obj (Opposite.op U) :=
    (ConcreteCategory.hom (X.presheaf.map iUr.op)) r with hr'
  set m' : F.val.obj (Opposite.op U) :=
    (ConcreteCategory.hom ((toAbPresheaf F).map iUm.op)) m with hm'
  have hgr : (ConcreteCategory.hom (X.presheaf.germ U x hxU)) r' = ρ := by
    rw [hr', TopCat.Presheaf.germ_res_apply]; exact hr
  have hgm : abGerm F U hxU m' = s := by
    rw [hm', abGerm]
    rw [TopCat.Presheaf.germ_res_apply]; exact hm
  have e1 := h₁ U hxU r' m'
  have e2 := h₂ U hxU r' m'
  change @SMul.smul _ _ inst₁.toSMul ρ s = @SMul.smul _ _ inst₂.toSMul ρ s
  have key1 : @SMul.smul _ _ inst₁.toSMul ρ s
      = abGerm F U hxU (sectionSMul F U r' m') := by
    rw [← hgr, ← hgm]; exact e1.symm
  have key2 : @SMul.smul _ _ inst₂.toSMul ρ s
      = abGerm F U hxU (sectionSMul F U r' m') := by
    rw [← hgr, ← hgm]; exact e2.symm
  rw [key1, key2]

/-- The `O_{X,x}`-linear stalk map induced by a morphism `φ : F ⟶ G` of sheaves of
`O_X`-modules.  Its underlying additive map is the image of `φ` under the (additive)
stalk functor on the underlying presheaves of abelian groups; linearity over the
local ring `O_{X,x}` follows from semilinearity of the germ maps
(`PresheafOfModules.germ_smul`) together with naturality of germs under the stalk
functor (`TopCat.Presheaf.stalkFunctor_map_germ_apply`). -/
@[ega "0 3.1.6" "special case"]
noncomputable def stalkLinearMap {F G : SheafOfModules (structureSheafRing X)} (φ : F ⟶ G)
    (x : X.carrier) :
    letI := stalkModule F x; letI := stalkModule G x;
    (abStalk F x) →ₗ[X.presheaf.stalk x] (abStalk G x) :=
  letI := stalkModule F x; letI := stalkModule G x;
  { toFun := fun s => (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map φ.val))) s
    map_add' := by intro a b; exact map_add _ _ _
    map_smul' := by
      intro ρ s
      simp only [RingHom.id_apply]
      obtain ⟨Ur, hxr, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf ρ
      obtain ⟨Um, hxm, m, hm⟩ := TopCat.Presheaf.exists_germ_eq (toAbPresheaf F) s
      set U : Opens X.carrier := Ur ⊓ Um with hU
      have hxU : x ∈ U := ⟨hxr, hxm⟩
      have iUr : U ⟶ Ur := homOfLE inf_le_left
      have iUm : U ⟶ Um := homOfLE inf_le_right
      set r' : X.presheaf.obj (Opposite.op U) :=
        (ConcreteCategory.hom (X.presheaf.map iUr.op)) r with hr'
      set m' : F.val.obj (Opposite.op U) :=
        (ConcreteCategory.hom ((toAbPresheaf F).map iUm.op)) m with hm'
      have hgr : (ConcreteCategory.hom (X.presheaf.germ U x hxU)) r' = ρ := by
        rw [hr', TopCat.Presheaf.germ_res_apply]; exact hr
      have hgm : (ConcreteCategory.hom ((toAbPresheaf F).germ U x hxU)) m' = s := by
        rw [hm', TopCat.Presheaf.germ_res_apply]; exact hm
      set Φ := (TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map φ.val) with hΦ
      have eF : ρ • s = (ConcreteCategory.hom ((toAbPresheaf F).germ U x hxU))
          ((show (structureSheafRing X).obj.obj (Opposite.op U) from r') • m') := by
        rw [← hgr, ← hgm]
        exact (PresheafOfModules.germ_smul F.val x U hxU r' m').symm
      have nat : ∀ (t : F.val.obj (Opposite.op U)),
          (ConcreteCategory.hom Φ) ((ConcreteCategory.hom ((toAbPresheaf F).germ U x hxU)) t)
            = (ConcreteCategory.hom ((toAbPresheaf G).germ U x hxU))
                ((ConcreteCategory.hom (φ.val.app (Opposite.op U))) t) := by
        intro t
        exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
          ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map φ.val) t
      have lin : (ConcreteCategory.hom (φ.val.app (Opposite.op U)))
          ((show (structureSheafRing X).obj.obj (Opposite.op U) from r') • m')
          = (show (structureSheafRing X).obj.obj (Opposite.op U) from r')
              • (ConcreteCategory.hom (φ.val.app (Opposite.op U))) m' :=
        map_smul _ _ _
      have eG := PresheafOfModules.germ_smul G.val x U hxU r'
          ((ConcreteCategory.hom (φ.val.app (Opposite.op U))) m')
      rw [eF, nat, lin]
      erw [eG, hgr, ← nat, hgm] }

/-- The additive stalk functor at `x` on sheaves of `O_X`-modules: take the underlying
sheaf of abelian groups (`SheafOfModules.toSheaf`), forget to a presheaf, and take the
stalk at `x`.  This composite is exact (each factor preserves finite limits and
colimits), which provides the abelian-group short exact sequence of stalks. -/
noncomputable def stalkF (x : X.carrier) :
    SheafOfModules (structureSheafRing X) ⥤ Ab :=
  SheafOfModules.toSheaf (structureSheafRing X) ⋙
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- **Stalk short-exactness bridge.**  A short exact sequence `S` of sheaves of
`O_X`-modules induces, at every point `x`, a short exact sequence of the canonical
stalk `O_{X,x}`-modules: there are `O_{X,x}`-linear maps
`f : (S.X₁)_x → (S.X₂)_x` and `g : (S.X₂)_x → (S.X₃)_x` with `f` injective,
`g` surjective, and exactness at the middle, where each stalk carries its canonical
`stalkModule` structure.

INFORMAL PROOF (rigorous).  The maps are the stalks of `S.f` and `S.g`, i.e. the
images under the (additive) stalk functor `stalkFunctor Ab x ∘ (forget)`.  They
are `O_{X,x}`-linear because the germ maps are semilinear (`germ_smul`) and the
stalk module structure is defined exactly so germ maps are linear; concretely the
stalk of a `SheafOfModules` morphism is `O_{X,x}`-linear via the colimit module
structure (`CategoryTheory.Limits.IsColimit.ι_smul`).  Exactness of the resulting
sequence of abelian groups is the exactness of the stalk functor on the short
exact sequence `S`: applying `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` to
the image of `S` under `SheafOfModules.toSheaf` (a sheaf of abelian groups, whose
underlying presheaf is `toAbPresheaf`), the short complex `S.map (forget ∘
stalkFunctor x)` is exact for every `x`; together with `hS.mono_f`/`hS.epi_g`
(monos/epis of sheaves are detected on stalks, `stalkFunctor_preserves_mono` and
the colimit-of-epis fact) this gives `f` injective and `g` surjective.  Reading
this exact `ShortComplex (Ab)` elementwise via
`ShortExact.moduleCat_exact_iff_function_exact`-style bridges yields
`Function.Exact f g`.

SANITY CHECK PASSED: this is the standard fact that the stalk functor on sheaves
of modules is exact (Stacks; Mathlib `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`
provides the abelian-group exactness, the module structure/linearity is the
canonical colimit one).  Orientation matches `S`: `f` from the stalk of `S.f`
(injective), `g` from the stalk of `S.g` (surjective). -/
theorem stalkShortExact
    (S : ShortComplex (SheafOfModules (structureSheafRing X)))
    (hS : S.ShortExact) (x : X.carrier) :
    ∃ (f : letI := stalkModule S.X₁ x; letI := stalkModule S.X₂ x;
          (abStalk S.X₁ x) →ₗ[X.presheaf.stalk x] (abStalk S.X₂ x))
      (g : letI := stalkModule S.X₂ x; letI := stalkModule S.X₃ x;
          (abStalk S.X₂ x) →ₗ[X.presheaf.stalk x] (abStalk S.X₃ x)),
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  -- Construct `f, g` as the stalks of `S.f, S.g` and prove linearity + the SES
  -- via exactness of the stalk functor (see informal proof above).
  let := stalkModule S.X₁ x
  let := stalkModule S.X₂ x
  let := stalkModule S.X₃ x
  have : (SheafOfModules.toSheaf (structureSheafRing X)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have i1 : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
          :=
    inferInstance
  -- Clean colimit preservation of the sheaf stalk functor (the global instance is tainted).
  have i2 : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
          :=
    forgetStalkColim x
  have hpzm_inner : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesZeroMorphisms := inferInstance
  have hpl : PreservesFiniteLimits (stalkF x) := by
    unfold stalkF; exact comp_preservesFiniteLimits _ _
  -- Provide the clean `PreservesFiniteColimits (toSheaf …)` and sheaf-stalk colimit
  -- preservation built above, fed EXPLICITLY (via `compPFC`) so that the composite
  -- `stalkF x` colimit-preservation never routes through a tainted global instance.
  have hpc : PreservesFiniteColimits (stalkF x) := by
    unfold stalkF
    exact compPFC (SheafOfModules.toSheaf (structureSheafRing X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (toSheafColim X) (forgetStalkColim x)
  -- NB: providing both functor args explicitly (rather than `unfold; infer_instance`)
  -- keeps the synthesized `(stalkF x).PreservesZeroMorphisms` term free of the silently
  -- inserted `sorryAx` that `respectTransparency false` would otherwise produce when
  -- folding back the unfolded composite instance.
  have : (stalkF x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp (SheafOfModules.toSheaf (structureSheafRing X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  have hUSE : (S.map (stalkF x)).ShortExact := hS.map_of_exact (stalkF x)
  -- The goal's stalk maps `stalkLinearMap S.f x`, `stalkLinearMap S.g x` have underlying
  -- types `abStalk S.X\u1d62 x`, while the abelian-group SES `hUSE` lives on the types
  -- `(S.map (stalkF x)).X\u1d62 = (stalkF x).obj S.X\u1d62`.  These objects are *equal* (after
  -- unfolding `stalkF`), but under `respectTransparency false` `exact`-ing across the
  -- coercion silently inserts `sorryAx`.  So we bridge explicitly via canonical
  -- `eqToIso` `AddEquiv`s and conjugate every property through them.
  have hobj1 : abStalk S.X₁ x = (stalkF x).obj S.X₁ := by
    unfold stalkF abStalk toAbPresheaf; rfl
  have hobj2 : abStalk S.X₂ x = (stalkF x).obj S.X₂ := by
    unfold stalkF abStalk toAbPresheaf; rfl
  have hobj3 : abStalk S.X₃ x = (stalkF x).obj S.X₃ := by
    unfold stalkF abStalk toAbPresheaf; rfl
  let e₁ : abStalk S.X₁ x ≃+ (S.map (stalkF x)).X₁ :=
    (eqToIso hobj1).addCommGroupIsoToAddEquiv
  let e₂ : abStalk S.X₂ x ≃+ (S.map (stalkF x)).X₂ :=
    (eqToIso hobj2).addCommGroupIsoToAddEquiv
  let e₃ : abStalk S.X₃ x ≃+ (S.map (stalkF x)).X₃ :=
    (eqToIso hobj3).addCommGroupIsoToAddEquiv
  -- Ladder squares: the bridge equivs conjugate the abelian-group maps `(S.map _).f/.g`
  -- to the stalk linear maps `stalkLinearMap S.f/.g x`.  Provable by `rfl` after `ext`.
  have sq1 : ((S.map (stalkF x)).f.hom).comp (e₁ : abStalk S.X₁ x →+ _)
      = (e₂ : abStalk S.X₂ x →+ _).comp (stalkLinearMap S.f x).toAddMonoidHom := by
    ext s
    simp only [e₁, e₂, Iso.addCommGroupIsoToAddEquiv, AddMonoidHom.coe_comp,
      Function.comp_apply, eqToIso.hom]
    rfl
  have sq2 : ((S.map (stalkF x)).g.hom).comp (e₂ : abStalk S.X₂ x →+ _)
      = (e₃ : abStalk S.X₃ x →+ _).comp (stalkLinearMap S.g x).toAddMonoidHom := by
    ext s
    simp only [e₂, e₃, Iso.addCommGroupIsoToAddEquiv, AddMonoidHom.coe_comp,
      Function.comp_apply, eqToIso.hom]
    rfl
  -- Pointwise conjugation identities.
  have hpt1 : ∀ s, e₂ (stalkLinearMap S.f x s) = (S.map (stalkF x)).f.hom (e₁ s) := by
    intro s
    have := DFunLike.congr_fun sq1 s
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddMonoidHom.coe_ofClass, LinearMap.toAddMonoidHom_coe] using this.symm
  have hpt2 : ∀ s, e₃ (stalkLinearMap S.g x s) = (S.map (stalkF x)).g.hom (e₂ s) := by
    intro s
    have := DFunLike.congr_fun sq2 s
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddMonoidHom.coe_ofClass, LinearMap.toAddMonoidHom_coe] using this.symm
  refine ⟨stalkLinearMap S.f x, stalkLinearMap S.g x, ?_, ?_, ?_⟩
  · -- Injectivity: `stalkLinearMap S.f x = e₂.symm ∘ (S.map _).f ∘ e₁`.
    have hf : Function.Injective ⇑(S.map (stalkF x)).f.hom :=
      (AddCommGrpCat.mono_iff_injective _).mp hUSE.mono_f
    intro a b hab
    have : (S.map (stalkF x)).f.hom (e₁ a) = (S.map (stalkF x)).f.hom (e₁ b) := by
      rw [← hpt1, ← hpt1, hab]
    exact e₁.injective (hf this)
  · -- Exactness via the ladder lemma.
    have hex := (ShortComplex.ab_exact_iff_function_exact (S.map (stalkF x))).mp hUSE.exact
    exact (Function.Exact.iff_of_ladder_addEquiv e₁ e₂ e₃ sq1 sq2).mp hex
  · -- Surjectivity: `stalkLinearMap S.g x = e₃.symm ∘ (S.map _).g ∘ e₂`.
    have hg : Function.Surjective ⇑(S.map (stalkF x)).g.hom :=
      (AddCommGrpCat.epi_iff_surjective _).mp hUSE.epi_g
    intro c
    obtain ⟨b, hb⟩ := hg (e₃ c)
    refine ⟨e₂.symm b, ?_⟩
    apply e₃.injective
    rw [hpt2]
    simp only [AddEquiv.apply_symm_apply, hb]

/-- Helper: `IsFlat F` is equivalent to flatness of the canonical stalk module at
 every point.  (`→` is immediate from the definition applied to `stalkModule`;
`←` uses `germCompatibleModule_unique` to transport flatness of the canonical
structure to any germ-compatible structure.) -/
theorem isFlat_iff_stalkModule_flat (F : SheafOfModules (structureSheafRing X)) :
    IsFlat F ↔ ∀ x : X.carrier, @Module.Flat _ _ _ _ (stalkModule F x) := by
  constructor
  · intro hF x
    exact hF x (stalkModule F x) (stalkModule_germCompatible F x)
  · intro hF x inst hinst
    -- `inst = stalkModule F x` by uniqueness; transport flatness along that equality.
    have : inst = stalkModule F x :=
      germCompatibleModule_unique F x inst (stalkModule F x) hinst
        (stalkModule_germCompatible F x)
    subst this
    exact hF x

/-- **Statement 1** (Stacks Tag 05NK, extension of flat modules is flat).  Given a short
exact sequence `0 → F₂ → F₁ → F₀ → 0` of sheaves of `O_X`-modules (encoded as a short
complex `S` in the abelian category `SheafOfModules (structureSheafRing X)` together with the
hypothesis `S.ShortExact`), if `S.X₁ = F₂` and `S.X₃ = F₀` are flat then the middle term
`S.X₂ = F₁` is flat.

PROOF.  By `isFlat_iff_stalkModule_flat` it suffices to show, for each `x`, that
the canonical stalk module `(S.X₂)_x` is flat.  By `stalkShortExact` we have a
short exact sequence of `O_{X,x}`-modules `0 → (S.X₁)_x → (S.X₂)_x → (S.X₃)_x → 0`.
By hypotheses `h₂, h₀` (via `isFlat_iff_stalkModule_flat`) the outer modules are
flat, so `Module.Flat.of_shortExact_extension` gives flatness of the middle. -/
@[stacks 05NK "(1)", sga "1 IV 1.1" "(ii) M' flat => M flat"]
theorem isFlat_middle_of_shortExact
    (S : ShortComplex (SheafOfModules (structureSheafRing X)))
    (hS : S.ShortExact) (h₂ : IsFlat S.X₁) (h₀ : IsFlat S.X₃) :
    IsFlat S.X₂ := by
  rw [isFlat_iff_stalkModule_flat]
  intro x
  obtain ⟨f, g, hf, hfg, hg⟩ := stalkShortExact S hS x
  let := stalkModule S.X₁ x
  let := stalkModule S.X₂ x
  let := stalkModule S.X₃ x
  exact Module.Flat.of_shortExact_extension f g hf hfg hg
    ((isFlat_iff_stalkModule_flat S.X₁).mp h₂ x)
    ((isFlat_iff_stalkModule_flat S.X₃).mp h₀ x)

/-- **Statement 2** (Stacks Tag 05NK, kernel of an epimorphism of flat modules is flat).
Given a short exact sequence `0 → F₂ → F₁ → F₀ → 0` of sheaves of `O_X`-modules (encoded as
a short complex `S` with `S.ShortExact`), if `S.X₂ = F₁` and `S.X₃ = F₀` are flat then the
left term `S.X₁ = F₂` is flat.

PROOF.  By `isFlat_iff_stalkModule_flat` it suffices to show `(S.X₁)_x` is flat for
each `x`.  By `stalkShortExact` we have the short exact sequence of stalk modules
`0 → (S.X₁)_x → (S.X₂)_x → (S.X₃)_x → 0`; by `h₁, h₀` the modules `(S.X₂)_x` and
`(S.X₃)_x` are flat, so `Module.Flat.of_shortExact_kernel` gives flatness of
`(S.X₁)_x`. -/
@[stacks 05NK "(2)",
  sga "1 IV 1.1" "(ii) M flat => M' flat",
  sga "4 XVII 4.1.1" "(i), ringed space"]
theorem isFlat_sub_of_shortExact
    (S : ShortComplex (SheafOfModules (structureSheafRing X)))
    (hS : S.ShortExact) (h₁ : IsFlat S.X₂) (h₀ : IsFlat S.X₃) :
    IsFlat S.X₁ := by
  rw [isFlat_iff_stalkModule_flat]
  intro x
  obtain ⟨f, g, hf, hfg, hg⟩ := stalkShortExact S hS x
  let := stalkModule S.X₁ x
  let := stalkModule S.X₂ x
  let := stalkModule S.X₃ x
  exact Module.Flat.of_shortExact_kernel f g hf hfg hg
    ((isFlat_iff_stalkModule_flat S.X₂).mp h₁ x)
    ((isFlat_iff_stalkModule_flat S.X₃).mp h₀ x)

end Stacks.SheafOfModules.FlatShortExact
