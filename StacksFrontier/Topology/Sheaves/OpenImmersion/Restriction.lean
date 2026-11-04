module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
public import Mathlib.RingTheory.Radical.NatInt
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
import StacksCore.Tactic.EgaSgaAttribute
/-!
# Stacks 00A1 — restriction of a (pre)sheaf to an open subspace

Stacks 00A1 defines the restriction `G|_U` of a (pre)sheaf on a space `X` to an open subset
`U ⊆ X`, in four settings. All four constructions are given here:

* (1) `restrictPresheaf`, for a presheaf `G` of objects of a category `C`: precomposition with
  the opposite of the open-embedding functor `Opens U ⥤ Opens X`, so `V ↦ G(V)` for `V ⊆ U`;
* (2) `local_restrictSheaf`, for a sheaf: the sheaf pullback
  `Topology.IsOpenEmbedding.sheafPullback` along the inclusion of `U`;
* (3) `openSubspace`, for a ringed space `(X, 𝒪)`: the open subspace with underlying space `U`
  and structure sheaf `𝒪|_U`, obtained from `SheafedSpace.restrict`;
* (4) `restrictPresheafOfModules`, for a presheaf of `𝒪`-modules: the functor
  `PresheafOfModules.pushforward` along the open-embedding functor, landing in presheaves of
  modules over `𝒪|_U`.

Both the sheaf pullback along an open embedding and `PresheafOfModules.pushforward` have
underlying presheaves that are definitionally `restrictPresheaf`, so the comparisons of (2)
and (4) with (1) recorded here are reflexivities.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

/-- Restriction of a presheaf to an open subset: precomposition with the
opposite of the open-embedding functor on opens. -/
@[stacks 00A1 "(1)",
  ega "0 3.1.5",
  sga "3 I 2.1.1" "restriction G ↦ G_S",
  sga "3 IV 4.3.17" "special case"]
def restrictPresheaf
    {C : Type*} [Category C] {X : TopCat}
    (G : TopCat.Presheaf C X) (U : Opens X) :
    TopCat.Presheaf C ((Opens.toTopCat X).obj U) :=
  U.isOpenEmbedding.functor.op ⋙ G

/-- The sections of the restriction `G|_U` over an open `V ⊆ U` are, by definition, the
sections of `G` over the image of `V` in `X`. -/
@[ega "0 3.1.5" "partial"]
theorem restrictPresheaf_obj
    {C : Type*} [Category C] {X : TopCat}
    (G : TopCat.Presheaf C X) (U : Opens X)
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    (restrictPresheaf G U).obj V =
      G.obj (op (U.isOpenEmbedding.functor.obj V.unop)) :=
  rfl

/-- Restriction of a sheaf to an open subset, via the open-embedding sheaf pullback. -/
@[stacks 00A1 "(2)",
  ega "0 3.1.5",
  ega "0 3.7.1" "special case",
  sga "4 III 1.9.2",
  sga "4 III 5.3" "special case"]
noncomputable def local_restrictSheaf
    {A : Type*} [Category A] {X : TopCat}
    (G : TopCat.Sheaf A X) (U : Opens X) :
    TopCat.Sheaf A ((Opens.toTopCat X).obj U) :=
  (Topology.IsOpenEmbedding.sheafPullback A U.isOpenEmbedding).obj G

/-- The underlying presheaf of the restricted sheaf `local_restrictSheaf G U` is isomorphic
to the restricted presheaf `restrictPresheaf G.presheaf U`; the two are definitionally equal,
so the isomorphism is the identity. -/
@[ega "0 3.1.5"]
theorem restrictSheaf_presheaf_iso
    {A : Type*} [Category A] {X : TopCat}
    (G : TopCat.Sheaf A X) (U : Opens X) :
    Nonempty ((local_restrictSheaf G U).presheaf ≅ restrictPresheaf G.presheaf U) :=
  Iso.nonempty_iso_refl _

/-- Open subspace of a ringed space `(X, 𝒪)` associated to an open `U ⊆ X`. -/
@[stacks 00A1 "(3)",
  ega "0 4.1.2" "special case",
  sga "2 I 1.7" "special case",
  sga "4 IV 14.1" "special case"]
noncomputable def openSubspace
    (X : SheafedSpace CommRingCat) (U : Opens X) :
    SheafedSpace CommRingCat :=
  X.restrict U.isOpenEmbedding

/-- The underlying topological space of the open subspace `openSubspace X U` is `U` with its
subspace topology. -/
theorem openSubspace_carrier
    (X : SheafedSpace CommRingCat) (U : Opens X) :
    (openSubspace X U).carrier = (Opens.toTopCat X).obj U :=
  rfl

/-- Restriction of a presheaf of `𝒪`-modules to an open subset, via
`PresheafOfModules.pushforward` along the open-embedding functor. -/
@[stacks 00A1 "(4)",
  sga "3 I 3.1.4" "F ↦ F_U for C = Opens(X)",
  sga "4 IV 11.2.2" "special case",
  sga "4 Vbis 1.3.7" "special case"]
noncomputable def restrictPresheafOfModules
    {X : TopCat} (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat) (U : Opens X) :
    PresheafOfModules 𝒪 ⥤ PresheafOfModules (restrictPresheaf 𝒪 U) :=
  PresheafOfModules.pushforward (F := U.isOpenEmbedding.functor) (𝟙 _)

/-- The underlying presheaf of abelian groups of a restricted presheaf of modules
`(restrictPresheafOfModules 𝒪 U).obj M` is isomorphic to the restriction of the underlying
presheaf of `M`; again the two are definitionally equal. -/
theorem restrictPresheafOfModules_presheaf_iso
    {X : TopCat} (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat)
    (M : PresheafOfModules 𝒪) (U : Opens X) :
    Nonempty (((restrictPresheafOfModules 𝒪 U).obj M).presheaf ≅
      restrictPresheaf M.presheaf U) :=
  Iso.nonempty_iso_refl _

