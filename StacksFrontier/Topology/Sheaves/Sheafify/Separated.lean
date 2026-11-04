module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Sheafify
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
# Stacks 0082 — a presheaf of sets is separated iff it injects into its sheafification

Let `X` be a topological space. A presheaf of sets `F` on `X` is *separated* (tag 007A) when two
sections over an open `U` that restrict to the same section on each member of an open covering of
`U` are equal. Tag 0082 states that `F` is separated if and only if the canonical morphism
`θ_F : F ⟶ F^#` to its sheafification is injective, meaning injective on sections over every open.

Both notions are spelled here — `IsSeparated` and `MorphismInjective` — in the open-covering
form the tag uses, `IsSeparated` being the cover-form reading of
`CategoryTheory.Presieve.IsSeparated` at the topology of the opens of `X`;
`separated_iff_toSheafify_injective` is the equivalence. The bridge in both directions is
`toSheafify_app_eq_iff_germ_eq`: two sections have
the same image in `F^#(U)` exactly when their germs agree at every point of `U`. Given that,
separatedness is applied to the covering extracted from `TopCat.Presheaf.germ_eq` in one
direction, and a covering is turned into agreement of germs in the other.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe v

variable {X : TopCat.{v}} (F : TopCat.Presheaf (Type v) X)

/--
A presheaf `F` (of sets) on `X` is *separated* if, for every open `U`,
every family of opens `U_i ≤ U` whose supremum is `U`, and every pair
of sections `s, t : F(U)` whose restrictions to each `U i` agree,
we have `s = t`.
-/
@[sga "3 IV 4.3.1" "special case", sga "3 IV 4.3.18" "special case", sga "4 II 2.1" "special case"]
def IsSeparated (F : TopCat.Presheaf (Type v) X) : Prop :=
  ∀ (U : Opens X) (ι : Type v) (U_ : ι → Opens X)
    (hle : ∀ i, U_ i ≤ U) (_ : iSup U_ = U)
    (s t : F.obj (op U)),
      (∀ i, F.map (homOfLE (hle i)).op s = F.map (homOfLE (hle i)).op t) →
      s = t

/--
A morphism of presheaves `φ : F ⟶ G` is *(sectionwise) injective* if
for every open `U`, the component `φ.app (op U) : F(U) → G(U)` is an
injective function.
-/
def MorphismInjective {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  ∀ U : Opens X, Function.Injective (φ.app (op U))

/-- Two sections of `F(U)` have the same image under `toSheafify` iff their
germs agree at every point of `U`. -/
lemma toSheafify_app_eq_iff_germ_eq
    (U : Opens X) (s t : F.obj (op U)) :
    (F.toSheafify.app (op U)) s = (F.toSheafify.app (op U)) t ↔
      ∀ (x : X) (hx : x ∈ U),
        (F.germ U x hx) s = (F.germ U x hx) t :=
  ⟨fun h x hx => congrFun (congrArg Subtype.val h) ⟨x, hx⟩,
    fun h => Subtype.ext (funext fun ⟨x, hx⟩ => h x hx)⟩

/--
**Stacks Project, tag 0082.** Let `F` be a presheaf of sets on a
topological space `X`. Then `F` is separated if and only if the
canonical morphism `θ_F : F ⟶ F^#` to its sheafification is
sectionwise injective.
-/
@[stacks 0082]
theorem separated_iff_toSheafify_injective (F : TopCat.Presheaf (Type v) X) :
    IsSeparated F ↔ MorphismInjective (F.toSheafify) := by
  refine ⟨fun hsep U s t hst => ?_, fun hinj U ι U_ hle hcov s t hrest => ?_⟩
  · -- Forward direction: separated ⇒ sectionwise injective.
    choose V hxV iU iV hres using fun p : {x : X // x ∈ U} =>
      TopCat.Presheaf.germ_eq F p.val p.property p.property s t
        ((toSheafify_app_eq_iff_germ_eq F U s t).mp hst p.val p.property)
    refine hsep U {x : X // x ∈ U} V (fun p => leOfHom (iU p))
      (le_antisymm (iSup_le fun p => leOfHom (iU p))
        fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) s t fun p => ?_
    simpa [Subsingleton.elim (iV p) (iU p),
      Subsingleton.elim (homOfLE (leOfHom (iU p))) (iU p)] using hres p
  · -- Reverse direction: sectionwise injective ⇒ separated.
    refine hinj U ?_
    rw [toSheafify_app_eq_iff_germ_eq]
    intro x hxU
    obtain ⟨i, hxUi⟩ := Opens.mem_iSup.mp (hcov ▸ hxU)
    have h := TopCat.Presheaf.germ_res_apply F (homOfLE (hle i)) x hxUi
    rw [← h s, ← h t, hrest i]

