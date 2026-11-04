module
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The image of a morphism of sites covers the final object

Let `f : D → C` be a morphism of sites (Stacks 00X1): a continuous functor `u : C ⥤ D` in the
opposite direction whose induced functor on sheaves of sets `f⁻¹ = u_s : Sh(C) ⥤ Sh(D)` — the
left adjoint of `f_* = u^s` — is exact. Stacks 08H2 says that the site `D` is, locally, in the
image of `u`: every object `V` of `D` admits a covering `{V_j → V}` such that each `V_j` carries
a morphism `V_j ⟶ u U_j` for some object `U_j` of `C`. Equivalently, the family of objects
`(u U)_{U : C}` covers the final object of `Sh(D)`.

Only one consequence of exactness is used, the one the source's proof opens with: `u_s` carries
the final sheaf `*` of `Sh(C)` to the final sheaf of `Sh(D)`. Indeed `u_s = # ∘ u_p`, and
`(u_p *)(V)` is a colimit over the category `I^u_V` of morphisms `V ⟶ u U`, so it is nonempty
precisely when some morphism `V ⟶ u U` exists; a section of a sheafification exists locally, so
the unique section of `u_s *` over `V` produces a covering of `V` by objects admitting such a
morphism. So the lemma is stated for a continuous `u` whose `u_s` merely preserves the final
object, which is strictly weaker than being a morphism of sites.

The hypothesis cannot be dropped: the source remarks before this lemma that the conclusion may
fail for a functor that is only continuous.

## Main results

* `CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback`
  (Stacks 08H2): if `u : C ⥤ D` is continuous and `u_s = u.sheafPullback (Type u) J K` preserves
  the final object, then the objects `u U`, for `U` an object of `C`, cover the final object of
  `Sh(D)`, i.e. for every `V : D` the sieve of morphisms `W ⟶ V` whose source `W` admits a
  morphism to some `u U` is a `K`-covering sieve.

## Implementation notes

* The conclusion is `K.CoversTop u.obj` (`CategoryTheory.GrothendieckTopology.CoversTop`), which
  unfolds to: for every `V : D` the sieve `CategoryTheory.Sieve.ofObjects u.obj V`, whose arrows
  are the `g : W ⟶ V` such that `W ⟶ u U` for some `U : C`, lies in `K V`. This is equivalent to
  the source's formulation with a covering family: a covering family `{V_j → V}` with morphisms
  `V_j ⟶ u U_j` generates a sieve contained in `Sieve.ofObjects u.obj V`, so the latter is a
  covering sieve as well; conversely the arrows of that sieve are such a family. Pinning the
  maximal such sieve rather than asserting a family to exist is what makes the statement usable
  without choice, and the source's `{V_j → V}` is recovered from it.
* The hypothesis is `u_s` preserving the final object rather than `u_s` being exact, this being
  the sharp form of what the source's proof uses. A morphism of sites in this repository's sense,
  `CategoryTheory.Functor.IsMorphismOfSites u J K` (Stacks 00X1, in
  `StacksFrontier/CategoryTheory/Sites/MorphismOfSites.lean`), supplies both hypotheses of the
  present statement: `hu.isContinuous`, and `hu.preservesFiniteLimits`, whose special case at the
  empty diagram is `Limits.PreservesLimit (Functor.empty.{0} _)`.
* `u_s` is `CategoryTheory.Functor.sheafPullback (Type u) J K`, Mathlib's left adjoint of the
  pushforward `u^s = CategoryTheory.Functor.sheafPushforwardContinuous`; sheaves of sets and small
  sites are the setting of Definition 00X1 and of `Functor.IsMorphismOfSites`.
* The morphism `f` itself does not appear: a morphism of sites is given by the functor `u`, and
  both hypothesis and conclusion are conditions on `u`.

## References

* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

namespace CategoryTheory.GrothendieckTopology

section

universe u v u₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.Sites.ImageCoversTop

section OfObjects

variable {D : Type u₂} [Category.{v} D] (K : GrothendieckTopology D)

/-- The subterminal presheaf of sets on `D` attached to a family of objects `Y : I → D`: a section
over `V` is a witness that `V` admits a morphism to some `Y i`, and there is at most one such
section. Its restriction maps exist for the same reason that `CategoryTheory.Sieve.ofObjects Y V`
is a sieve: the condition depends on the source object only and is stable under precomposition.
The arrows of `Sieve.ofObjects Y V` are exactly the `g : W ⟶ V` for which this presheaf is nonempty
at `W`. -/
@[sga "3 IV 4.1.1" "special case",
  sga "3 IV 4.1.2" "special case",
  sga "4 I 4.3.3" "special case",
  sga "4 IV 8.1.1"]
private def ofObjectsSubfunctor {I : Type*} (Y : I → D) :
    Subfunctor ((Functor.const Dᵒᵖ).obj PUnit.{v + 1})
    where
  obj V := {_x | ∃ i, Nonempty (V.unop ⟶ Y i)}
  map {_ _} f := by
    rintro x ⟨i, ⟨g⟩⟩
    exact ⟨i, ⟨f.unop ≫ g⟩⟩

/-- `Stacks.Sites.ImageCoversTop.ofObjectsSubfunctor Y` as a presheaf of types. -/
private abbrev ofObjectsPresheaf {I : Type*} (Y : I → D) : Dᵒᵖ ⥤ Type v :=
  (ofObjectsSubfunctor Y).toFunctor

/-- A section of `Stacks.Sites.ImageCoversTop.ofObjectsPresheaf Y` over `V` is a witness that `V`
admits a morphism to some `Y i`; this is the whole content of that presheaf. -/
private lemma exists_nonempty_hom_of_ofObjectsPresheaf {I : Type*} {Y : I → D} {V : D}
    (x : (ofObjectsPresheaf Y).obj (op V)) : ∃ i, Nonempty (V ⟶ Y i) :=
  x.2

/-- **The step that carries Stacks 08H2.** Let `f : P ⟶ G` be a locally surjective morphism of
presheaves of sets on `D`, and suppose that `P` has a section over an object only if that object
admits a morphism to some `Y i`. Then the objects `Y i` cover every object over which `G` has a
section.

Indeed, a section `s` of `G` over `V` is locally in the image of `P`, so the arrows `g : W ⟶ V`
along which `s` restricts into the image of `P` form a covering sieve of `V`; each such `W` carries
a section of `P`, hence a morphism to some `Y i`, so that sieve is contained in
`Sieve.ofObjects Y V`, which is therefore covering as well. -/
private lemma ofObjects_mem_of_isLocallySurjective {I : Type*} {Y : I → D} {P G : Dᵒᵖ ⥤ Type v}
    (f : P ⟶ G) [Presheaf.IsLocallySurjective K f]
    (hP : ∀ {W : D}, P.obj (op W) → ∃ i, Nonempty (W ⟶ Y i)) {V : D} (s : G.obj (op V)) :
    Sieve.ofObjects Y V ∈ K V := by
  refine K.superset_covering ?_ (Presheaf.imageSieve_mem K f s)
  rintro W g ⟨t, -⟩
  exact hP t

end OfObjects

section

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- If the sheafification of `Q` is the final sheaf on `D`, then the sheafification of any presheaf
`P` receiving a morphism from `Q` has a section over every object: the final sheaf has a section
over every object, and the morphism `Q ⟶ P ⟶ P^#` is adjoint to a morphism of sheaves `Q^# ⟶ P^#`
carrying it to one of `P^#`. -/
private lemma nonempty_sheafify_obj_of_isTerminal_sheafify {Q P : Dᵒᵖ ⥤ Type u} (f : Q ⟶ P)
    (h : IsTerminal ((presheafToSheaf K (Type u)).obj Q)) (V : Dᵒᵖ) :
    Nonempty ((K.sheafify P).obj V) :=
  ⟨(h.from (Sheaf.terminal K Types.isTerminalPUnit) ≫
          ((sheafificationAdjunction K (Type u)).homEquiv Q
                ⟨K.sheafify P, K.sheafify_isSheaf P⟩).symm
            (f ≫ K.toSheafify P)).hom.app
      V PUnit.unit⟩

/-- The section of `Stacks.Sites.ImageCoversTop.ofObjectsPresheaf u.obj` over `u U` given by the
identity of `u U`, for every object `U` of `C`: a morphism `* ⟶ u^p P` from the final presheaf of
sets on `C`. Naturality is a definitional identity: `P` is a subfunctor of the final presheaf, so
its restriction maps do not move the underlying element, and its defining condition is a
proposition. -/
private def constToOfObjectsPresheaf :
    (Functor.const Cᵒᵖ).obj PUnit.{u + 1} ⟶ u.op ⋙ ofObjectsPresheaf u.obj
    where
  app U := ↾fun _ ↦ ⟨PUnit.unit, ⟨U.unop, ⟨𝟙 _⟩⟩⟩
  naturality _ _ _ := rfl

/-- The morphism `u_p * ⟶ P` adjoint to `Stacks.Sites.ImageCoversTop.constToOfObjectsPresheaf`,
where `u_p` is the pullback of presheaves `u.op.lan` and `P` is
`Stacks.Sites.ImageCoversTop.ofObjectsPresheaf u.obj`. -/
private noncomputable def lanConstToOfObjectsPresheaf :
    u.op.lan.obj ((Functor.const Cᵒᵖ).obj PUnit.{u + 1}) ⟶ ofObjectsPresheaf u.obj :=
  ((u.op.lanAdjunction (Type u)).homEquiv _ _).symm (constToOfObjectsPresheaf u)

/-- **The hypothesis of Stacks 08H2, unwound.** If `u_s = u.sheafPullback (Type u) J K` preserves
the final object, then the sheafification of `u_p *` is the final sheaf on `D`: it is the value of
`u_s` at the final sheaf `*` of `Sh(C)`, up to the comparison
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso` of `u_s` with `# ∘ u_p`. -/
private noncomputable def isTerminalSheafifyLanConst [u.IsContinuous J K]
    [PreservesLimit (Functor.empty.{0} (Sheaf J (Type u))) (u.sheafPullback (Type u) J K)] :
    IsTerminal
      ((presheafToSheaf K (Type u)).obj (u.op.lan.obj ((Functor.const Cᵒᵖ).obj PUnit.{u + 1}))) :=
  ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj (u.sheafPullback (Type u) J K)
        _).ofIso
    ((Functor.sheafPullbackConstruction.sheafPullbackIso u (Type u) J K).app
      (Sheaf.terminal J Types.isTerminalPUnit))

end

end Stacks.Sites.ImageCoversTop

@[expose] public section

open Stacks.Sites.ImageCoversTop in
/-- **Stacks 08H2.** Let `u : C ⥤ D` be a continuous functor of sites, giving a morphism of sites
`f : D → C`, and assume that `f⁻¹ = u_s : Sh(C) ⥤ Sh(D)` preserves the final object (as it does
when `u_s` is exact, i.e. when `u` defines a morphism of sites, Stacks 00X1). Then the objects
`u U`, for `U` an object of `C`, cover the final object of `Sh(D)`: for every object `V` of `D`
there is a covering `{V_j → V}` such that every `V_j` admits a morphism `V_j ⟶ u U_j` to the
image of some object `U_j` of `C`. -/
@[stacks 08H2 "For a morphism of sites f : D → C given by u : C ⥤ D, every object V of D has a
covering {V_j → V} such that each V_j admits a morphism V_j ⟶ u(U_j) for some object U_j of C."]
public theorem coversTop_obj_of_preservesTerminal_sheafPullback {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K]
    [PreservesLimit (Functor.empty.{0} (Sheaf J (Type u))) (u.sheafPullback (Type u) J K)] :
    K.CoversTop u.obj := by
  intro V
  exact
    ofObjects_mem_of_isLocallySurjective K (K.toSheafify (ofObjectsPresheaf u.obj))
      exists_nonempty_hom_of_ofObjectsPresheaf
      (nonempty_sheafify_obj_of_isTerminal_sheafify K (lanConstToOfObjectsPresheaf u)
          (isTerminalSheafifyLanConst u J K) (op V)).some

end

end

end CategoryTheory.GrothendieckTopology
