module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import Mathlib.Topology.Sheaves.Init

/-!
# Every sheaf of sets is covered by sheafified representables

Stacks tag 00WS, narrowed to the substantive first step of the Stacks proof. Call `E ⊆ Ob(C)`
a *covering subset* of a site `(C, J)` if every object admits a `J`-covering sieve all of
whose arrows have domain in `E`. For a sheaf of sets `F` the canonical map
`π : (∐_{(U, s) : E × F(U)} h_U)^♯ ⟶ F` is then locally surjective, hence an epimorphism of
sheaves. The full Stacks statement — that `F` is a coequalizer `F₁ ⇉ F₀ → F` of two
coproducts of sheafified representables `h_U^♯` with `U ∈ E` — follows by applying tag 086K
to `π` and to the analogous epimorphism onto the kernel pair `F₀ ×_F F₀`.
-/

@[expose] public section

open CategoryTheory Limits Opposite


universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Stacks.Sites.CoveredByRepresentables

/-- The Stacks notion of *covering subset*: `E ⊆ Ob(C)` is a covering subset of
the site `(C, J)` if every object `V` admits a `J`-covering sieve all of whose
arrows have domain in `E`. -/
def IsCoveringSubset (E : Set C) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (f : W ⟶ V), S f → W ∈ E

/-- The indexing type for the coproduct presentation of `F00WS`: pairs `(U, s)`
where `U` is an object of the site lying in the covering subset `E`, and `s` is
a section of `F00WS` over `U`. -/
def index (E : Set C) (F00WS : Sheaf J (Type max v u)) : Type max v u :=
  Σ U : E, F00WS.obj.obj (op U.val)

/-- The component presheaf at index `(U, s)`: the universe-lifted representable
`y(U)` valued in `Type max v u`. -/
noncomputable def indexFamilyPre (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    index J E F00WS → (Cᵒᵖ ⥤ Type max v u) :=
  fun p => uliftYoneda.{u}.obj p.1.val

/-- The presheaf coproduct `P = ∐_{(U,s) ∈ E × F00WS(U)} y(U)`. -/
noncomputable def P (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    Cᵒᵖ ⥤ Type max v u :=
  ∐ indexFamilyPre J E F00WS

/-- The presheaf-level map `P ⟶ F00WS.obj`: on the `(U, s)` component, the Yoneda
map sending `id_U ↦ s`. -/
noncomputable def πPre (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    P J E F00WS ⟶ F00WS.obj :=
  Sigma.desc (fun p => uliftYonedaEquiv.{u}.symm p.2)

/-- The defining equation of `πPre` as a `Sigma.desc`: its restriction to the `(U, s)` summand
of `P` is the Yoneda transpose `id_U ↦ s` of the section `s`.  Evaluating it at `ULift.up (𝟙 U)`
is `πPre_app_of_ι`, the local surjectivity witness. -/
lemma ι_πPre {E : Set C} {F00WS : Sheaf J (Type max v u)}
    (p : index J E F00WS) :
    Sigma.ι (indexFamilyPre J E F00WS) p ≫ πPre J E F00WS =
      uliftYonedaEquiv.{u}.symm p.2 := by
  unfold πPre
  exact Sigma.ι_comp_desc _ _

/-- Pointwise computation of the cocone-leg-then-`πPre` composite on identity:
the `(U, s)` leg sends `ULift.up (𝟙 U)` to `s`. -/
lemma πPre_app_of_ι (E : Set C) (F00WS : Sheaf J (Type max v u))
    (U : E) (s : F00WS.obj.obj (op U.val)) :
    (πPre J E F00WS).app (op U.val)
        ((Sigma.ι (indexFamilyPre J E F00WS) ⟨U, s⟩).app (op U.val)
          (ULift.up (𝟙 U.val))) = s := by
  -- The composite `Sigma.ι _ ⟨U, s⟩ ≫ πPre = uliftYonedaEquiv.symm s` on
  -- `ULift.up (𝟙 U)` evaluates to `F00WS.obj.map (𝟙 _).op s = s`.
  have hcomp := ι_πPre (J := J) (E := E) (F00WS := F00WS) ⟨U, s⟩
  -- Rewrite the LHS via the composite identity, then evaluate `yoneda.symm`.
  change (Sigma.ι (indexFamilyPre J E F00WS) ⟨U, s⟩ ≫ πPre J E F00WS).app (op U.val)
      (ULift.up (𝟙 U.val)) = s
  rw [hcomp]
  -- The remaining goal is `F00WS.obj.map (𝟙 U).op s = s`.
  change F00WS.obj.map (𝟙 U.val).op s = s
  simp

/-- The presheaf coproduct map `πPre` is locally surjective: for every section
`s` of `F00WS` over any object `V`, the cover of `V` by elements of `E` from the
hypothesis `IsCoveringSubset J E` lifts each restriction of `s` into the image
of `πPre`. This is the substantive first step of the Stacks 00WS proof. -/
lemma isLocallySurjective_πPre {E : Set C} (hE : IsCoveringSubset J E)
    (F00WS : Sheaf J (Type max v u)) :
    Presheaf.IsLocallySurjective J (πPre J E F00WS) := by
  refine ⟨?_⟩
  intro V s
  -- Cover `V` by elements of `E`.
  obtain ⟨S, hSJ, hSE⟩ := hE V
  refine J.superset_covering (S := S) ?_ hSJ
  intro W f hf
  -- The arrow `f : W ⟶ V.unop` has `W ∈ E`, so `(⟨W, _⟩, F00WS.obj.map f.op s)` is
  -- a valid index. The image of `ULift.up (𝟙 W)` under the corresponding
  -- inclusion is a preimage of `F00WS.obj.map f.op s` under `πPre`.
  have hWE : W ∈ E := hSE f hf
  set p : index J E F00WS := ⟨⟨W, hWE⟩, F00WS.obj.map f.op s⟩ with hp
  refine ⟨(Sigma.ι (indexFamilyPre J E F00WS) p).app (op W) (ULift.up (𝟙 W)), ?_⟩
  -- The required equality reduces to `πPre_app_of_ι`.
  have h := πPre_app_of_ι (J := J) (E := E) (F00WS := F00WS) ⟨W, hWE⟩ (F00WS.obj.map f.op s)
  -- `s` is meant in the codomain `F00WS.obj.obj V`; we need the image of `id`
  -- under the inclusion-then-`πPre` to equal `F00WS.obj.map f.op s`.
  -- The naturality identity for `πPre` then upgrades pointwise to a
  -- presheaf-level statement.
  -- Concretely: the goal is
  --   (πPre J E F00WS).app (op W) ((Sigma.ι _ p).app (op W) (ULift.up (𝟙 W)))
  --     = F00WS.obj.map f.op s
  -- which is exactly `h`.
  exact h

/-- The sheafification `F00WS₀ = a(P)` of the presheaf coproduct: by construction
this is a coproduct of sheafified representable sheaves
`h_U^# = a(y(U))` indexed by `E × F00WS(U)`. -/
noncomputable def F00WS₀ (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    Sheaf J (Type max v u) :=
  (presheafToSheaf J (Type max v u)).obj (P J E F00WS)

/-- The canonical sheafification of `πPre` to a sheaf morphism `F00WS₀ ⟶ F00WS`,
obtained from the sheafification adjunction. -/
noncomputable def π (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    F00WS₀ J E F00WS ⟶ F00WS :=
  ((sheafificationAdjunction J (Type max v u)).homEquiv _ F00WS).symm (πPre J E F00WS)

/-- **Stacks 00WS** (narrowed to the substantive first step of the Stacks
proof). Let `J` be a Grothendieck topology on `C`, let `E ⊆ Ob(C)` be a
covering subset of the site (Definition `IsCoveringSubset`), and let `F00WS` be a
sheaf of sets on `C`.

Then the canonical map
`π : F00WS₀ := a(∐_{(U, s) : E × F00WS(U)} y(U)) ⟶ F00WS`
into `F00WS` is an *epimorphism* in `Sheaf J (Type max v u)`, where `a` denotes
sheafification. Equivalently, `π` is locally surjective.

The full Stacks 00WS statement — that `F00WS` is a coequalizer
`F00WS₁ ⇉ F00WS₀ → F00WS` of two such coproducts — follows by combining this lemma with
Stacks 086K applied to `π` (existence of `F00WS₁`) and to the analogous epimorphism
onto the kernel pair `F00WS₀ ×_F F00WS₀` (faithfulness of the coequalizer cofork). -/
@[stacks 00WS]
theorem isLocallySurjective_π {E : Set C} (hE : IsCoveringSubset J E)
    (F00WS : Sheaf J (Type max v u)) :
    Sheaf.IsLocallySurjective (π J E F00WS) := by
  -- The composite `(presheafToSheaf).map πPre ≫ counit` equals `πPre`
  -- *postcomposed* with the sheafification of `F00WS.obj`, after passing through
  -- the unit of the adjunction. We reduce local surjectivity of `π` to local
  -- surjectivity of the presheaf map `πPre` via
  -- `isLocallySurjective_presheafToSheaf_map_iff`.
  have hPre : Presheaf.IsLocallySurjective J (πPre J E F00WS) :=
    isLocallySurjective_πPre J hE F00WS
  -- The sheafified map is locally surjective.
  have h1 : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type max v u)).map (πPre J E F00WS)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff (J := J)
      (φ := πPre J E F00WS)).mpr hPre
  -- Convert local surjectivity to epi, then conclude.
  have hEpi1 : Epi ((presheafToSheaf J (Type max v u)).map (πPre J E F00WS)) :=
    Sheaf.epi_of_isLocallySurjective _
  -- The counit is iso, hence epi.
  have hCoIso : IsIso ((sheafificationAdjunction J (Type max v u)).counit.app F00WS) :=
    inferInstance
  have hCoEpi : Epi ((sheafificationAdjunction J (Type max v u)).counit.app F00WS) :=
    IsIso.epi_of_iso _
  -- `π` equals the composition; the composition is epi, hence locally surjective.
  have hpi_eq : π J E F00WS =
      (presheafToSheaf J (Type max v u)).map (πPre J E F00WS) ≫
        (sheafificationAdjunction J (Type max v u)).counit.app F00WS := by
    rfl
  rw [hpi_eq]
  have hCompEpi : Epi ((presheafToSheaf J (Type max v u)).map (πPre J E F00WS) ≫
      (sheafificationAdjunction J (Type max v u)).counit.app F00WS) :=
    @epi_comp _ _ _ _ _
      ((presheafToSheaf J (Type max v u)).map (πPre J E F00WS)) hEpi1
      ((sheafificationAdjunction J (Type max v u)).counit.app F00WS) hCoEpi
  -- Use `Sheaf.isLocallySurjective_iff_epi.mpr`.
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr hCompEpi

end Stacks.Sites.CoveredByRepresentables

