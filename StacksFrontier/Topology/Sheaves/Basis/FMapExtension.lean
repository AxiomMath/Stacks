module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
# Stacks tag 009X — Unique f-map between sheaves of algebraic structures from compatible
morphisms on bases

Let `f : X ⟶ Y` be a continuous map of topological spaces, let `(C, F)` be a "type of
algebraic structures" (a concrete category with all limits whose forgetful functor
preserves limits and reflects isomorphisms). Let `F` be a sheaf on `X` with values in
`C`, and `G` a sheaf on `Y` with values in `C`. Let `BX`, `BY` be bases of the
topologies of `X`, `Y`.

An *f-map* `φ : G ⟶ f_*F` is a morphism of presheaves on `Y`.

A *compatible basis family* consists of morphisms `Φ.φ V hV U hU hfU : G(V) ⟶ F(U)`
for every `V ∈ BY`, `U ∈ BX` with `U ≤ f⁻¹V`, compatible with the restriction maps
of both `G` and `F`.

**Theorem.** Given a compatible basis family, there is a unique `f`-map `φ : G ⟶ f_*F`
such that for every basis pair `(V, U)`,
  `Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.val.map (homOfLE hfU).op`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat Opposite Limits


universe w v u

/-- An `f`-map from `G` to `F` is a morphism of presheaves on `Y` from `G` to the
pushforward `f_*F`. -/
@[ega "0 3.5.1" "special case", sga "4 XVII 0.2.1" "(ii), special case"]
abbrev FMapValPresheaf (C : Type u) [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) : Type _ :=
  G.obj ⟶ (TopCat.Presheaf.pushforward C f).obj F.obj

/-- A compatible family of morphisms on the bases `(BX, BY)`: for every basis pair
`(V, U)` with `V ∈ BY`, `U ∈ BX` and `U ≤ f⁻¹V`, a morphism
`G(V) ⟶ F(U)` compatible with the restrictions of `G` and `F`. -/
structure CompatibleBasisFamily (C : Type u) [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y)
    (BX : Set (Opens X)) (BY : Set (Opens Y)) where
  φ : ∀ (V : Opens Y) (_ : V ∈ BY) (U : Opens X) (_ : U ∈ BX)
        (_ : U ≤ (Opens.comap f.hom) V),
      G.obj.obj (op V) ⟶ F.obj.obj (op U)
  compat : ∀ (V V' : Opens Y) (hV : V ∈ BY) (hV' : V' ∈ BY) (hVV' : V' ≤ V)
            (U U' : Opens X) (hU : U ∈ BX) (hU' : U' ∈ BX) (hUU' : U' ≤ U)
            (hfU : U ≤ (Opens.comap f.hom) V) (hfU' : U' ≤ (Opens.comap f.hom) V'),
    φ V hV U hU hfU ≫ F.obj.map (homOfLE hUU').op
      = G.obj.map (homOfLE hVV').op ≫ φ V' hV' U' hU' hfU'

section CoverLemmas

/-- A family of opens `S ⊆ Opens X` with `sSup S = W` gives a covering sieve in
`Opens.grothendieckTopology X`. -/
@[sga "4 III 1.9.1" "partial",
  sga "4½ Arcata 1.1" "sufficient direction",
  sga "4½ Arcata 1.6.4" "partial"]
lemma cover_of_sSup_of_opens {X : TopCat.{w}} (W : Opens X) (S : Set (Opens X))
    (hcov : sSup S = W) :
    Sieve.generate (fun {V : Opens X} (_ : V ⟶ W) => V ∈ S ∧ V ≤ W)
      ∈ (Opens.grothendieckTopology X).sieves W := by
  intro x hxW
  rw [← hcov] at hxW
  obtain ⟨U, hUS, hxU⟩ := (Opens.mem_sSup).mp hxW
  have hle : U ≤ W := hcov ▸ le_sSup hUS
  exact ⟨U, homOfLE hle, ⟨U, 𝟙 U, homOfLE hle, ⟨hUS, hle⟩, by simp⟩, hxU⟩

/-- Hom-ext for a sheaf on `X` using a `sSup` cover: if two morphisms into
`F(W)` agree after composing with the restriction to every member of a family
of opens whose supremum is `W`, then they are equal. -/
lemma sheaf_hom_ext_of_supr_cover
    {X : TopCat.{w}} {C : Type u} [Category.{v} C] [HasLimits C]
    (F : TopCat.Sheaf C X) (W : Opens X) (S : Set (Opens X)) (hcov : sSup S = W)
    {T : C} (s₁ s₂ : T ⟶ F.obj.obj (op W))
    (h : ∀ U ∈ S, ∀ (hU : U ≤ W),
      s₁ ≫ F.obj.map (homOfLE hU).op = s₂ ≫ F.obj.map (homOfLE hU).op) :
    s₁ = s₂ := by
  set P : Presieve W := fun {V : Opens X} (_ : V ⟶ W) => V ∈ S ∧ V ≤ W
  have hRcov : Sieve.generate P ∈ (Opens.grothendieckTopology X).sieves W :=
    cover_of_sSup_of_opens W S hcov
  refine F.property.hom_ext ⟨Sieve.generate P, hRcov⟩ s₁ s₂ ?_
  rintro ⟨V, fVW, hf⟩
  obtain ⟨U, g, fUW, ⟨hUS, hUW⟩, rfl⟩ := hf
  have hfUW : fUW = homOfLE hUW := rfl
  simp only [op_comp, F.obj.map_comp]
  have key : s₁ ≫ F.obj.map fUW.op = s₂ ≫ F.obj.map fUW.op := by
    rw [hfUW]; exact h U hUS hUW
  rw [← Category.assoc, ← Category.assoc, key]

/-- The basis-element subset is a cover: if `BX` is a basis of the topology on `X`
and `W : Opens X`, the family of basis elements contained in `W` has supremum `W`. -/
lemma sSup_basis_le {X : TopCat.{w}} {BX : Set (Opens X)}
    (hBX : Opens.IsBasis BX) (W : Opens X) :
    sSup {U : Opens X | U ∈ BX ∧ U ≤ W} = W := by
  refine le_antisymm (sSup_le fun U hU => hU.2) fun x hx => ?_
  rw [Opens.isBasis_iff_nbhd] at hBX
  obtain ⟨U', hU'B, hxU', hU'W⟩ := hBX hx
  exact Opens.mem_sSup.mpr ⟨U', ⟨hU'B, hU'W⟩, hxU'⟩

end CoverLemmas

section Uniqueness

variable (C : Type u) [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} C FC]
  [HasLimits C]
  [PreservesLimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y)
variable (BX : Set (Opens X)) (BY : Set (Opens Y))

/-- **Uniqueness on basis opens of `Y`.** Two `f`-maps that agree with `Φ` on every
basis pair must agree at every basis open `V ∈ BY`. -/
lemma app_eq_on_basis_open
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (φ φ' : FMapValPresheaf C f F G)
    (hφ : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.obj.map (homOfLE hfU).op)
    (hφ' : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ'.app (op V) ≫ F.obj.map (homOfLE hfU).op)
    (V : Opens Y) (hV : V ∈ BY) :
    φ.app (op V) = φ'.app (op V) := by
  let _ := hBY
  refine sheaf_hom_ext_of_supr_cover F ((Opens.comap f.hom) V)
      {U : Opens X | U ∈ BX ∧ U ≤ (Opens.comap f.hom) V}
      (sSup_basis_le hBX ((Opens.comap f.hom) V)) _ _ ?_
  rintro U ⟨hU, _⟩ hUfV
  exact (hφ V hV U hU hUfV).symm.trans (hφ' V hV U hU hUfV)

/-- **Uniqueness on arbitrary opens of `Y`.** Two `f`-maps that agree with `Φ` on
every basis pair must agree at every open `W : Opens Y`. -/
@[ega "0 3.2.5" "uniqueness", ega "0 3.5.1" "partial", ega "0 4.4.1" "partial"]
lemma app_eq_on_open
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (φ φ' : FMapValPresheaf C f F G)
    (hφ : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.obj.map (homOfLE hfU).op)
    (hφ' : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ'.app (op V) ≫ F.obj.map (homOfLE hfU).op)
    (W : Opens Y) :
    φ.app (op W) = φ'.app (op W) := by
  let F' : TopCat.Sheaf C Y := (TopCat.Sheaf.pushforward C f).obj F
  apply sheaf_hom_ext_of_supr_cover F' W
      {V : Opens Y | V ∈ BY ∧ V ≤ W}
      (sSup_basis_le hBY W)
  rintro V ⟨hV, _⟩ hVW
  have natφ := φ.naturality (homOfLE hVW).op
  have natφ' := φ'.naturality (homOfLE hVW).op
  simp only [F', TopCat.Sheaf.pushforward_obj_val]
  rw [← natφ, ← natφ']
  congr 1
  exact app_eq_on_basis_open C f F G BX BY hBX hBY Φ φ φ' hφ hφ' V hV

/-- **Uniqueness of the `f`-map.** -/
@[ega "0 3.2.5" "uniqueness", ega "0 3.5.1" "partial", ega "0 4.4.1" "partial"]
lemma fmap_eq_of_basis
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (φ φ' : FMapValPresheaf C f F G)
    (hφ : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.obj.map (homOfLE hfU).op)
    (hφ' : ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
            (hfU : U ≤ (Opens.comap f.hom) V),
            Φ.φ V hV U hU hfU = φ'.app (op V) ≫ F.obj.map (homOfLE hfU).op) :
    φ = φ' := by
  ext W
  rcases W with ⟨W⟩
  exact app_eq_on_open C f F G BX BY hBX hBY Φ φ φ' hφ hφ' W

end Uniqueness

section Existence

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} C FC]
  [HasLimits C]
  [PreservesLimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{w}} {f : X ⟶ Y}
variable {F : TopCat.Sheaf C X} {G : TopCat.Sheaf C Y}
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}

/-- Compatibility of `Φ.φ V hV` viewed as a family on the basis cover of `f⁻¹V`:
for any open `W` of `X` and two factorizations `W → U` and `W → U'` through basis
opens `U, U' ∈ BX` with `U, U' ≤ f⁻¹V`, the induced maps `G(V) → F(W)` agree. -/
lemma Phi_compat_on_inter
    (hBX : Opens.IsBasis BX)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (V : Opens Y) (hV : V ∈ BY)
    (W : Opens X) (U U' : Opens X) (hU : U ∈ BX) (hU' : U' ∈ BX)
    (hWU : W ≤ U) (hWU' : W ≤ U')
    (hfU : U ≤ (Opens.comap f.hom) V) (hfU' : U' ≤ (Opens.comap f.hom) V) :
    Φ.φ V hV U hU hfU ≫ F.obj.map (homOfLE hWU).op
      = Φ.φ V hV U' hU' hfU' ≫ F.obj.map (homOfLE hWU').op := by
  apply sheaf_hom_ext_of_supr_cover F W
      {V' : Opens X | V' ∈ BX ∧ V' ≤ W} (sSup_basis_le hBX W)
  rintro V₀ ⟨hV₀B, hV₀W⟩ _
  have hfV₀ : V₀ ≤ (Opens.comap f.hom) V := (hV₀W.trans hWU).trans hfU
  have key : ∀ (U : Opens X) (hU : U ∈ BX) (hWU : W ≤ U) (hfU : U ≤ (Opens.comap f.hom) V),
      (Φ.φ V hV U hU hfU ≫ F.obj.map (homOfLE hWU).op) ≫ F.obj.map (homOfLE hV₀W).op
        = Φ.φ V hV V₀ hV₀B hfV₀ := by
    intro U hU hWU hfU
    have e := Φ.compat V V hV hV (le_refl V) U V₀ hU hV₀B (hV₀W.trans hWU) hfU hfV₀
    rw [Category.assoc, ← F.obj.map_comp]
    exact e.trans (by simp)
  rw [key U hU hWU hfU, key U' hU' hWU' hfU']

/-- For each basis `V ∈ BY`, the component `G(V) ⟶ F(f⁻¹V)` obtained by amalgamating
the basis family `Φ.φ V hV _ _ _` on the basis cover of `f⁻¹V`. -/
noncomputable def appOnBasis
    (hBX : Opens.IsBasis BX)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (V : Opens Y) (hV : V ∈ BY) :
    G.obj.obj (op V) ⟶ F.obj.obj (op ((Opens.comap f.hom) V)) := by
  refine F.property.amalgamateOfArrows
    (S := (Opens.comap f.hom) V)
    (I := {U : Opens X // U ∈ BX ∧ U ≤ (Opens.comap f.hom) V})
    (X := fun U => U.1)
    (f := fun ⟨_, _, hfU⟩ => homOfLE hfU)
    ?_
    (fun ⟨U, hU, hfU⟩ => Φ.φ V hV U hU hfU)
    ?_
  · -- The family is a cover.
    intro x hxW
    have hcov := sSup_basis_le hBX ((Opens.comap f.hom) V)
    rw [← hcov] at hxW
    obtain ⟨U', ⟨hU'mem, hxU'⟩⟩ := Opens.mem_sSup.mp hxW
    -- We need to exhibit membership in `Sieve.generate (Presieve.ofArrows _ _)`.
    refine ⟨U', homOfLE hU'mem.2, ?_, hxU'⟩
    refine ⟨U', 𝟙 _, homOfLE hU'mem.2, ?_, by simp⟩
    exact Presieve.ofArrows.mk (⟨U', hU'mem⟩ :
      {U : Opens X // U ∈ BX ∧ U ≤ (Opens.comap f.hom) V})
  · -- Compatibility of the family on overlaps.
    rintro W ⟨U, hUB, hUf⟩ ⟨U', hU'B, hU'f⟩ a b _
    have hWU : W ≤ U := leOfHom a
    have hWU' : W ≤ U' := leOfHom b
    exact Phi_compat_on_inter hBX Φ V hV W U U' hUB hU'B hWU hWU' hUf hU'f

/-- The defining property of `appOnBasis`: restricting along an inclusion
`U ⟶ f⁻¹V` from a basis `U ∈ BX` recovers `Φ.φ V hV U hU hfU`. -/
lemma appOnBasis_restrict
    (hBX : Opens.IsBasis BX)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (V : Opens Y) (hV : V ∈ BY)
    (U : Opens X) (hU : U ∈ BX) (hfU : U ≤ (Opens.comap f.hom) V) :
    appOnBasis hBX Φ V hV ≫ F.obj.map (homOfLE hfU).op
      = Φ.φ V hV U hU hfU := by
  unfold appOnBasis
  exact F.property.amalgamateOfArrows_map
    (X := fun U : {U : Opens X // U ∈ BX ∧ U ≤ (Opens.comap f.hom) V} => U.1)
    (f := fun ⟨_, _, hfU⟩ => homOfLE hfU) _
    (fun ⟨U, hU, hfU⟩ => Φ.φ V hV U hU hfU) _ ⟨U, hU, hfU⟩

/-- Naturality of `appOnBasis` for inclusions of basis opens in `BY`. -/
lemma appOnBasis_naturality
    (hBX : Opens.IsBasis BX)
    (Φ : CompatibleBasisFamily C f F G BX BY)
    (V V' : Opens Y) (hV : V ∈ BY) (hV' : V' ∈ BY) (hVV' : V' ≤ V) :
    G.obj.map (homOfLE hVV').op ≫ appOnBasis hBX Φ V' hV'
      = appOnBasis hBX Φ V hV ≫
          F.obj.map (homOfLE (OrderHomClass.mono (Opens.comap f.hom) hVV')).op := by
  apply sheaf_hom_ext_of_supr_cover F ((Opens.comap f.hom) V')
      {U : Opens X | U ∈ BX ∧ U ≤ (Opens.comap f.hom) V'} (sSup_basis_le hBX _)
  rintro U ⟨hU, hUfV'⟩ _
  have hUfV : U ≤ (Opens.comap f.hom) V :=
    hUfV'.trans (OrderHomClass.mono (Opens.comap f.hom) hVV')
  have hL :
      (G.obj.map (homOfLE hVV').op ≫ appOnBasis hBX Φ V' hV')
        ≫ F.obj.map (homOfLE hUfV').op
        = G.obj.map (homOfLE hVV').op ≫ Φ.φ V' hV' U hU hUfV' := by
    rw [Category.assoc, appOnBasis_restrict hBX Φ V' hV' U hU hUfV']
  have hcomp_eq : (homOfLE (OrderHomClass.mono (Opens.comap f.hom) hVV')).op ≫
        (homOfLE hUfV').op = (homOfLE hUfV).op := rfl
  have hR :
      (appOnBasis hBX Φ V hV ≫
          F.obj.map (homOfLE (OrderHomClass.mono (Opens.comap f.hom) hVV')).op)
        ≫ F.obj.map (homOfLE hUfV').op
        = Φ.φ V hV U hU hUfV := by
    rw [Category.assoc, ← F.obj.map_comp, hcomp_eq]
    exact appOnBasis_restrict hBX Φ V hV U hU hUfV
  rw [hL, hR]
  -- Goal now: G.val.map hVV'.op ≫ Φ.φ V' hV' U hU hUfV' = Φ.φ V hV U hU hUfV.
  have e := Φ.compat V V' hV hV' hVV' U U hU hU (le_refl U) hUfV hUfV'
  have eId : F.obj.map (homOfLE (le_refl U)).op = 𝟙 _ := by simp
  rw [eId, Category.comp_id] at e
  exact e.symm

/-- The basis-restricted natural transformation built from `appOnBasis`. -/
noncomputable def basisNatTrans
    (hBX : Opens.IsBasis BX)
    (Φ : CompatibleBasisFamily C f F G BX BY) :
    (inducedFunctor (Subtype.val : ↥BY → Opens Y)).op ⋙ G.obj ⟶
      (inducedFunctor (Subtype.val : ↥BY → Opens Y)).op ⋙
        ((TopCat.Sheaf.pushforward C f).obj F).obj where
  app V := appOnBasis hBX Φ V.unop.1 V.unop.2
  naturality V V' i := by
    have hle : V'.unop.1 ≤ V.unop.1 := leOfHom i.unop.hom
    exact appOnBasis_naturality hBX Φ V.unop.1 V'.unop.1 V.unop.2 V'.unop.2 hle

/-- The existence part of Stacks 009X. -/
lemma exists_fmap_extending
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : CompatibleBasisFamily C f F G BX BY) :
    ∃ (φ : FMapValPresheaf C f F G),
      ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
        (hfU : U ≤ (Opens.comap f.hom) V),
        Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.obj.map (homOfLE hfU).op := by
  have hBY_range : Opens.IsBasis (Set.range (Subtype.val : ↥BY → Opens Y)) := by
    rwa [Subtype.range_coe]
  let α := basisNatTrans hBX Φ
  let φ : FMapValPresheaf C f F G :=
    TopCat.Sheaf.restrictHomEquivHom G.obj
      ((TopCat.Sheaf.pushforward C f).obj F) hBY_range α
  refine ⟨φ, ?_⟩
  intro V hV U hU hfU
  have hext : φ.app (op V) = α.app (op ⟨V, hV⟩) :=
    TopCat.Sheaf.extend_hom_app G.obj
      ((TopCat.Sheaf.pushforward C f).obj F) hBY_range α ⟨V, hV⟩
  rw [hext]
  show Φ.φ V hV U hU hfU = appOnBasis hBX Φ V hV ≫ F.obj.map (homOfLE hfU).op
  rw [appOnBasis_restrict hBX Φ V hV U hU hfU]

end Existence

/-- **Stacks tag 009X (main theorem).** Given a compatible basis family, there is
a unique `f`-map extending it. -/
@[stacks 009X, ega "0 3.2.5" "second paragraph", ega "0 3.5.1" "special case"]
theorem main_theorem009X (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} C FC]
    [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y)
    (BX : Set (Opens X)) (BY : Set (Opens Y))
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (Φ : CompatibleBasisFamily C f F G BX BY) :
    ∃! (φ : FMapValPresheaf C f F G),
      ∀ (V : Opens Y) (hV : V ∈ BY) (U : Opens X) (hU : U ∈ BX)
        (hfU : U ≤ (Opens.comap f.hom) V),
        Φ.φ V hV U hU hfU = φ.app (op V) ≫ F.obj.map (homOfLE hfU).op := by
  obtain ⟨φ, hφ⟩ := exists_fmap_extending hBX hBY Φ
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact fmap_eq_of_basis C f F G BX BY hBX hBY Φ φ' φ hφ' hφ
