module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
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
# Stacks tag 008K — Bijections between sheaf maps, `f`-maps, and inverse image maps

Let `f : X ⟶ Y` be a continuous map of topological spaces, let `F` be a sheaf of
sets on `X`, and let `G` be a sheaf of sets on `Y`.  There are bijections,
functorial in `F` and `G`, between the following four sets:

* `S₁ := Hom_{Sh(Y)} (G, f_* F)`
* `S₂ := Hom_{Sh(X)} (f⁻¹ G, F)`
* `S₃` — the set of `f`-maps `ξ : G → F`, i.e. rules assigning, to every
  open `V ⊆ Y`, a map `ξ_V : G(V) → F(f⁻¹(V))` compatible with restriction.
* `S₄` — the set of compatible collections `ξ_{U,V} : G(V) → F(U)` indexed
  by pairs `(U, V)` of opens with `f(U) ⊆ V`, compatible with restriction
  in both arguments.

The bijection `S₁ ↔ S₂` is the hom-set equivalence of the pushforward / pullback
adjunction.  The bijection `S₁ ↔ S₃` is the canonical (definitional)
identification `(f_* F)(V) = F(f⁻¹(V))`.  The bijection `S₃ ↔ S₄` sends an
`f`-map `ξ` to `ξ_{U,V} := ρ^{f⁻¹(V)}_U ∘ ξ_V`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (F : TopCat.Sheaf (Type u) X) (G : TopCat.Sheaf (Type u) Y)

/-! ## Main definitions -/

/-- The direct image (pushforward) sheaf `f_* F` on `Y`. -/
@[ega "0 3.4.1" "special case",
  sga "4 III 1.9.1",
  sga "4 III 5.3" "special case",
  sga "4 IV 4.1.1" "partial"]
noncomputable abbrev directImage : TopCat.Sheaf (Type u) Y :=
  (TopCat.Sheaf.pushforward (Type u) f).obj F

/-- The presheaf inverse image `f_p G` of a sheaf `G` on `Y`, regarded as a
presheaf on `X`.  By definition `(f_p G)(U) = colim_{V : f(U) ⊆ V} G(V)`. -/
noncomputable abbrev presheafInverseImage : TopCat.Presheaf (Type u) X :=
  (TopCat.Presheaf.pullback (Type u) f).obj G.obj

/-- The inverse image (pullback) sheaf `f⁻¹ G` on `X`, obtained as the
sheafification of the presheaf-level pullback. -/
@[ega "0 3.5.3" "partial, special case",
  ega "0 3.7.1" "more general",
  sga "4 III 1.9.1",
  sga "4 IV 4.1.1" "partial",
  sga "4 IV 9.2.5" "special case",
  sga "4 IV 9.8.1",
  sga "7 XIV 4.5" "partial"]
noncomputable abbrev inverseImage : TopCat.Sheaf (Type u) X :=
  (TopCat.Sheaf.pullback (Type u) f).obj G

/-- An `f`-map from a sheaf `G` on `Y` to a sheaf `F` on `X` along `f : X ⟶ Y`. -/
@[ext]
structure FMapAppNaturalityStruct : Type u where
  /-- For every open `V ⊆ Y`, a section-level map `G(V) → F(f⁻¹(V))`. -/
  app (V : Opens Y) : G.obj.obj (op V) → F.obj.obj (op ((Opens.map f).obj V))
  /-- Compatibility with restriction. -/
  naturality :
    ∀ {V W : Opens Y} (h : W ⟶ V) (s : G.obj.obj (op V)),
      app W (G.obj.map h.op s)
        = F.obj.map ((Opens.map f).map h).op (app V s)

/-- A compatible collection of section-level maps `G(V) → F(U)` indexed by
pairs `(U, V)` of opens with `f(U) ⊆ V`. -/
@[ext]
structure CompatibleCollection : Type u where
  /-- For every pair `(U, V)` with `f(U) ⊆ V`, a section-level map
  `G(V) → F(U)`. -/
  app (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V) :
    G.obj.obj (op V) → F.obj.obj (op U)
  /-- Compatibility with restriction in both arguments. -/
  naturality :
    ∀ {U U' : Opens X} {V V' : Opens Y}
      (hU : U' ⟶ U) (hV : V' ⟶ V)
      (hUV : U ≤ (Opens.map f).obj V)
      (hUV' : U' ≤ (Opens.map f).obj V')
      (s : G.obj.obj (op V)),
      app U' V' hUV' (G.obj.map hV.op s)
        = F.obj.map hU.op (app U V hUV s)

/-- `S₁` : sheaf maps `G ⟶ f_* F` in `Sh(Y)`. -/
@[ega "0 3.5.1" "special case", sga "4 XVII 0.2.1" "(ii), special case"]
abbrev S1 : Type u := G ⟶ directImage f F

/-- `S₂` : sheaf maps `f⁻¹ G ⟶ F` in `Sh(X)`. -/
@[sga "4 XVII 0.2.1" "(i), special case"]
abbrev S2 : Type u := inverseImage f G ⟶ F

/-- `S₃` : the set of `f`-maps `G → F`. -/
@[ega "0 3.5.1" "special case", sga "4 XVII 0.2.1" "(ii), special case"]
abbrev S3 : Type u := FMapAppNaturalityStruct f F G

/-- `S₄` : the set of compatible collections of maps `G → F` along `f`. -/
abbrev S4 : Type u := CompatibleCollection f F G

/-! ## Bijection `S₁ ≃ S₃`

The forward map sends `a : G ⟶ f_* F` to the `f`-map with components
`a.hom.app (op V)`.  This is well-defined because, by definition of
`TopCat.Presheaf.pushforward`, `(f_* F).obj.obj (op V) = F.obj.obj
(op ((Opens.map f).obj V))`.
-/

/-- Forward: from a sheaf morphism `G ⟶ f_* F` to an `f`-map. -/
noncomputable def fwdS1S3 (a : S1 f F G) : S3 f F G where
  app V := ConcreteCategory.hom (a.hom.app (op V))
  naturality h s := NatTrans.naturality_apply a.hom h.op s

/-- Backward construction helper: the natural-transformation underlying the
inverse map. -/
noncomputable def bwdS1S3_natTrans (ξ : S3 f F G) :
    G.obj ⟶ (directImage f F).obj where
  app V := TypeCat.ofHom (ξ.app V.unop)
  naturality _ _ h := by
    ext s
    exact ξ.naturality h.unop s

/-- Backward: from an `f`-map to a sheaf morphism `G ⟶ f_* F`. -/
noncomputable def bwdS1S3 (ξ : S3 f F G) : S1 f F G :=
  ObjectProperty.homMk (bwdS1S3_natTrans f F G ξ)

/-- Reading off the components of a sheaf morphism `G ⟶ f_* F` and reassembling them returns the
morphism itself: the identification `(f_* F)(V) = F(f⁻¹(V))` is definitional. -/
lemma left_inv_S1S3 : Function.LeftInverse (bwdS1S3 f F G) (fwdS1S3 f F G) := by
  intro a
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  rfl

/-- Assembling an `f`-map into a sheaf morphism `G ⟶ f_* F` and reading off its components returns
the original `f`-map. -/
lemma right_inv_S1S3 : Function.RightInverse (bwdS1S3 f F G) (fwdS1S3 f F G) := by
  intro ξ
  apply FMapAppNaturalityStruct.ext
  funext V s
  rfl

/-- **Stacks 008K, (1) ↔ (3).**  Sheaf maps `G ⟶ f_* F` are in bijection with
`f`-maps from `G` to `F`.  Functoriality in `F` and `G` is
`equiv_S1_S3_naturality_F` and `equiv_S1_S3_naturality_G`. -/
@[stacks 008K]
noncomputable def equiv_S1_S3 : S1 f F G ≃ S3 f F G :=
  ⟨fwdS1S3 f F G, bwdS1S3 f F G, left_inv_S1S3 f F G, right_inv_S1S3 f F G⟩

/-! ## Bijection `S₃ ≃ S₄` -/

/-- Naturality of the forward map for `S₃ ≃ S₄`. -/
lemma fwdS3S4_naturality (ξ : S3 f F G)
    {U U' : Opens X} {V V' : Opens Y}
    (hU : U' ⟶ U) (hV : V' ⟶ V)
    (hUV : U ≤ (Opens.map f).obj V)
    (hUV' : U' ≤ (Opens.map f).obj V')
    (s : G.obj.obj (op V)) :
    F.obj.map (homOfLE hUV').op (ξ.app V' (G.obj.map hV.op s))
      = F.obj.map hU.op (F.obj.map (homOfLE hUV).op (ξ.app V s)) := by
  -- Use `ξ.naturality` to push `G.obj.map hV.op` past `ξ.app`.
  rw [ξ.naturality hV s]
  -- Now both sides apply two restriction maps to `ξ.app V s`. Combine using
  -- `Functor.map_comp` (read right-to-left).
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
  -- Both composite morphisms in `Opens X` agree because `Opens X` is a
  -- preorder, so `Hom`-types are subsingletons.
  congr 2

/-- Forward: `ξ ↦ ((U,V,h) ↦ F.obj.map (homOfLE h).op ∘ ξ_V)`. -/
noncomputable def fwdS3S4 (ξ : S3 f F G) : S4 f F G where
  app _U V hUV s := F.obj.map (homOfLE hUV).op (ξ.app V s)
  naturality hU hV hUV hUV' s :=
    fwdS3S4_naturality f F G ξ hU hV hUV hUV' s

/-- Backward: `ξ̃ ↦ (V ↦ ξ̃_{f⁻¹(V), V, le_refl _})`. -/
noncomputable def bwdS3S4 (η : S4 f F G) : S3 f F G where
  app V s := η.app ((Opens.map f).obj V) V (le_refl _) s
  naturality h s :=
    η.naturality ((Opens.map f).map h) h (le_refl _) (le_refl _) s

/-- Keeping only the diagonal pairs `(f⁻¹(V), V)` of the collection built from an `f`-map `ξ`
returns `ξ`, because the restriction along `f⁻¹(V) ≤ f⁻¹(V)` is the identity. -/
lemma left_inv_S3S4 : Function.LeftInverse (bwdS3S4 f F G) (fwdS3S4 f F G) := by
  intro ξ
  apply FMapAppNaturalityStruct.ext
  funext V s
  -- `(bwdS3S4 (fwdS3S4 ξ)).app V s = F.obj.map (homOfLE _).op (ξ.app V s)`,
  -- and the morphism `homOfLE (le_refl _)` is the identity, hence
  -- `F.obj.map ... = id`.
  simp [bwdS3S4, fwdS3S4]

/-- A compatible collection is recovered from its diagonal part: by compatibility in the first
argument, `ξ_{U,V}` is the restriction to `U` of `ξ_{f⁻¹(V),V}`. -/
lemma right_inv_S3S4 : Function.RightInverse (bwdS3S4 f F G) (fwdS3S4 f F G) := by
  intro η
  apply CompatibleCollection.ext
  funext U V hUV s
  -- `(fwdS3S4 (bwdS3S4 η)).app U V hUV s
  --   = F.obj.map (homOfLE hUV).op (η.app (f⁻¹V) V (le_refl _) s)`.
  -- Apply `η.naturality` with `hU = homOfLE hUV : U ⟶ f⁻¹V`,
  -- `hV = 𝟙 V`, `hUV (input) = le_refl _`, `hUV' (input) = hUV`, on `s`.
  have hnat :=
    η.naturality (U := (Opens.map f).obj V) (U' := U) (V := V) (V' := V)
      (homOfLE hUV) (𝟙 V) (le_refl _) hUV s
  rw [show ((𝟙 V : V ⟶ V)).op = 𝟙 (op V) from rfl,
      Functor.map_id_apply] at hnat
  exact hnat.symm

/-- **Stacks 008K, (3) ↔ (4).**  `f`-maps from `G` to `F` are in bijection with
compatible collections of section-level maps.  Functoriality in `F` and `G` is
`equiv_S3_S4_naturality_F` and `equiv_S3_S4_naturality_G`. -/
@[stacks 008K, sga "4 XVII 0.2.1" "(ii), special case"]
noncomputable def equiv_S3_S4 : S3 f F G ≃ S4 f F G :=
  ⟨fwdS3S4 f F G, bwdS3S4 f F G, left_inv_S3S4 f F G, right_inv_S3S4 f F G⟩

/-! ## Bijection `S₁ ≃ S₂` via the adjunction -/

/-- **Stacks 008K, (1) ↔ (2)** via the pullback/pushforward adjunction.  Functoriality in
`F` and `G` is recorded, in composite form, by `equiv_S2_S4_naturality_F` and
`equiv_S2_S4_naturality_G`. -/
@[stacks 008K, sga "4 XVII 0.2.1" "(i), special case"]
noncomputable def equiv_S1_S2 : S1 f F G ≃ S2 f F G :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv G F).symm

/-- **Stacks 008K, (2) ↔ (4).**  Composite via `S₂ ≃ S₁ ≃ S₃ ≃ S₄`. -/
@[sga "4 XVII 0.2.1" "equivalence (i) ⇔ (iii)"]
noncomputable def equiv_S2_S4 : S2 f F G ≃ S4 f F G :=
  (equiv_S1_S2 f F G).symm.trans
    ((equiv_S1_S3 f F G).trans (equiv_S3_S4 f F G))

/-- On sections, the bijection `S₂ ≃ S₄` sends `b` to the restriction to `U` of its adjoint
`f`-map evaluated on `V`. -/
lemma equiv_S2_S4_app (b : S2 f F G) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ (Opens.map f).obj V) (s : G.obj.obj (op V)) :
    (equiv_S2_S4 f F G b).app U V hUV s = F.obj.map (homOfLE hUV).op
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv G F b).hom.app
        (op V) s) :=
  rfl

/-- **Stacks 008K, (1) ↔ (4).** -/
@[sga "4 XVII 0.2.1" "equivalence (ii) ⇔ (iii)"]
noncomputable def equiv_S1_S4 : S1 f F G ≃ S4 f F G :=
  (equiv_S1_S3 f F G).trans (equiv_S3_S4 f F G)

/-- **Stacks 008K, (2) ↔ (3).** -/
noncomputable def equiv_S2_S3 : S2 f F G ≃ S3 f F G :=
  (equiv_S2_S4 f F G).trans (equiv_S3_S4 f F G).symm

/-- Existence form of the six pairwise bijections between `S₁`, `S₂`, `S₃` and `S₄`
(Stacks Tag 008K): a convenience corollary of `equiv_S1_S2`, `equiv_S1_S3`, `equiv_S1_S4`,
`equiv_S2_S3`, `equiv_S2_S4` and `equiv_S3_S4`, which are the actual bijections and which
carry the tag along with the naturality lemmas expressing functoriality in `F` and `G`. -/
theorem nonempty_pairwise_equiv :
    Nonempty (S1 f F G ≃ S2 f F G) ∧
    Nonempty (S1 f F G ≃ S3 f F G) ∧
    Nonempty (S1 f F G ≃ S4 f F G) ∧
    Nonempty (S2 f F G ≃ S3 f F G) ∧
    Nonempty (S2 f F G ≃ S4 f F G) ∧
    Nonempty (S3 f F G ≃ S4 f F G) :=
  ⟨⟨equiv_S1_S2 f F G⟩, ⟨equiv_S1_S3 f F G⟩, ⟨equiv_S1_S4 f F G⟩,
   ⟨equiv_S2_S3 f F G⟩, ⟨equiv_S2_S4 f F G⟩, ⟨equiv_S3_S4 f F G⟩⟩

/-! ## Functorial actions on `FMapAppNaturalityStruct` and `CompatibleCollection` -/

/-- Post-composition of an `f`-map by a sheaf morphism `α : F ⟶ F'`. -/
noncomputable def FMapAppNaturalityStruct.postcomp
    {F F' : TopCat.Sheaf (Type u) X} (α : F ⟶ F') (ξ : FMapAppNaturalityStruct f F G) :
    FMapAppNaturalityStruct f F' G where
  app V t := α.hom.app (op ((Opens.map f).obj V)) (ξ.app V t)
  naturality {V W} h t := by
    have h1 := ξ.naturality h t
    have h2 := NatTrans.naturality_apply α.hom
      ((Opens.map f).map h).op (ξ.app V t)
    rw [h1, h2]

/-- Pre-composition of an `f`-map by a sheaf morphism `β : G' ⟶ G`. -/
noncomputable def FMapAppNaturalityStruct.precomp
    {G G' : TopCat.Sheaf (Type u) Y} (β : G' ⟶ G) (ξ : FMapAppNaturalityStruct f F G) :
    FMapAppNaturalityStruct f F G' where
  app V t := ξ.app V (β.hom.app (op V) t)
  naturality {V W} h t := by
    have h1 := NatTrans.naturality_apply β.hom h.op t
    have h2 := ξ.naturality h (β.hom.app (op V) t)
    rw [h1, h2]

/-- Post-composition of a compatible collection by a sheaf morphism. -/
noncomputable def CompatibleCollection.postcomp
    {F F' : TopCat.Sheaf (Type u) X} (α : F ⟶ F')
    (ξ : CompatibleCollection f F G) :
    CompatibleCollection f F' G where
  app U V hUV t := α.hom.app (op U) (ξ.app U V hUV t)
  naturality {U U' V V'} hU hV hUV hUV' t := by
    have h1 := ξ.naturality hU hV hUV hUV' t
    have h2 := NatTrans.naturality_apply α.hom hU.op (ξ.app U V hUV t)
    rw [h1, h2]

/-- Pre-composition of a compatible collection by a sheaf morphism. -/
noncomputable def CompatibleCollection.precomp
    {G G' : TopCat.Sheaf (Type u) Y} (β : G' ⟶ G)
    (ξ : CompatibleCollection f F G) :
    CompatibleCollection f F G' where
  app U V hUV t := ξ.app U V hUV (β.hom.app (op V) t)
  naturality {U U' V V'} hU hV hUV hUV' t := by
    have h1 := NatTrans.naturality_apply β.hom hV.op t
    have h2 := ξ.naturality hU hV hUV hUV' (β.hom.app (op V) t)
    rw [h1, h2]

/-! ## Naturality (functoriality in `F` and `G`) -/

/-- Naturality in `F` of the bijection `S₁ ≃ S₃`. -/
@[stacks 008K]
theorem equiv_S1_S3_naturality_F
    (F' : TopCat.Sheaf (Type u) X) (α : F ⟶ F') (a : S1 f F G) (V : Opens Y)
    (s : G.obj.obj (op V)) :
    (equiv_S1_S3 f F' G
        (a ≫ ((TopCat.Sheaf.pushforward (Type u) f).map α))).app V s
      = α.hom.app (op ((Opens.map f).obj V)) ((equiv_S1_S3 f F G a).app V s) :=
  rfl

/-- Naturality in `G` of the bijection `S₁ ≃ S₃`. -/
@[stacks 008K]
theorem equiv_S1_S3_naturality_G
    (G' : TopCat.Sheaf (Type u) Y) (β : G' ⟶ G) (a : S1 f F G) (V : Opens Y)
    (s : G'.obj.obj (op V)) :
    (equiv_S1_S3 f F G' (β ≫ a)).app V s
      = (equiv_S1_S3 f F G a).app V (β.hom.app (op V) s) :=
  rfl

/-- Naturality in `F` of the bijection `S₃ ≃ S₄`. -/
@[stacks 008K]
theorem equiv_S3_S4_naturality_F
    (F' : TopCat.Sheaf (Type u) X) (α : F ⟶ F') (ξ : S3 f F G) :
    equiv_S3_S4 f F' G (FMapAppNaturalityStruct.postcomp f G α ξ)
      = CompatibleCollection.postcomp f G α (equiv_S3_S4 f F G ξ) :=
  -- LHS: `F'.obj.map (homOfLE hUV).op (α.hom.app (op (f⁻¹V)) (ξ.app V s))`.
  -- RHS: `α.hom.app (op U) (F.obj.map (homOfLE hUV).op (ξ.app V s))`.
  -- By naturality of `α` at `homOfLE hUV : U ⟶ f⁻¹V`.
  CompatibleCollection.ext <| funext fun _U ↦ funext₃ fun V hUV s ↦
    (NatTrans.naturality_apply α.hom (homOfLE hUV).op (ξ.app V s)).symm

/-- Naturality in `G` of the bijection `S₃ ≃ S₄`. -/
@[stacks 008K]
theorem equiv_S3_S4_naturality_G
    (G' : TopCat.Sheaf (Type u) Y) (β : G' ⟶ G) (ξ : S3 f F G) :
    equiv_S3_S4 f F G' (FMapAppNaturalityStruct.precomp f F β ξ)
      = CompatibleCollection.precomp f F β (equiv_S3_S4 f F G ξ) :=
  rfl

/-- Naturality in `F` of the bijection `S₂ ≃ S₄`. -/
@[stacks 008K]
theorem equiv_S2_S4_naturality_F
    (F' : TopCat.Sheaf (Type u) X) (α : F ⟶ F') (b : S2 f F G)
    (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V)
    (s : G.obj.obj (op V)) :
    (equiv_S2_S4 f F' G (b ≫ α)).app U V hUV s
      = α.hom.app (op U) ((equiv_S2_S4 f F G b).app U V hUV s) := by
  simp only [equiv_S2_S4_app,
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv_naturality_right b α,
    TopCat.Sheaf.comp_app, TopCat.Sheaf.pushforward_map,
    TopCat.Presheaf.pushforward_map_app']
  exact (NatTrans.naturality_apply α.hom (homOfLE hUV).op _).symm

/-- Naturality in `G` of the bijection `S₂ ≃ S₄`. -/
@[stacks 008K]
theorem equiv_S2_S4_naturality_G
    (G' : TopCat.Sheaf (Type u) Y) (β : G' ⟶ G) (b : S2 f F G)
    (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V)
    (s : G'.obj.obj (op V)) :
    (equiv_S2_S4 f F G'
          ((TopCat.Sheaf.pullback (Type u) f).map β ≫ b)).app U V hUV s
      = (equiv_S2_S4 f F G b).app U V hUV (β.hom.app (op V) s) := by
  simp only [equiv_S2_S4_app,
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv_naturality_left β b,
    TopCat.Sheaf.comp_app]
  rfl
