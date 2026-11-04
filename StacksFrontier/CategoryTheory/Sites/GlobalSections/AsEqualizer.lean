module

public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.Topology.Sheaves.Init

/-!
# Global sections as an equalizer

Stacks tag 0792.  Fix a pair of morphisms `a, b : V ⟶ U` in a site `(C, J)` and suppose the
map `h_U^# ⟶ *` to the terminal sheaf exhibits `*` as the coequalizer of the two induced
maps `h_V^# ⇉ h_U^#` of sheafified representables.  Then for every sheaf of sets `F` the
evaluation map `Γ(C, F) = Hom(*, F) → F(U)` exhibits `Γ(C, F)` as the equalizer of
`a^*, b^* : F(U) ⇉ F(V)`.  The proof transposes sections along the sheafified Yoneda
bijection `Hom_{Sh}(h_U^#, F) ≃ F(U)`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace Stacks.Sites.GlobalSectionsAsEqualizer

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The sheafified Yoneda embedding `h_X^#`. -/
noncomputable abbrev shYoneda (X : C) : Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj (yoneda.obj X)

/-- A morphism `a : V ⟶ U` in `C` induces a morphism `h_V^# ⟶ h_U^#`. -/
noncomputable abbrev shYonedaMap {V U : C} (a : V ⟶ U) : shYoneda J V ⟶ shYoneda J U :=
  (presheafToSheaf J (Type u)).map (yoneda.map a)

/-- The unique morphism `h_U^# ⟶ *` to the terminal sheaf. -/
noncomputable abbrev shYonedaTerminal (U : C) : shYoneda J U ⟶ ⊤_ Sheaf J (Type u) :=
  terminal.from _

/-- The two compositions `h_V^# ⟶ h_U^# ⟶ *` agree. -/
lemma shYoneda_fork_commutes {V U : C} (a b : V ⟶ U) :
    shYonedaMap J a ≫ shYonedaTerminal J U = shYonedaMap J b ≫ shYonedaTerminal J U :=
  Subsingleton.elim _ _

/-- Global sections of a sheaf `F`. -/
noncomputable abbrev globalSections0792 (F : Sheaf J (Type u)) : Type u :=
  (⊤_ Sheaf J (Type u)) ⟶ F

/-- The canonical bijection `Hom_{Sh(C)}(h_X^#, F) ≃ F(X)`. -/
@[implicit_reducible]
noncomputable def shYonedaHomEquiv (U : C) (F : Sheaf J (Type u)) :
    (shYoneda J U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj U) F).trans yonedaEquiv

/-- The canonical evaluation function `Γ(C, F) → F(U)`. -/
noncomputable def evalFn (F : Sheaf J (Type u)) (U : C) :
    globalSections0792 J F → F.obj.obj (op U) :=
  fun s => shYonedaHomEquiv J U F (shYonedaTerminal J U ≫ s)

/-- The canonical evaluation map `Γ(C, F) → F(U)` as a hom in `Type u`. -/
noncomputable abbrev evalAt (F : Sheaf J (Type u)) (U : C) :
    globalSections0792 J F ⟶ F.obj.obj (op U) :=
  ↾(evalFn J F U)

/-- Naturality of `shYonedaHomEquiv` in `U`. -/
lemma shYonedaHomEquiv_naturality {V U : C} (a : V ⟶ U) (F : Sheaf J (Type u))
    (φ : shYoneda J U ⟶ F) :
    shYonedaHomEquiv J V F (shYonedaMap J a ≫ φ) =
      F.obj.map a.op (shYonedaHomEquiv J U F φ) := by
  rw [shYonedaHomEquiv, shYonedaHomEquiv, Equiv.trans_apply, Equiv.trans_apply,
    (sheafificationAdjunction J (Type u)).homEquiv_naturality_left, yonedaEquiv_naturality]

/-- `evalAt J F U` forms a fork for `F.obj.map a.op, F.obj.map b.op`. -/
lemma evalAt_eq {V U : C} (a b : V ⟶ U) (F : Sheaf J (Type u)) :
    evalAt J F U ≫ F.obj.map a.op = evalAt J F U ≫ F.obj.map b.op := by
  ext s
  dsimp
  simp only [evalFn, ← shYonedaHomEquiv_naturality]
  congr 1
  rw [← Category.assoc, ← Category.assoc, shYoneda_fork_commutes J a b]

/-- The morphism `shYoneda J U ⟶ F` corresponding to an element `x : F.obj.obj (op U)`,
i.e. the sheafified-Yoneda transpose of a section `x ∈ F(U)`. -/
noncomputable def shYonedaOfElt (U : C) (F : Sheaf J (Type u)) (x : F.obj.obj (op U)) :
    shYoneda J U ⟶ F :=
  (shYonedaHomEquiv J U F).symm x

/-- Evaluating the sheafified-Yoneda transpose `shYonedaOfElt J U F x` recovers the section
`x ∈ F(U)`.  It is the `apply_symm_apply` law of `shYonedaHomEquiv`, and it is what turns the
compatibility hypothesis on `x` into the coequalizing property of its transpose. -/
lemma shYonedaHomEquiv_shYonedaOfElt (U : C) (F : Sheaf J (Type u)) (x : F.obj.obj (op U)) :
    shYonedaHomEquiv J U F (shYonedaOfElt J U F x) = x :=
  (shYonedaHomEquiv J U F).apply_symm_apply x

/-- If `x : F(U)` satisfies `F.obj.map a.op x = F.obj.map b.op x`, then `shYonedaOfElt J U F x`
coequalizes the parallel pair `shYonedaMap J a, shYonedaMap J b`. -/
lemma shYonedaOfElt_coequalizes {V U : C} (a b : V ⟶ U) (F : Sheaf J (Type u))
    (x : F.obj.obj (op U)) (hx : F.obj.map a.op x = F.obj.map b.op x) :
    shYonedaMap J a ≫ shYonedaOfElt J U F x = shYonedaMap J b ≫ shYonedaOfElt J U F x := by
  apply (shYonedaHomEquiv J V F).injective
  rwa [shYonedaHomEquiv_naturality, shYonedaHomEquiv_naturality, shYonedaHomEquiv_shYonedaOfElt]

/-- Given the coequalizer hypothesis, factor `shYonedaOfElt J U F x` through
`shYonedaTerminal J U`. -/
noncomputable def liftMap {V U : C} (a b : V ⟶ U)
    (h : IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)))
    (F : Sheaf J (Type u)) (x : F.obj.obj (op U))
    (hx : F.obj.map a.op x = F.obj.map b.op x) :
    globalSections0792 J F :=
  h.desc (Cofork.ofπ (shYonedaOfElt J U F x) (shYonedaOfElt_coequalizes J a b F x hx))

/-- The defining factorization of `liftMap`: composing it with `h_U^# ⟶ *` gives back the
transpose `shYonedaOfElt J U F x` of `x`.  This is the `IsColimit.fac` of the coequalizer
hypothesis `h` at `WalkingParallelPair.one`. -/
lemma shYonedaTerminal_liftMap {V U : C} (a b : V ⟶ U)
    (h : IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)))
    (F : Sheaf J (Type u)) (x : F.obj.obj (op U))
    (hx : F.obj.map a.op x = F.obj.map b.op x) :
    shYonedaTerminal J U ≫ liftMap J a b h F x hx = shYonedaOfElt J U F x := by
  simpa [Cofork.ofπ, Cofork.π, liftMap] using
    h.fac (Cofork.ofπ (shYonedaOfElt J U F x) (shYonedaOfElt_coequalizes J a b F x hx))
      WalkingParallelPair.one

/-- `liftMap` is a preimage of `x` under evaluation at `U`: `evalFn J F U (liftMap … x hx) = x`.
Together with `liftMap_unique` this is the existence half of the equalizer property proved in
`globalSectionsForkIsLimit`. -/
lemma evalFn_liftMap {V U : C} (a b : V ⟶ U)
    (h : IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)))
    (F : Sheaf J (Type u)) (x : F.obj.obj (op U))
    (hx : F.obj.map a.op x = F.obj.map b.op x) :
    evalFn J F U (liftMap J a b h F x hx) = x := by
  simp [evalFn, shYonedaTerminal_liftMap J a b h F x hx, shYonedaHomEquiv_shYonedaOfElt]

/-- Uniqueness: any global section `ψ` with `evalFn J F U ψ = x` equals `liftMap`. -/
lemma liftMap_unique {V U : C} (a b : V ⟶ U)
    (h : IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)))
    (F : Sheaf J (Type u)) (x : F.obj.obj (op U))
    (hx : F.obj.map a.op x = F.obj.map b.op x)
    (ψ : globalSections0792 J F) (hψ : evalFn J F U ψ = x) :
    ψ = liftMap J a b h F x hx := by
  refine Cofork.IsColimit.hom_ext h ?_
  dsimp
  rw [shYonedaTerminal_liftMap]
  apply (shYonedaHomEquiv J U F).injective
  rwa [shYonedaHomEquiv_shYonedaOfElt]

/-- For a fork `s : Fork (F.obj.map a.op) (F.obj.map b.op)`, the condition gives
that for each `x : s.pt`, the two restrictions of `s.ι x` agree. -/
lemma fork_condition_apply {V U : C} (a b : V ⟶ U) (F : Sheaf J (Type u))
    (s : Fork (F.obj.map a.op) (F.obj.map b.op)) (x : s.pt) :
    F.obj.map a.op (s.ι x) = F.obj.map b.op (s.ι x) :=
  ConcreteCategory.congr_hom s.condition x

/-- **Stacks Tag 0792**: `Γ(C, F)` is the equalizer of `a^*, b^*`. -/
@[stacks 0792]
noncomputable def globalSectionsForkIsLimit {V U : C} (a b : V ⟶ U)
    (h : IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)))
    (F : Sheaf J (Type u)) :
    IsLimit (Fork.ofι (evalAt J F U) (evalAt_eq J a b F)) := by
  refine Fork.IsLimit.mk _ ?lift ?fac ?uniq
  · -- lift: for each `s`, give a hom `s.pt ⟶ globalSections0792 J F`.
    exact fun s => ↾fun x => liftMap J a b h F (s.ι x) (fork_condition_apply J a b F s x)
  · intro s
    ext x
    -- Goal: evalAt ∘ lift = s.ι at x
    dsimp
    exact evalFn_liftMap J a b h F (s.ι x) _
  · intro s m hm
    ext x
    dsimp
    refine liftMap_unique J a b h F (s.ι x) _ (m x) ?_
    -- hm says m ≫ evalAt = s.ι; apply at x.
    rw [Fork.ι_ofι] at hm
    have hh := congrArg (fun (f : s.pt ⟶ F.obj.obj (op U)) =>
      CategoryTheory.ConcreteCategory.hom f x) hm
    -- hh : evalFn ((CC.hom m) x) = (CC.hom s.ι) x
    -- Now (CC.hom (m ≫ evalAt)) x = evalAt ((CC.hom m) x) = evalFn (m x)
    simpa [evalAt, evalFn] using hh

end Stacks.Sites.GlobalSectionsAsEqualizer
