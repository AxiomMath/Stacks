module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.CompletePartialOrder
public import StacksFrontier.CategoryTheory.Abelian.Telescope
public import StacksFrontier.Homology.DerivedCategory.CountableCoproducts

/-!
# Hom out of an object commuting with countable coproducts into a termwise colimit

Let `R` be a ring and `D(R)` the derived category of `R`-modules. Let `K ∈ D(R)` be an object such
that for every sequence `(E_n)` of objects of `D(R)` with a coproduct, the canonical map
`⨁_n Hom(K, E_n) → Hom(K, ⨁_n E_n)` is an isomorphism. Then for every system `(L_n, t_n)` of
cochain complexes of `R`-modules indexed by `ℕ` with termwise colimit `L`, the canonical map
`colim_n Hom(K, L_n) → Hom(K, L)` is an isomorphism.

## Main definitions

* `Stacks.MappingTelescope.DMod`: the derived category `D(R)` of `R`-modules.
* `Stacks.MappingTelescope.System`: a system of cochain complexes of `R`-modules indexed by `ℕ`.
* `Stacks.MappingTelescope.termwiseColimit`: the termwise colimit of a system, as an object of
  `D(R)`.
* `Stacks.MappingTelescope.colimHomComparison`: the canonical map
  `colim_n Hom(K, L_n) → Hom(K, L)`.
* `Stacks.MappingTelescope.CommutesWithCountableCoproducts`: the property that `Hom(K, -)` commutes
  with countable coproducts in `D(R)`.

## Main results

* `Stacks.MappingTelescope.isIso_colimHomComparison`: if `K` commutes with countable coproducts,
  then `colim_n Hom(K, L_n) → Hom(K, L)` is an isomorphism for every system `(L_n)`.

## Implementation notes

A system is a functor `ℕ ⥤ CochainComplex (ModuleCat R) ℤ`, and its termwise colimit is
`colimit L`, sent into `D(R)` by `DerivedCategory.Q`. Since coproducts in `D(R)` are not
automatic, the hypothesis on `K` quantifies over families with `[HasCoproduct E]`. Bijectivity of a
morphism of abelian groups is expressed as `IsIso`.

## References

* [Stacks, Tag 07LR](https://stacks.math.columbia.edu/tag/07LR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.MappingTelescope

universe w u

/-- The category of abelian groups has exact colimits of any small filtered shape. -/
scoped instance hasExactColimitsOfShape_addCommGrpCat (J : Type) [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J AddCommGrpCat.{w} :=
  have : AB5OfSize.{0, 0, w, w + 1} AddCommGrpCat.{w} :=
    AB5OfSize_of_univLE.{0, 0, w, w} AddCommGrpCat.{w}
  AB5OfSize.ofShape J

/-- The category of cochain complexes of `R`-modules has exact colimits of any small filtered
shape. -/
scoped instance hasExactColimitsOfShape_cochainComplex (R : Type u) [Ring R] (J : Type)
    [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J (CochainComplex (ModuleCat.{u} R) ℤ) :=
  have : AB5OfSize.{u, u} (CochainComplex (ModuleCat.{u} R) ℤ) :=
    HomologicalComplex.ab5OfSize (ModuleCat.{u} R) (ComplexShape.up ℤ)
  have : AB5OfSize.{0, 0, u, u + 1} (CochainComplex (ModuleCat.{u} R) ℤ) :=
    AB5OfSize_of_univLE.{0, 0, u, u} (CochainComplex (ModuleCat.{u} R) ℤ)
  AB5OfSize.ofShape J

variable (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The derived category `D(R)` of `R`-modules. -/
abbrev DMod := DerivedCategory (ModuleCat.{u} R)

variable {R}

/-- A *system of complexes over `ℕ`*: a functor from the poset `ℕ` to the category of cochain
complexes of `R`-modules. The morphism `n ⟶ n+1` gives the transition map `t_n : L_n → L_{n+1}`. -/
abbrev System (R : Type u) [Ring R] := ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ

@[deprecated (since := "2026-09-27")]
alias SystemOfComplexes := System

/-- The *termwise colimit* of a system `L`, regarded as an object of the derived category: the
image under `DerivedCategory.Q` of the complex `colimit L`, which is computed termwise in
`CochainComplex (ModuleCat R) ℤ` with the induced differentials. -/
noncomputable def termwiseColimit (L : System R) : DMod R :=
  DerivedCategory.Q.obj (colimit L)

/-- The additive `Hom(K, -)` functor on a preadditive category, landing in abelian groups. -/
noncomputable abbrev homFunctor {C : Type*} [Category.{w} C] [Preadditive C] (K : C) :
    C ⥤ AddCommGrpCat.{w} :=
  preadditiveCoyoneda.obj (Opposite.op K)

/-- The diagram `n ↦ Hom_{D(R)}(K, L_n)` of abelian groups attached to a system `L`
and an object `K`, along the maps induced by the transition maps. -/
noncomputable abbrev homDiagram (L : System R) (K : DMod R) : ℕ ⥤ AddCommGrpCat.{w} :=
  (L ⋙ DerivedCategory.Q) ⋙ homFunctor K

/-- The canonical comparison map `colim_n Hom_{D(R)}(K, L_n) → Hom_{D(R)}(K, L)`, where `L` is the
termwise colimit of the system: the map out of the colimit induced by the cocone obtained by
applying `Hom_{D(R)}(K, -)` to the canonical cocone `Q L_n → L = Q (colimit L)`. -/
noncomputable def colimHomComparison (L : System R) (K : DMod R) :
    colimit (homDiagram L K) ⟶ (homFunctor K).obj (termwiseColimit L) :=
  colimit.desc (homDiagram L K)
    ((homFunctor K).mapCocone (DerivedCategory.Q.mapCocone (colimit.cocone L)))

/-- The composite of the `n`-th colimit injection with `colimHomComparison L K` is
`Hom_{D(R)}(K, -)` applied to the canonical map `Q L_n → L` from the `n`-th term of the system to
the termwise colimit. -/
@[reassoc (attr := simp)]
theorem colimHomComparison_ι (L : System R) (K : DMod R) (n : ℕ) :
    colimit.ι (homDiagram L K) n ≫ colimHomComparison L K
      = (homFunctor K).map (DerivedCategory.Q.map (colimit.ι L n)) := by
  simp [colimHomComparison]

/-- `K` *commutes with countable coproducts*: for every sequence `E : ℕ → D(R)` whose coproduct
exists, the canonical comparison map `⨁_n Hom_{D(R)}(K, E_n) → Hom_{D(R)}(K, ⨁_n E_n)`, that is
`sigmaComparison (Hom_{D(R)}(K, -)) E`, is an isomorphism. -/
def CommutesWithCountableCoproducts (K : DMod R) : Prop :=
  ∀ (E : ℕ → DMod R) [HasCoproduct E], IsIso (sigmaComparison (homFunctor K) E)

/-- If `K` commutes with countable coproducts, the comparison map for a sequence `E` with a
coproduct is an isomorphism. -/
theorem CommutesWithCountableCoproducts.isIso_sigmaComparison {K : DMod R}
    (hK : CommutesWithCountableCoproducts K) (E : ℕ → DMod R) [HasCoproduct E] :
    IsIso (sigmaComparison (homFunctor K) E) := hK E

/-- An object `K` whose `Hom_{D(R)}(K, -)` functor preserves colimits of shape `Discrete ℕ`
commutes with countable coproducts. -/
theorem CommutesWithCountableCoproducts.of_preservesColimitsOfShape {K : DMod R}
    [PreservesColimitsOfShape (Discrete ℕ) (homFunctor K)] :
    CommutesWithCountableCoproducts K := fun _ _ => inferInstance

/-- The family `n ↦ Q(L_n)` of objects of `D(R)` attached to a system `L`. -/
noncomputable abbrev derivedSystem (L : System R) : ℕ → DMod R :=
  fun n => DerivedCategory.Q.obj (L.obj n)

/-- For a system `L`, the family `n ↦ Q(L_n)` has a coproduct in `D(R)`. -/
instance hasCoproduct_derivedSystem (L : System R) : HasCoproduct (derivedSystem L) := by
  have := derivedCategoryQ_preservesColimitsOfShapeℕ (R := R)
  exact hasColimit_of_iso
    (Discrete.natIso (fun _ => Iso.refl _) : Discrete.functor (derivedSystem L) ≅
      Discrete.functor (fun n => L.obj n) ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R)))

/-- For a system `L`, writing `S = ∐_n Q(L_n)`, there is a distinguished triangle
`S --f--> S --p--> termwiseColimit L --δ--> S[1]` in `D(R)` such that, for every `n`,
`Sigma.ι n ≫ p = Q(ι_n)` for the colimit injection `ι_n : L_n ⟶ colimit L` and
`Sigma.ι n ≫ f = Sigma.ι n - Q(t_n) ≫ Sigma.ι (n + 1)`. -/
theorem exists_telescope_triangle (L : System R) :
    ∃ (f : (∐ derivedSystem L) ⟶ (∐ derivedSystem L))
      (p : (∐ derivedSystem L) ⟶ termwiseColimit L)
      (δ : termwiseColimit L ⟶ (shiftFunctor (DMod R) (1 : ℤ)).obj (∐ derivedSystem L)),
      (Triangle.mk f p δ ∈ distinguishedTriangles)
      ∧ (∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ p = DerivedCategory.Q.map (colimit.ι L n))
      ∧ (∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ f = Sigma.ι (derivedSystem L) n
          - DerivedCategory.Q.map (L.map (homOfLE n.le_succ))
              ≫ Sigma.ι (derivedSystem L) (n + 1)) := by
  have := derivedCategoryQ_preservesColimitsOfShapeℕ (R := R)
  let e : (∐ derivedSystem L) ≅ DerivedCategory.Q.obj (∐ (fun n => L.obj n)) :=
    colimit.isoColimitCocone
      { cocone := (Cocone.precompose (Discrete.natIso (fun _ => Iso.refl _) :
            Discrete.functor (derivedSystem L) ≅
              (Discrete.functor (fun n => L.obj n)
                ⋙ DerivedCategory.Q (C := ModuleCat.{u} R))).hom).obj
          (DerivedCategory.Q.mapCocone
            (Cofan.mk (∐ (fun n => L.obj n)) (Sigma.ι (fun n => L.obj n))))
        isColimit := (IsColimit.precomposeHomEquiv (Discrete.natIso (fun _ => Iso.refl _) :
            Discrete.functor (derivedSystem L) ≅
              (Discrete.functor (fun n => L.obj n)
                ⋙ DerivedCategory.Q (C := ModuleCat.{u} R))) _).symm
          (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct (fun n => L.obj n))) }
  have he : ∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ e.hom
      = DerivedCategory.Q.map (Sigma.ι (fun n => L.obj n) n) := by
    intro n
    rw [show Sigma.ι (derivedSystem L) n
        = colimit.ι (Discrete.functor (derivedSystem L)) ⟨n⟩ from rfl,
      colimit.isoColimitCocone_ι_hom]
    simp only [Cocone.precompose_obj_ι, NatTrans.comp_app,
      Functor.mapCocone_ι_app, Discrete.natIso_hom_app, Iso.refl_hom]
    simp [Cofan.mk]
  set tel := Sigma.desc (fun n => Sigma.ι (fun n => L.obj n) n
      - L.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => L.obj n) (n + 1)) with htel_eq
  have hz : tel ≫ Sigma.desc (fun n => colimit.ι L n) = 0 := telescope_general_hz L
  have htel : (ShortComplex.mk tel (Sigma.desc (fun n => colimit.ι L n)) hz).ShortExact :=
    telescope_shortExact_general L hz
  set Sc : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk tel (Sigma.desc (fun n => colimit.ι L n)) hz
  have hdist0 : DerivedCategory.triangleOfSES htel ∈ distinguishedTriangles :=
    DerivedCategory.triangleOfSES_distinguished htel
  refine ⟨e.hom ≫ DerivedCategory.Q.map Sc.f ≫ e.inv,
          e.hom ≫ DerivedCategory.Q.map Sc.g,
          (DerivedCategory.triangleOfSES htel).mor₃ ≫ (shiftFunctor (DMod R) (1 : ℤ)).map e.inv,
          ?_, ?_, ?_⟩
  · refine isomorphic_distinguished _ hdist0 _ ?_
    refine Triangle.isoMk _ _ e e (Iso.refl _) ?_ ?_ ?_
    · change (e.hom ≫ DerivedCategory.Q.map Sc.f ≫ e.inv) ≫ e.hom
        = e.hom ≫ DerivedCategory.Q.map Sc.f
      simp
    · change (e.hom ≫ DerivedCategory.Q.map Sc.g) ≫ (Iso.refl _).hom
        = e.hom ≫ DerivedCategory.Q.map Sc.g
      simp
    · change ((DerivedCategory.triangleOfSES htel).mor₃ ≫ (shiftFunctor (DMod R) (1 : ℤ)).map e.inv)
            ≫ (shiftFunctor (DMod R) (1 : ℤ)).map e.hom
        = (Iso.refl _).hom ≫ (DerivedCategory.triangleOfSES htel).mor₃
      have hcancel : (shiftFunctor (DMod R) (1 : ℤ)).map e.inv
            ≫ (shiftFunctor (DMod R) (1 : ℤ)).map e.hom = 𝟙 _ :=
        ((shiftFunctor (DMod R) (1 : ℤ)).mapIso e).inv_hom_id
      rw [Category.assoc, hcancel]
      simp only [Iso.refl_hom, Category.id_comp]
      exact Category.comp_id _
  · intro n
    rw [← Category.assoc, he n]
    have : Sc.g = Sigma.desc (fun n => colimit.ι L n) := rfl
    rw [this, ← Functor.map_comp]
    congr 1
    exact Sigma.ι_comp_desc _ _
  · have he_inv : ∀ m : ℕ, DerivedCategory.Q.map (Sigma.ι (fun n => L.obj n) m) ≫ e.inv
        = Sigma.ι (derivedSystem L) m := by
      intro m
      rw [← he m, Category.assoc, e.hom_inv_id, Category.comp_id]
    intro n
    have hScf : Sc.f = tel := rfl
    rw [← Category.assoc, ← Category.assoc, he n, Category.assoc, hScf, htel_eq,
      ← Functor.map_comp_assoc, Sigma.ι_comp_desc]
    rw [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp, Category.assoc,
      he_inv n, he_inv (n + 1)]

/-- If `g : ∐ E ⟶ ∐ E` acts on the `n`-th summand by `ι_n - t_n ≫ ι_{n+1}`, then
`sigmaComparison` for `Hom(K, -)` conjugates `Hom(K, g)` into the corresponding telescope map. -/
private theorem sigmaComparison_comp_map_telescope {C : Type*} [Category.{w} C] [Preadditive C]
    (K : C) (E : ℕ → C) [HasCoproduct E] (t : (n : ℕ) → E n ⟶ E (n + 1)) (g : (∐ E) ⟶ (∐ E))
    (hg : ∀ n : ℕ, Sigma.ι E n ≫ g = Sigma.ι E n - t n ≫ Sigma.ι E (n + 1)) :
    sigmaComparison (homFunctor K) E ≫ (homFunctor K).map g
      = (Sigma.desc (fun n => Sigma.ι (fun n => (homFunctor K).obj (E n)) n
          - (homFunctor K).map (t n) ≫ Sigma.ι (fun n => (homFunctor K).obj (E n)) (n + 1)))
        ≫ sigmaComparison (homFunctor K) E := by
  refine Sigma.hom_ext _ _ (fun n => ?_)
  rw [← Category.assoc, ι_comp_sigmaComparison, ← Category.assoc, Sigma.ι_comp_desc,
    Preadditive.sub_comp, Category.assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_sub, hg n]

/-- Let `E : ℕ → C` have a coproduct such that `Hom(K, -)` takes it to a coproduct, and let
`t n : E n ⟶ E (n + 1)`. If `g : ∐ E ⟶ ∐ E` satisfies
`Sigma.ι E n ≫ g = Sigma.ι E n - t n ≫ Sigma.ι E (n + 1)` for all `n`, then `Hom(K, g)` is a
monomorphism. -/
theorem mono_homFunctor_map_of_telescope {C : Type*} [Category.{w} C] [Preadditive C] (K : C)
    (E : ℕ → C) [HasCoproduct E] (hE : IsIso (sigmaComparison (homFunctor K) E))
    (t : (n : ℕ) → E n ⟶ E (n + 1)) (g : (∐ E) ⟶ (∐ E))
    (hg : ∀ n : ℕ, Sigma.ι E n ≫ g = Sigma.ι E n - t n ≫ Sigma.ι E (n + 1)) :
    Mono ((homFunctor K).map g) := by
  set H := homFunctor K
  let G : ℕ ⥤ AddCommGrpCat.{w} := Functor.ofSequence (fun n => H.map (t n))
  have hGmap : ∀ n : ℕ, G.map (homOfLE n.le_succ) = H.map (t n) := fun n =>
    Functor.ofSequence_map_homOfLE_succ _ n
  have hmonoG := telescope_general_mono G
  simp only [hGmap] at hmonoG
  have hconj := sigmaComparison_comp_map_telescope K E t g hg
  have hg_eq : H.map g
      = inv (sigmaComparison H E)
        ≫ ((Sigma.desc (fun n => Sigma.ι (fun n => H.obj (E n)) n
            - H.map (t n) ≫ Sigma.ι (fun n => H.obj (E n)) (n + 1)))
          ≫ sigmaComparison H E) := by
    rw [← hconj, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hg_eq]
  have : Mono (Sigma.desc (fun n => Sigma.ι (fun n => H.obj (E n)) n
      - H.map (t n) ≫ Sigma.ι (fun n => H.obj (E n)) (n + 1))) := hmonoG
  infer_instance

/-- Let `K` commute with countable coproducts, and let
`S --f--> S --p--> termwiseColimit L --δ--> S[1]` be a distinguished triangle with
`S = ∐_n Q(L_n)`, `Sigma.ι n ≫ p = Q(ι_n)` and
`Sigma.ι n ≫ f = Sigma.ι n - Q(t_n) ≫ Sigma.ι (n + 1)`. Then, writing `F = homDiagram L K`, the map
`⨁_n F_n ⟶ Hom_{D(R)}(K, termwiseColimit L)` induced by the maps `Hom_{D(R)}(K, Q(ι_n))` fits into
a short exact sequence with the telescope map `⨁_n F_n ⟶ ⨁_n F_n`, given on the `n`-th summand by
`ι_n - F(t_n) ≫ ι_{n+1}`. In particular the former is a cokernel of the latter. -/
theorem shortExact_homSigmaDesc_of_telescope (K : DMod R)
    (hK : CommutesWithCountableCoproducts K) (L : System R)
    (f : (∐ derivedSystem L) ⟶ (∐ derivedSystem L))
    (p : (∐ derivedSystem L) ⟶ termwiseColimit L)
    (δ : termwiseColimit L ⟶ (shiftFunctor (DMod R) (1 : ℤ)).obj (∐ derivedSystem L))
    (hdist : Triangle.mk f p δ ∈ distinguishedTriangles)
    (hp : ∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ p = DerivedCategory.Q.map (colimit.ι L n))
    (hf : ∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ f = Sigma.ι (derivedSystem L) n
          - DerivedCategory.Q.map (L.map (homOfLE n.le_succ))
              ≫ Sigma.ι (derivedSystem L) (n + 1))
    (hzΦ : (Sigma.desc (fun n => Sigma.ι (fun n => (homDiagram L K).obj n) n
              - (homDiagram L K).map (homOfLE n.le_succ)
                  ≫ Sigma.ι (fun n => (homDiagram L K).obj n) (n + 1)))
            ≫ Sigma.desc (fun n =>
                (homFunctor K).map (DerivedCategory.Q.map (colimit.ι L n))) = 0) :
    (ShortComplex.mk
      (Sigma.desc (fun n => Sigma.ι (fun n => (homDiagram L K).obj n) n
          - (homDiagram L K).map (homOfLE n.le_succ)
              ≫ Sigma.ι (fun n => (homDiagram L K).obj n) (n + 1)))
      (Sigma.desc (fun n =>
          (homFunctor K).map (DerivedCategory.Q.map (colimit.ι L n)))) hzΦ).ShortExact := by
  set H := homFunctor K
  set E := derivedSystem L
  have hσiso : IsIso (sigmaComparison H E) := hK.isIso_sigmaComparison E
  have hισ : ∀ m, Sigma.ι (fun n => H.obj (E n)) m ≫ sigmaComparison H E = H.map (Sigma.ι E m) :=
    fun m => ι_comp_sigmaComparison H E m
  set Φ := Sigma.desc (fun n => H.map (DerivedCategory.Q.map (colimit.ι L n))) with hΦ
  set telF := Sigma.desc (fun n => Sigma.ι (fun n => (homDiagram L K).obj n) n
      - (homDiagram L K).map (homOfLE n.le_succ)
        ≫ Sigma.ι (fun n => (homDiagram L K).obj n) (n + 1)) with htelF
  have hStepA : sigmaComparison H E ≫ H.map p = Φ := by
    refine Sigma.hom_ext _ _ (fun n => ?_)
    rw [← Category.assoc, hισ n, ← H.map_comp, hp n, hΦ, Sigma.ι_comp_desc]
  have hStepA' : sigmaComparison H E ≫ H.map f = telF ≫ sigmaComparison H E :=
    sigmaComparison_comp_map_telescope K E
      (fun n => DerivedCategory.Q.map (L.map (homOfLE n.le_succ))) f hf
  have hmono_telF : Mono telF := telescope_general_mono (homDiagram L K)
  have hexact_fp : (ShortComplex.mk telF Φ hzΦ).Exact := by
    have hHex := Functor.IsHomological.exact (F := H) (Triangle.mk f p δ) hdist
    refine ShortComplex.exact_of_iso ?_ hHex
    refine ShortComplex.isoMk
      (asIso (sigmaComparison H E)).symm (asIso (sigmaComparison H E)).symm (Iso.refl _) ?_ ?_
    · change inv (sigmaComparison H E) ≫ telF = H.map f ≫ inv (sigmaComparison H E)
      rw [IsIso.inv_comp_eq, ← Category.assoc, hStepA', Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    · change inv (sigmaComparison H E) ≫ Φ = H.map p ≫ 𝟙 _
      rw [Category.comp_id, IsIso.inv_comp_eq, hStepA]
  set E' := fun n => (shiftFunctor (DMod R) (1 : ℤ)).obj (E n)
  have hcop' : HasCoproduct E' := by
    have : HasColimit (Discrete.functor E ⋙ shiftFunctor (DMod R) (1 : ℤ)) :=
      ⟨_, isColimitOfPreserves (shiftFunctor (DMod R) (1 : ℤ))
        (colimit.isColimit (Discrete.functor E))⟩
    exact hasColimit_of_iso
      (Discrete.natIsoFunctor (F := Discrete.functor E ⋙ shiftFunctor (DMod R) (1 : ℤ))).symm
  have : IsIso (sigmaComparison (shiftFunctor (DMod R) (1 : ℤ)) E) := inferInstance
  set c := sigmaComparison (shiftFunctor (DMod R) (1 : ℤ)) E
  have hιc : ∀ n, Sigma.ι E' n ≫ c = (shiftFunctor (DMod R) (1 : ℤ)).map (Sigma.ι E n) :=
    fun n => ι_comp_sigmaComparison (shiftFunctor (DMod R) (1 : ℤ)) E n
  set g' : (∐ E') ⟶ (∐ E') := c ≫ (shiftFunctor (DMod R) (1 : ℤ)).map f ≫ inv c with hg'
  have hg'_tel : ∀ n : ℕ, Sigma.ι E' n ≫ g'
      = Sigma.ι E' n - (shiftFunctor (DMod R) (1 : ℤ)).map (DerivedCategory.Q.map (L.map (homOfLE
          n.le_succ)))
          ≫ Sigma.ι E' (n + 1) := by
    intro n
    have hci : ∀ m, (shiftFunctor (DMod R) (1 : ℤ)).map (Sigma.ι E m) ≫ inv c = Sigma.ι E' m := by
      intro m
      rw [← hιc m, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hg', ← Category.assoc, ← Category.assoc, hιc n,
      ← Functor.map_comp, hf n, Functor.map_sub, Preadditive.sub_comp, hci n,
      Functor.map_comp, Category.assoc, hci (n + 1)]
  have hmono_shf : Mono (H.map ((shiftFunctor (DMod R) (1 : ℤ)).map f)) := by
    have hmg' : Mono (H.map g') :=
      mono_homFunctor_map_of_telescope K E' (hK.isIso_sigmaComparison E')
        (fun n =>
          (shiftFunctor (DMod R) (1 : ℤ)).map (DerivedCategory.Q.map (L.map (homOfLE n.le_succ))))
        g' hg'_tel
    have hfeq : (shiftFunctor (DMod R) (1 : ℤ)).map f = inv c ≫ g' ≫ c := by
      rw [hg', ← Category.assoc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hfeq, H.map_comp, H.map_comp]
    infer_instance
  have hepi_Hp : Epi (H.map p) := by
    have hd1 := rot_of_distTriang _ hdist
    have hd2 := rot_of_distTriang _ hd1
    have hmono2 : Mono ((shortComplexOfDistTriangle _ hd2).map H).g := by
      change Mono (H.map (-((shiftFunctor (DMod R) (1 : ℤ)).map f)))
      rw [Functor.map_neg]
      infer_instance
    exact (ShortComplex.exact_iff_epi _ ((ShortComplex.Exact.mono_g_iff
      (Functor.IsHomological.exact (F := H) _ hd2)).mp hmono2)).mp
        (Functor.IsHomological.exact (F := H) _ hd1)
  have : Epi Φ := by
    rw [← hStepA]
    infer_instance
  exact (ShortComplex.ShortExact.mk hexact_fp : (ShortComplex.mk telF Φ hzΦ).ShortExact)

/-- Let `K` commute with countable coproducts, and let
`S --f--> S --p--> termwiseColimit L --δ--> S[1]` be a distinguished triangle with
`S = ∐_n Q(L_n)`, `Sigma.ι n ≫ p = Q(ι_n)` and
`Sigma.ι n ≫ f = Sigma.ι n - Q(t_n) ≫ Sigma.ι (n + 1)`. Then `colimHomComparison L K` is an
isomorphism. -/
theorem isIso_colimHomComparison_of_telescope (K : DMod R)
    (hK : CommutesWithCountableCoproducts K) (L : System R)
    (f : (∐ derivedSystem L) ⟶ (∐ derivedSystem L))
    (p : (∐ derivedSystem L) ⟶ termwiseColimit L)
    (δ : termwiseColimit L ⟶ (shiftFunctor (DMod R) (1 : ℤ)).obj (∐ derivedSystem L))
    (hdist : Triangle.mk f p δ ∈ distinguishedTriangles)
    (hp : ∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ p = DerivedCategory.Q.map (colimit.ι L n))
    (hf : ∀ n : ℕ, Sigma.ι (derivedSystem L) n ≫ f = Sigma.ι (derivedSystem L) n
          - DerivedCategory.Q.map (L.map (homOfLE n.le_succ))
              ≫ Sigma.ι (derivedSystem L) (n + 1)) :
    IsIso (colimHomComparison L K) := by
  set F : ℕ ⥤ AddCommGrpCat.{w} := homDiagram L K
  have hzcan : (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
        ≫ Sigma.desc (fun n => colimit.ι F n) = 0 := telescope_general_hz F
  have hSEScan : (ShortComplex.mk
      (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
      (Sigma.desc (fun n => colimit.ι F n)) hzcan).ShortExact :=
    telescope_shortExact_general F hzcan
  have hcanCok : IsColimit (CokernelCofork.ofπ
      (Sigma.desc (fun n => colimit.ι F n)) hzcan) := hSEScan.gIsCokernel
  have hclaimB : (Sigma.desc (fun n => colimit.ι F n)) ≫ colimHomComparison L K
      = Sigma.desc (fun n =>
          (homFunctor K).map (DerivedCategory.Q.map (colimit.ι L n))) := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact colimHomComparison_ι L K n
  have hzΦ : (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
              - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
            ≫ Sigma.desc (fun n =>
                (homFunctor K).map (DerivedCategory.Q.map (colimit.ι L n))) = 0 := by
    have : (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
              - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
            ≫ ((Sigma.desc (fun n => colimit.ι F n)) ≫ colimHomComparison L K)
          = 0 := by rw [← Category.assoc, hzcan, zero_comp]
    rwa [hclaimB] at this
  have hΦCok :=
    (shortExact_homSigmaDesc_of_telescope K hK L f p δ hdist hp hf hzΦ).gIsCokernel
  have heq : colimHomComparison L K
      = (IsColimit.coconePointUniqueUpToIso hcanCok hΦCok).hom := by
    refine Cofork.IsColimit.hom_ext hcanCok ?_
    exact hclaimB.trans
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcanCok hΦCok WalkingParallelPair.one).symm
  rw [heq]
  infer_instance

/-- **Stacks 07LR**.
Let `R` be a ring and let `K ∈ D(R)` be such that for every sequence `(E_n)` of objects of `D(R)`
with a coproduct, the canonical map `⨁_n Hom_{D(R)}(K, E_n) → Hom_{D(R)}(K, ⨁_n E_n)` is an
isomorphism. Then for every system of complexes `(L_n, t_n)` over `ℕ` with termwise colimit `L`,
the canonical map `colim_n Hom_{D(R)}(K, L_n) → Hom_{D(R)}(K, L)` is an isomorphism. -/
@[stacks 07LR]
theorem isIso_colimHomComparison (K : DMod R) (hK : CommutesWithCountableCoproducts K)
    (L : System R) :
    IsIso (colimHomComparison L K) := by
  obtain ⟨f, p, δ, hdist, hp, hf⟩ := exists_telescope_triangle L
  exact isIso_colimHomComparison_of_telescope K hK L f p δ hdist hp hf

end Stacks.MappingTelescope
