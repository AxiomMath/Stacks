module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.QuotientColumn

/-!
# Reading the tower of algebraizations along the other ideal

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves, let
`(F_n)` be an object of `Coh(X, ℐ)` and let `(G_e)` be the object of `Coh(X, 𝒦)` assembled from
the algebraizations of the reductions `(F_n / 𝒦 ᵉ⁺¹ F_n)` in the proof of [Stacks, Tag 088A].
The datum relating them is an identification

`c : (G_e) ^∧_ℐ ≅ (F_n / 𝒦 ᵉ⁺¹ F_n)`

of towers indexed by `e`. The end of the source's argument needs the *transposed* reading of the
same datum: for each `n`, an identification

`G / ℐ ⁿ⁺¹ G ≅ (F_n) ^∧_𝒦`

of objects of `Coh(X, 𝒦)`, natural in `n`.

Both readings are the same double family `(n, e) ↦ F_n / (ℐ ⁿ⁺¹ + 𝒦 ᵉ⁺¹) F_n`, and the passage
between them is `Stacks.Coherent.idealPowerQuotientAdicColumnIso` on one side and
`Stacks.Coherent.completionTermQuotientIso` on the other. Naturality in `n` is forced, as
everywhere in this directory, by the normalization of both sides by the quotient projections.

## Main definitions

* `Stacks.Coherent.liftedQuotientRowIso` — **the transposed identification** at one `n`.
* `Stacks.Coherent.liftedQuotientRowTowerIso` — the same, as an isomorphism of towers indexed by
  `n`.

## Main results

* `Stacks.Coherent.liftedQuotientRowIso_projection` — the transposed identification is
  normalized by the projection onto the `ℐ ⁿ⁺¹`-reduction.
* `Stacks.Coherent.completionQuotientTower_exchange` — the two ways of dividing the completion
  of a coherent module by both ideals agree.
* `Stacks.Coherent.liftedQuotientRowIso_map_to_completion` — the comparison `γ` of
  `Stacks.Coherent.exists_tower_map_to_completion` and the comparison `α` of hypothesis (2) of
  Tag 088A correspond under the transposed identification.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### Two elementary rewriting steps -/

/-- **Pasting two commuting squares along a shared edge.** -/
public theorem comp_pasteSquare {C : Type*} [Category C] {P Q R S T U : C}
    (g : P ⟶ Q) (cn : Q ⟶ R) (col : R ⟶ S) (c1 : P ⟶ T) (col1 : T ⟶ U) (k : U ⟶ S)
    (q : T ⟶ R) (h1 : q ≫ col = col1 ≫ k) (h2 : g ≫ cn = c1 ≫ q) :
    (c1 ≫ col1) ≫ k = g ≫ cn ≫ col :=
  (Category.assoc c1 col1 k).trans
    ((congrArg (fun z => c1 ≫ z) h1.symm).trans
      ((Category.assoc c1 q col).symm.trans
        ((congrArg (fun z => z ≫ col) h2.symm).trans (Category.assoc g cn col))))

/-- **The shape of the normalized naturality squares of this file.** A morphism factoring as
`p ≫ m` agrees with `p'' ≫ m' ≫ k` as soon as `p'' ≫ m'` factors as `p' ≫ m''`, the square
`m'' ≫ k = g ≫ m` commutes, and `p' ≫ g = p`. -/
public theorem eq_comp_comp_of_pasted {C : Type*} [Category C]
    {A A' A'' B B' D : C} {x : A ⟶ D} {p : A ⟶ B} {m : B ⟶ D}
    {p' : A ⟶ A'} {m'' : A' ⟶ B'} {g : A' ⟶ B}
    {p'' : A ⟶ A''} {m' : A'' ⟶ B'} {k : B' ⟶ D}
    (e1 : x = p ≫ m) (e2 : p'' ≫ m' = p' ≫ m'') (e3 : m'' ≫ k = g ≫ m)
    (e4 : p' ≫ g = p) : x = p'' ≫ m' ≫ k :=
  e1.trans ((congrArg (fun z => z ≫ m) e4.symm).trans
    ((Category.assoc p' g m).trans
      ((congrArg (fun z => p' ≫ z) e3.symm).trans
        ((Category.assoc p' m'' k).symm.trans
          ((congrArg (fun z => z ≫ k) e2.symm).trans (Category.assoc p'' m' k))))))

omit [IsLocallyNoetherian X] in
/-- The components of an isomorphism of coherent adic systems are mutually inverse. -/
public theorem adicIso_hom_inv_id_app {I : X.IdealSheafData} {F G : CoherentAdicSystems I}
    (e : F ≅ G) (n : ℕᵒᵖ) : e.hom.hom.app n ≫ e.inv.hom.app n = 𝟙 (F.obj.obj n) :=
  congrArg (fun f : F ⟶ F => f.hom.app n) e.hom_inv_id

omit [IsLocallyNoetherian X] in
/-- The components of an isomorphism of coherent adic systems cancel under a further
composite. -/
public theorem adicIso_hom_inv_id_app_assoc {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (e : F ≅ G) (n : ℕᵒᵖ) {Z : X.Modules}
    (k : F.obj.obj n ⟶ Z) : e.hom.hom.app n ≫ e.inv.hom.app n ≫ k = k :=
  (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ k) (adicIso_hom_inv_id_app e n)).trans (Category.id_comp k))

/-! ### The transposed identification -/

variable (I K : X.IdealSheafData)

/-- The components of the projection onto a reduction of a coherent adic system are epimorphisms. -/
private theorem epi_idealPowerQuotientAdicProjection_hom_app (G : CoherentAdicSystems K)
    (r e : ℕ) : Epi (((idealPowerQuotientAdicProjection K I r).app G).hom.app (op e)) := by
  change Epi (cokernel.π (C := X.Modules) _)
  infer_instance

/-- Pasting a commuting square with an identity on the remaining composite. -/
private theorem comp_eq_comp_comp_of_square {C : Type*} [Category C] {A B D E S : C}
    {P : A ⟶ B} {m : B ⟶ D} {f : A ⟶ E} {Q : E ⟶ D} {r : D ⟶ S} {x : B ⟶ S}
    (hp : P ≫ m = f ≫ Q) (hr : m ≫ r = x) : P ≫ x = f ≫ Q ≫ r := by
  rw [← hr, ← Category.assoc, hp, Category.assoc]

/-- **The transposed reading of the identification `c`.** Let `(F_n)` be an object of
`Coh(X, ℐ)`, let `(G_e)` be an object of `Coh(X, 𝒦)` and let `c` identify the tower of
`ℐ`-completions of the terms of `(G_e)` with the tower of `𝒦`-power reductions of `(F_n)`. Then
for each `n` the `ℐ ⁿ⁺¹`-reduction of `(G_e)` is the `𝒦`-completion of the coherent module
`F_n`.

Both sides are the row `e ↦ F_n / (ℐ ⁿ⁺¹ + 𝒦 ᵉ⁺¹) F_n` of the double family: on the left `c`
read at the index `n`, on the right `Stacks.Coherent.idealPowerQuotientAdicColumnIso`. -/
public def liftedQuotientRowIso (F : CoherentAdicSystems I) (G : CoherentAdicSystems K)
    (c : (coherentAdicTerms K).obj G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) (n : ℕ) :
    (idealPowerQuotientAdicFunctor K I (n + 1)).obj G ≅
      (completionFunctor X K).obj (((coherentAdicTerms I).obj F).obj (op n)) :=
  (ObjectProperty.fullyFaithfulι (IsCoherentAdicSystem K)).preimageIso
    (Functor.isoWhiskerLeft ((coherentAdicTerms K).obj G)
        (completionTermQuotientIso I n).symm ≪≫
      Functor.isoWhiskerRight c
        (ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
          (evaluation ℕᵒᵖ X.Modules).obj (op n)) ≪≫
      idealPowerQuotientAdicColumnIso I K F n)

/-- **The transposed identification is normalized by the projection.** -/
public theorem liftedQuotientRowIso_projection (F : CoherentAdicSystems I)
    (G : CoherentAdicSystems K)
    (c : (coherentAdicTerms K).obj G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) (n e : ℕ) :
    ((idealPowerQuotientAdicProjection K I (n + 1)).app G).hom.app (op e) ≫
        (liftedQuotientRowIso I K F G c n).hom.hom.app (op e) =
      completionProjection X I (((coherentAdicTerms K).obj G).obj (op e)) n ≫
        (c.app (op e)).hom.hom.app (op n) ≫
          (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) := by
  show cokernel.π (C := X.Modules) _ ≫
      ((completionTermQuotientIso I n).app
        (((coherentAdicTerms K).obj G).obj (op e))).inv ≫
      (c.app (op e)).hom.hom.app (op n) ≫
      (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) = _
  rw [← completionProjection_comp_completionTermQuotientIso I n]
  refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
  refine congrArg (fun z => completionProjection X I
    (((coherentAdicTerms K).obj G).obj (op e)) n ≫ z) ?_
  refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (c.app (op e)).hom.hom.app (op n) ≫
    (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e))
      (Iso.hom_inv_id_app (completionTermQuotientIso I n) _)) ?_
  exact Category.id_comp _

attribute [local irreducible] liftedQuotientRowIso completionTermQuotientIso
  idealPowerQuotientAdicColumnIso completionQuotientTowerTermIso

/-- **The termwise exchange of the two towers is natural in the coherent module.** -/
public theorem completionQuotientTowerTermIso_naturality
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : M ⟶ N)
    (n : ℕ) :
    (idealPowerQuotientAdicFunctor I K (n + 1)).map ((completionFunctor X I).map a) ≫
        (completionQuotientTowerTermIso I K N n).hom =
      (completionQuotientTowerTermIso I K M n).hom ≫
        (completionFunctor X I).map
          (((coherentAdicTerms K).map ((completionFunctor X K).map a)).app (op n)) := by
  have := epi_idealPowerQuotientAdicProjection I K (n + 1) ((completionFunctor X I).obj M)
  apply (cancel_epi ((idealPowerQuotientAdicProjection I K (n + 1)).app
    ((completionFunctor X I).obj M))).mp
  rw [← Category.assoc, ← (idealPowerQuotientAdicProjection I K (n + 1)).naturality,
    Category.assoc, idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso,
    ← Category.assoc, idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso,
    Functor.id_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ObjectProperty.hom_ext _ (completionFunctor_map_quotient X K a n).symm

/-! ### The transposed identification as a morphism of towers -/

/-- **The transposed identification is natural in `n`.** Both transitions are normalized by
the projection onto the `ℐ ⁿ⁺²`-reduction, which is an epimorphism; the resulting identity
pastes the compatibility of the column comparisons with the transitions
(`Stacks.Coherent.idealPowerQuotientAdicColumnIso_hom_naturality`), the naturality of `c`, and
the compatibility of the completion projections with the transitions. -/
public theorem liftedQuotientRowIso_naturality (F : CoherentAdicSystems I)
    (G : CoherentAdicSystems K)
    (c : (coherentAdicTerms K).obj G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) (n : ℕ) :
    (idealPowerQuotientAdicTower K I ⋙ (evaluation _ _).obj G).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        (liftedQuotientRowIso I K F G c n).hom =
      (liftedQuotientRowIso I K F G c (n + 1)).hom ≫
        ((coherentAdicTerms I).obj F ⋙ completionFunctor X K).map
          (homOfLE (Nat.le_add_right n 1)).op := by
  have htower : (idealPowerQuotientAdicTower K I ⋙ (evaluation _ _).obj G).map
        (homOfLE (Nat.le_add_right n 1)).op =
      (idealPowerQuotientAdicDrop K I (Nat.le_succ (n + 1))).app G :=
    congrArg (fun φ => φ.app G) (idealPowerQuotientAdicTower_map_succ K I n)
  refine Eq.trans
    (congrArg (fun z => z ≫ (liftedQuotientRowIso I K F G c n).hom) htower) ?_
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem K) (NatTrans.ext (funext fun y => ?_))
  obtain ⟨e⟩ := y
  have htransition := congrArg (fun f => f.hom.app (op e))
    (idealPowerQuotientAdicProjection_drop K I (Nat.le_succ (n + 1)) G)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at htransition
  have hc := (c.app (op e)).hom.hom.naturality (homOfLE (Nat.le_add_right n 1)).op
  have := epi_idealPowerQuotientAdicProjection_hom_app I K G (n + 1 + 1) e
  apply (cancel_epi (((idealPowerQuotientAdicProjection K I (n + 1 + 1)).app G).hom.app
    (op e))).mp
  refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun z => z ≫ (liftedQuotientRowIso I K F G c n).hom.hom.app (op e)) htransition) ?_
  exact eq_comp_comp_of_pasted (liftedQuotientRowIso_projection I K F G c n e)
    (liftedQuotientRowIso_projection I K F G c (n + 1) e)
    (comp_pasteSquare _ _ _ _ _ _ _
      (idealPowerQuotientAdicColumnIso_hom_naturality I K F n e) hc)
    (completionProjection_transition X I (((coherentAdicTerms K).obj G).obj (op e)) n)

/-- **The transposed identification, as an isomorphism of towers.** The `ℐ ⁿ⁺¹`-reductions of
`(G_e)` form a tower, the `𝒦`-completions of the terms `F_n` form a tower, and
`Stacks.Coherent.liftedQuotientRowIso` identifies them. -/
public def liftedQuotientRowTowerIso (F : CoherentAdicSystems I) (G : CoherentAdicSystems K)
    (c : (coherentAdicTerms K).obj G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) :
    idealPowerQuotientAdicTower K I ⋙ (evaluation _ _).obj G ≅
      (coherentAdicTerms I).obj F ⋙ completionFunctor X K :=
  NatIso.ofComponents (fun n => liftedQuotientRowIso I K F G c n.unop)
    (fun f => (NatTrans.ofOpSequence
      (F := idealPowerQuotientAdicTower K I ⋙ (evaluation _ _).obj G)
      (G := (coherentAdicTerms I).obj F ⋙ completionFunctor X K)
      (fun n => (liftedQuotientRowIso I K F G c n).hom)
      (liftedQuotientRowIso_naturality I K F G c)).naturality f)

/-! ### Dividing a completion by both ideals -/

/-- **The two orders of division of a completion agree.** For a coherent module `H`, dividing
the `ℐ`-completion of `H` by `𝒦 ⁿ⁺¹` and taking the `e`-th term gives the same thing as dividing
the `𝒦`-completion by `ℐ ⁿ⁺¹` and taking the `n`-th term; both are
`H / (ℐ ⁿ⁺¹ + 𝒦 ᵉ⁺¹) H`.

Both sides are normalized by the projection of `H` onto the `e`-th term of its `𝒦`-completion,
which is an epimorphism, after which the identity is the two exchanges of
`Stacks.Coherent.completionQuotientTowerTermIso` together with
`Stacks.Coherent.idealPowerQuotientAdicColumnIso`. -/
public theorem completionQuotientTower_exchange
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n e : ℕ) :
    completionProjection X I
        (((coherentAdicTerms K).obj ((completionFunctor X K).obj H)).obj (op e)) n ≫
      (completionQuotientTowerTermIso I K H e).inv.hom.app (op n) ≫
      (idealPowerQuotientAdicColumnIso I K ((completionFunctor X I).obj H) n).hom.app
        (op e) =
    ((idealPowerQuotientAdicProjection K I (n + 1)).app
        ((completionFunctor X K).obj H)).hom.app (op e) ≫
      (completionQuotientTowerTermIso K I H n).hom.hom.app (op e) := by
  have : Epi (completionProjection X K H e) :=
    Stacks.Algebraization.epi_completionProjection X K H e
  apply (cancel_epi (completionProjection X K H e)).mp
  have h1 := congrArg (fun f => f.hom.app (op n))
    (idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso I K H e)
  have h2 := congrArg (fun f => f.hom.app (op e))
    (idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso K I H n)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h1 h2
  have hp1 := completionFunctor_map_quotient X I (coherentCompletionProjection K H e) n
  change completionProjection X I H n ≫
      ((completionFunctor X I).map (coherentCompletionProjection K H e)).hom.app (op n) =
    completionProjection X K H e ≫ completionProjection X I
      (((coherentAdicTerms K).obj ((completionFunctor X K).obj H)).obj (op e)) n at hp1
  have hp2 := completionFunctor_map_quotient X K (coherentCompletionProjection I H n) e
  change completionProjection X K H e ≫
      ((completionFunctor X K).map (coherentCompletionProjection I H n)).hom.app (op e) =
    completionProjection X I H n ≫ completionProjection X K
      (((coherentAdicTerms I).obj ((completionFunctor X I).obj H)).obj (op n)) e at hp2
  have hinner : ((completionFunctor X I).map
        (coherentCompletionProjection K H e)).hom.app (op n) ≫
      (completionQuotientTowerTermIso I K H e).inv.hom.app (op n) ≫
        (idealPowerQuotientAdicColumnIso I K ((completionFunctor X I).obj H) n).hom.app
          (op e) =
      completionProjection X K
        (((coherentAdicTerms I).obj ((completionFunctor X I).obj H)).obj (op n)) e := by
    rw [← h1, Category.assoc (obj := X.Modules)]
    erw [adicIso_hom_inv_id_app_assoc (completionQuotientTowerTermIso I K H e) (op n)]
    exact idealPowerQuotientAdicProjection_comp_columnIso I K ((completionFunctor X I).obj H) n e
  exact (comp_eq_comp_comp_of_square hp1 hinner).symm.trans
    ((congrArg (fun z => completionProjection X K H e ≫ z) h2).trans hp2).symm

/-- **The two comparisons correspond under the transposed identification.** With the data of
`Stacks.Coherent.exists_tower_map_to_completion` — the comparison `α : (F_n) ⟶ H ^∧_ℐ` of
hypothesis (2) of [Stacks, Tag 088A], the tower `(G_e)`, the identification `c` and the
comparison `γ : (G_e) ⟶ H ^∧_𝒦` whose `ℐ`-completion is given by `c` and `α` — the
`ℐ ⁿ⁺¹`-reduction of `γ` is `α` at the index `n`, read through
`Stacks.Coherent.liftedQuotientRowIso`.

This is what lets the uniqueness clause of [Stacks, Tag 0889], applied to `γ`, be transported
back to a statement about `(F_n)`. -/
public theorem liftedQuotientRowIso_map_to_completion (F : CoherentAdicSystems I)
    (G : CoherentAdicSystems K)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (α : F ⟶ (completionFunctor X I).obj H)
    (γ : G ⟶ (completionFunctor X K).obj H)
    (c : (coherentAdicTerms K).obj G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F)
    (hγ : ∀ e : ℕ, (completionFunctor X I).map (((coherentAdicTerms K).map γ).app (op e)) =
      (c.app (op e)).hom ≫ (idealPowerQuotientAdicFunctor I K (e + 1)).map α ≫
        (completionQuotientTowerTermIso I K H e).hom) (n : ℕ) :
    (idealPowerQuotientAdicFunctor K I (n + 1)).map γ ≫
        (completionQuotientTowerTermIso K I H n).hom =
      (liftedQuotientRowIso I K F G c n).hom ≫
        (completionFunctor X K).map (((coherentAdicTerms I).map α).app (op n)) := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem K) (NatTrans.ext (funext fun y => ?_))
  obtain ⟨e⟩ := y
  have := epi_idealPowerQuotientAdicProjection_hom_app I K G (n + 1) e
  apply (cancel_epi (((idealPowerQuotientAdicProjection K I (n + 1)).app G).hom.app (op e))).mp
  have hnat := congrArg (fun f => f.hom.app (op e))
    ((idealPowerQuotientAdicProjection K I (n + 1)).naturality γ)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.id_map] at hnat
  have hp := completionFunctor_map_quotient X I (((coherentAdicTerms K).map γ).app (op e)) n
  change completionProjection X I (((coherentAdicTerms K).obj G).obj (op e)) n ≫
      ((completionFunctor X I).map
        (((coherentAdicTerms K).map γ).app (op e))).hom.app (op n) =
    γ.hom.app (op e) ≫ completionProjection X I
      (((coherentAdicTerms K).obj ((completionFunctor X K).obj H)).obj (op e)) n at hp
  have hh : ((completionFunctor X I).map
        (((coherentAdicTerms K).map γ).app (op e))).hom.app (op n) =
      (c.app (op e)).hom.hom.app (op n) ≫
        ((idealPowerQuotientAdicFunctor I K (e + 1)).map α).hom.app (op n) ≫
          (completionQuotientTowerTermIso I K H e).hom.hom.app (op n) :=
    congrArg (fun f => f.hom.app (op n)) (hγ e)
  have hcol : idealPowerQuotientMap K K (e + 1) (e + 1) le_rfl (α.hom.app (op n)) ≫
      (idealPowerQuotientAdicColumnIso I K ((completionFunctor X I).obj H) n).hom.app
        (op e) =
    (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) ≫
      ((completionFunctor X K).map
        (((coherentAdicTerms I).map α).app (op n))).hom.app (op e) := by
    rw [idealPowerQuotientAdicColumnIso_hom_app, idealPowerQuotientAdicColumnIso_hom_app]
    exact (completionTermQuotientIso K e).inv.naturality
      (((coherentAdicTerms I).map α).app (op n))
  show _ ≫ _ ≫ _ = _ ≫ _ ≫ _
  have hinner : ((completionFunctor X I).map
        (((coherentAdicTerms K).map γ).app (op e))).hom.app (op n) ≫
      (completionQuotientTowerTermIso I K H e).inv.hom.app (op n) ≫
        (idealPowerQuotientAdicColumnIso I K ((completionFunctor X I).obj H) n).hom.app
          (op e) =
      (c.app (op e)).hom.hom.app (op n) ≫
        (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) ≫
          ((completionFunctor X K).map
            (((coherentAdicTerms I).map α).app (op n))).hom.app (op e) := by
    rw [hh, Category.assoc (obj := X.Modules)]
    erw [Category.assoc (obj := X.Modules), adicIso_hom_inv_id_app_assoc
      (completionQuotientTowerTermIso I K H e) (op n)]
    exact congrArg (fun z => (c.app (op e)).hom.hom.app (op n) ≫ z) hcol
  rw [← Category.assoc (obj := X.Modules), ← hnat, Category.assoc (obj := X.Modules),
    ← completionQuotientTower_exchange I K H n e]
  refine (comp_eq_comp_comp_of_square hp hinner).symm.trans ?_
  rw [← Category.assoc (obj := X.Modules) _ ((liftedQuotientRowIso I K F G c n).hom.hom.app (op e)),
    liftedQuotientRowIso_projection]
  erw [Category.assoc (obj := X.Modules), Category.assoc (obj := X.Modules)]

end Stacks.Coherent

end
