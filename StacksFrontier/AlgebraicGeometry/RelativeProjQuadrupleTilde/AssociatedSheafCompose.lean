module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AssociatedSheafPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# The module of Tag 01O6 along a strict equivalence and along a composite pullback

Let `(d, f : T → S, L, ψ)` be a quadruple and `ℳ̃_T` its module of Tag 01O6, the degree-zero part
of `f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n})`. This file records two coherences of that
construction.

* **Strict equivalence.** An isomorphism `e : L ≅ L'` carrying `ψ` to `ψ'` induces an
  isomorphism `ℳ̃_T(ψ) ≅ ℳ̃_T(ψ')`, `associatedSheafCongrIso`, which is `x ⊗ l ↦ x ⊗ e(l)` on the
  degreewise pure tensors.
* **Composite pullbacks.** For `k : T'' ⟶ T'` and `g : T' ⟶ T` the comparison
  `(k ∘ g)^*ℳ̃_T ≅ ℳ̃_{T''}` of the pullback along the composite is the composite of the
  comparisons along `g` and along `k`, read through the contraction `(k ∘ g)^* ≅ k^* g^*` and
  through the isomorphism of `ℳ̃_{T''}` induced by `k^*g^*L ≅ (k ∘ g)^*L`:
  `associatedSheafPullbackIso_comp`.

The second is what the compatibility of the isomorphisms of Tag 01O7 (1) with pullbacks needs
when it is checked on a covering: the restriction of a pullback is the pullback of a
restriction.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafMap`: the morphism
  `ℳ̃_T(ψ) ⟶ ℳ̃_T(ψ')` induced by a multiplicative degreewise family of morphisms of the Laurent
  algebras carrying `ψ` to `ψ'`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafCongrIso`: the isomorphism
  induced by an isomorphism of the invertible modules.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pureTensor_associatedSheafMap`: the induced
  morphism on the pure tensors.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summandPullback_comp`: the comparison of the
  degreewise summands along a composite.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafPullbackIso_comp`: **the
  comparison along a composite is the composite of the comparisons.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
  (pullbackModule)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso)
open RingedSpaceModuleAdjunction

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesAbelian
  Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesHasCoproducts

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### Rearrangements in an abstract monoidal category -/

section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem inner_square {Ap Li Lj Lk Lm L'i L'j L'k L'm : C} {ψ : Ap ⟶ Li} {ψ' : Ap ⟶ L'i}
    {ci : Li ⟶ L'i} {cj : Lj ⟶ L'j} {ck : Lk ⟶ L'k} {cm : Lm ⟶ L'm} {mul : Li ⊗ Lj ⟶ Lk}
    {mul' : L'i ⊗ L'j ⟶ L'k} {eq : Lk ⟶ Lm} {eq' : L'k ⟶ L'm}
    (hψ : ψ ≫ ci = ψ') (hmul : mul ≫ ck = (ci ⊗ₘ cj) ≫ mul') (heq : eq ≫ cm = ck ≫ eq') :
    ((ψ ▷ Lj) ≫ mul ≫ eq) ≫ cm = (Ap ◁ cj) ≫ (ψ' ▷ L'j) ≫ mul' ≫ eq' := by
  subst hψ
  have h1 : (ψ ▷ Lj) ≫ (ci ⊗ₘ cj) = (Ap ◁ cj) ≫ ((ψ ≫ ci) ▷ L'j) := by
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whisker_exchange]
  calc ((ψ ▷ Lj) ≫ mul ≫ eq) ≫ cm = (ψ ▷ Lj) ≫ mul ≫ ck ≫ eq' := by
        simp only [Category.assoc, heq]
    _ = (ψ ▷ Lj) ≫ (ci ⊗ₘ cj) ≫ mul' ≫ eq' := by rw [reassoc_of% hmul]
    _ = ((ψ ▷ Lj) ≫ (ci ⊗ₘ cj)) ≫ mul' ≫ eq' := (Category.assoc _ _ _).symm
    _ = _ := by rw [h1, Category.assoc]

private theorem assoc_square {Mx Ap Lj L'j Lm L'm : C} {inner : Ap ⊗ Lj ⟶ Lm}
    {inner' : Ap ⊗ L'j ⟶ L'm} {cj : Lj ⟶ L'j} {cm : Lm ⟶ L'm}
    (h : inner ≫ cm = (Ap ◁ cj) ≫ inner') :
    ((α_ Mx Ap Lj).hom ≫ (Mx ◁ inner)) ≫ (Mx ◁ cm) =
      ((Mx ⊗ Ap) ◁ cj) ≫ (α_ Mx Ap L'j).hom ≫ (Mx ◁ inner') := by
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.associator_naturality_right_assoc]

/-- Cancelling a whiskered retraction in front of a morphism out of a tensor product. -/
theorem whiskerLeft_retraction_comp {X Y Y' Z : C} {a : Y ⟶ Y'} {b : Y' ⟶ Y} (h : a ≫ b = 𝟙 Y)
    (z : X ⊗ Y ⟶ Z) : (X ◁ a) ≫ (X ◁ b) ≫ z = z ≫ 𝟙 Z := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, h, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id]

private theorem summand_comp_square {W W1 W2 W3 GP GX P1 X1 P2 X2 P3 X3 X4 : C}
    {cc : W ⟶ W1} {kpt : W1 ⟶ W3} {kp : W1 ⟶ W2} {kt : W2 ⟶ W3} {pk0 : W2 ⟶ GP ⊗ GX}
    {pk : W3 ⟶ P2 ⊗ X2} {ka : GP ⟶ P2} {kb : GX ⟶ X2} {pkg : W ⟶ P1 ⊗ X1} {ccP : P1 ⟶ GP}
    {ccX : X1 ⟶ GX} {ia : P2 ⟶ P3} {lb : X2 ⟶ X3} {c : X3 ⟶ X4} {ra : P1 ⟶ P3}
    {rb : X1 ⟶ X4} (hkpt : kpt = kp ≫ kt) (h1 : kt ≫ pk = pk0 ≫ (ka ⊗ₘ kb))
    (h2 : cc ≫ kp ≫ pk0 = pkg ≫ (ccP ⊗ₘ ccX)) (h3 : ccP ≫ ka ≫ ia = ra)
    (h4 : ccX ≫ kb ≫ lb ≫ c = rb) :
    cc ≫ kpt ≫ (pk ≫ (ia ⊗ₘ lb)) ≫ (P3 ◁ c) = pkg ≫ (ra ⊗ₘ rb) := by
  subst hkpt h3 h4
  calc cc ≫ (kp ≫ kt) ≫ (pk ≫ (ia ⊗ₘ lb)) ≫ (P3 ◁ c)
      = cc ≫ kp ≫ (kt ≫ pk) ≫ (ia ⊗ₘ lb) ≫ (P3 ◁ c) := by simp only [Category.assoc]
    _ = (cc ≫ kp ≫ pk0) ≫ (ka ⊗ₘ kb) ≫ (ia ⊗ₘ lb) ≫ (P3 ◁ c) := by
          rw [h1]
          simp only [Category.assoc]
    _ = _ := by
          rw [h2, ← MonoidalCategory.id_tensorHom]
          simp only [Category.assoc,
            MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

private theorem chain_square {D : Type*} [Category D] {P0 P1 Q0 Q1 R0 R1 S0 S1 S0' E : D}
    {a : P0 ⟶ P1} {cM : P1 ⟶ Q1} {cS : P0 ⟶ Q0} {b : Q0 ⟶ Q1} {ig : Q1 ⟶ R1} {s1 : Q0 ⟶ R0}
    {t1 : R0 ⟶ R1} {ik : R1 ⟶ S1} {s2 : R0 ⟶ S0} {t2 : S0 ⟶ S1} {cg : S1 ⟶ E} {w : S0 ⟶ S0'}
    {t3 : S0' ⟶ E} {s : P0 ⟶ S0'}
    (hnat : cS ≫ b = a ≫ cM) (h1 : b ≫ ig = s1 ≫ t1) (h2 : t1 ≫ ik = s2 ≫ t2)
    (h3 : t2 ≫ cg = w ≫ t3) (h4 : cS ≫ s1 ≫ s2 ≫ w = s) :
    a ≫ cM ≫ ig ≫ ik ≫ cg = s ≫ t3 := by
  subst h4
  rw [← Category.assoc a, ← hnat, Category.assoc, reassoc_of% h1, reassoc_of% h2, h3]
  simp only [Category.assoc]

private theorem inv_assoc_square {D : Type*} [Category D] {X Y Z W : D} (a : X ⟶ Y) (ha : IsIso a)
    (b : Y ⟶ Z) (c : X ⟶ W) (hc : IsIso c) (e : W ⟶ Z) (e' : Z ⟶ W) (he : e ≫ e' = 𝟙 W)
    (h : a ≫ b = c ≫ e) : b ≫ e' ≫ inv c = inv a := by
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [← Category.assoc, h, Category.assoc, reassoc_of% he, IsIso.hom_inv_id]

end Monoidal

/-! ### The module along a morphism of Laurent algebras -/

section Congr

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) {d : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- Two morphisms out of `ℳ̃_T` agree as soon as they agree on the degreewise pure tensors. -/
theorem Twisting.associatedSheaf_hom_ext (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    {a b : Twisting.associatedSheaf M ψ ⟶ N}
    (h : ∀ n : ℤ, Twisting.pureTensor M ψ n ≫ a = Twisting.pureTensor M ψ n ≫ b) : a = b := by
  refine (cancel_epi (cokernel.π (Twisting.relation M ψ))).1 (Sigma.hom_ext _ _ fun n => ?_)
  exact (Category.assoc _ _ _).symm.trans ((h n).trans (Category.assoc _ _ _))

/-- The degreewise morphism of summands `x ⊗ l ↦ x ⊗ c(l)` induced by a degreewise family `c` of
morphisms of the Laurent pieces. -/
def summandMap (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n) (n : ℤ) :
    summand f M d L n ⟶ summand f M d L' n :=
  (pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)) ◁ c (-n)

/-- The morphism of the sources of the balancing relations induced by `c`. -/
def relationSummandMap (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n)
    (p : ℤ × ℤ) : relationSummand f M d L p ⟶ relationSummand f M d L' p :=
  ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ⊗
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d))) ◁ c (-(p.1 + p.2))

/-- The left balancing relation `x ⊗ a ⊗ l ↦ x a ⊗ l` intertwines `relationSummandMap M c` and
`summandMap M c`. -/
theorem relationLeft_summandMap (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n)
    (p : ℤ × ℤ) :
    relationLeft f M d L p ≫ summandMap M c (p.1 + p.2) =
      relationSummandMap M c p ≫ relationLeft f M d L' p :=
  (MonoidalCategory.whisker_exchange _ _).symm

/-- A degreewise family of morphisms commutes with transport along an equality of degrees. -/
theorem eqToHom_comp_laurentFamily
    {X Y : ℤ → SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (c : ∀ n : ℤ, X n ⟶ Y n) {i j : ℤ} (h : i = j) :
    eqToHom (congrArg X h) ≫ c j = c i ≫ eqToHom (congrArg Y h) := by
  subst h
  simp

variable {M}

/-- For a multiplicative degreewise family `c` carrying `ψ` to `ψ'`, the right balancing relations
`x ⊗ a ⊗ l ↦ x ⊗ ψ(a) l` of `ψ` and of `ψ'` are intertwined by `relationSummandMap M c` and
`summandMap M c`. -/
theorem relationRight_summandMap (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n)
    (hψ : ∀ n : ℤ, ψ.app n ≫ c n = ψ'.app n)
    (hmul : ∀ i j : ℤ, (laurent L).mulSheaf i j ≫ c (i + j) =
      (c i ⊗ₘ c j) ≫ (laurent L').mulSheaf i j) (p : ℤ × ℤ) :
    Twisting.relationRight M ψ p ≫ summandMap M c p.1 =
      relationSummandMap M c p ≫ Twisting.relationRight M ψ' p := by
  rw [relationRight_eq, relationRight_eq]
  exact assoc_square (inner_square (hψ p.2) (hmul p.2 (-(p.1 + p.2)))
    (eqToHom_comp_laurentFamily c (by ring : p.2 + -(p.1 + p.2) = -p.1)))

variable (M)

/-- **The morphism `ℳ̃_T(ψ) ⟶ ℳ̃_T(ψ')` induced by a multiplicative degreewise family `c` of
morphisms of the Laurent algebras carrying `ψ` to `ψ'`**: on the degreewise pure tensors it is
`x ⊗ l ↦ x ⊗ c(l)`. -/
def associatedSheafMap (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n)
    (hψ : ∀ n : ℤ, ψ.app n ≫ c n = ψ'.app n)
    (hmul : ∀ i j : ℤ, (laurent L).mulSheaf i j ≫ c (i + j) =
      (c i ⊗ₘ c j) ≫ (laurent L').mulSheaf i j) :
    Twisting.associatedSheaf M ψ ⟶ Twisting.associatedSheaf M ψ' :=
  (Twisting.existsUnique_hom M ψ (Twisting.associatedSheaf M ψ')
    (fun n => summandMap M c n ≫ Twisting.pureTensor M ψ' n) (fun p => by
      rw [← Category.assoc, relationLeft_summandMap, Category.assoc,
        Twisting.relationLeft_pureTensor, ← Category.assoc,
        ← relationRight_summandMap ψ ψ' c hψ hmul p, Category.assoc])).exists.choose

/-- On the degree-`n` pure tensors, `associatedSheafMap M ψ ψ' c` is `x ⊗ l ↦ x ⊗ c(l)`. -/
theorem pureTensor_associatedSheafMap (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (c : ∀ n : ℤ, (laurent L).piece n ⟶ (laurent L').piece n)
    (hψ : ∀ n : ℤ, ψ.app n ≫ c n = ψ'.app n)
    (hmul : ∀ i j : ℤ, (laurent L).mulSheaf i j ≫ c (i + j) =
      (c i ⊗ₘ c j) ≫ (laurent L').mulSheaf i j) (n : ℤ) :
    Twisting.pureTensor M ψ n ≫ associatedSheafMap M ψ ψ' c hψ hmul =
      summandMap M c n ≫ Twisting.pureTensor M ψ' n :=
  (Twisting.existsUnique_hom M ψ (Twisting.associatedSheaf M ψ')
    (fun n => summandMap M c n ≫ Twisting.pureTensor M ψ' n) (fun p => by
      rw [← Category.assoc, relationLeft_summandMap, Category.assoc,
        Twisting.relationLeft_pureTensor, ← Category.assoc,
        ← relationRight_summandMap ψ ψ' c hψ hmul p, Category.assoc])).exists.choose_spec n

/-- **The isomorphism `ℳ̃_T(ψ) ≅ ℳ̃_T(ψ')` induced by an isomorphism `e : L ≅ L'` of the invertible
modules carrying `ψ` to `ψ'`**, that is, by a strict equivalence of quadruples: on the
degreewise pure tensors it is `x ⊗ l ↦ x ⊗ e(l)`. -/
def associatedSheafCongrIso (ψ : Twisting f A d L) (ψ' : Twisting f A d L') (e : L ≅ L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n) :
    Twisting.associatedSheaf M ψ ≅ Twisting.associatedSheaf M ψ' where
  hom := associatedSheafMap M ψ ψ' (fun n => (congrIso e n).hom) hψ
    (LaurentAlgebraCongr.congrIso_mulSheaf e)
  inv := associatedSheafMap M ψ' ψ (fun n => (congrIso e n).inv)
    (fun n => (Iso.comp_inv_eq _).mpr (hψ n).symm) (LaurentAlgebraCongr.congrIso_inv_mulSheaf e)
  hom_inv_id := Twisting.associatedSheaf_hom_ext M ψ fun n => by
    rw [reassoc_of% pureTensor_associatedSheafMap, pureTensor_associatedSheafMap]
    exact whiskerLeft_retraction_comp (congrIso e (-n)).hom_inv_id _
  inv_hom_id := Twisting.associatedSheaf_hom_ext M ψ' fun n => by
    rw [reassoc_of% pureTensor_associatedSheafMap, pureTensor_associatedSheafMap]
    exact whiskerLeft_retraction_comp (congrIso e (-n)).inv_hom_id _

/-- On the degree-`n` pure tensors, `(associatedSheafCongrIso M ψ ψ' e hψ).hom` is
`x ⊗ l ↦ x ⊗ e(l)`. -/
theorem pureTensor_associatedSheafCongrIso_hom (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (e : L ≅ L') (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n) (n : ℤ) :
    Twisting.pureTensor M ψ n ≫ (associatedSheafCongrIso M ψ ψ' e hψ).hom =
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)) ◁ (congrIso e (-n)).hom) ≫
        Twisting.pureTensor M ψ' n :=
  pureTensor_associatedSheafMap M ψ ψ' _ hψ (LaurentAlgebraCongr.congrIso_mulSheaf e) n

end Congr

/-! ### Composite pullbacks -/

section Compose

variable {T'' T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (g : T' ⟶ T) (k : T'' ⟶ T')

/-- The contraction of an iterated pullback is compatible with its own inverse along a composite:
the associativity coherence `compComparison_assoc`, solved for the inverses. -/
theorem compComparison_comp_inv_assoc
    (N : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    compComparison k g ((pullbackFunctor (ringedSpaceHom f)).obj N) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (inv (compComparison g f N)) ≫
          inv (compComparison k (g ≫ f) N) =
      inv (compComparison (k ≫ g) f N) :=
  inv_assoc_square (compComparison (k ≫ g) f N) (isIso_compComparison (k ≫ g) f N)
    (compComparison k g ((pullbackFunctor (ringedSpaceHom f)).obj N))
    (compComparison k (g ≫ f) N) (isIso_compComparison k (g ≫ f) N)
    ((pullbackFunctor (ringedSpaceHom k)).map (compComparison g f N))
    ((pullbackFunctor (ringedSpaceHom k)).map (inv (compComparison g f N)))
    (((pullbackFunctor (ringedSpaceHom k)).map_comp _ _).symm.trans
      ((congrArg (pullbackFunctor (ringedSpaceHom k)).map (IsIso.hom_inv_id _)).trans
        ((pullbackFunctor (ringedSpaceHom k)).map_id _)))
    (compComparison_assoc k g f N)

/-- The comparison of the integral tensor powers along a composite, with the contraction of the
iterated pullback in front: `laurentPullback_comp` solved for the comparison along `k ≫ g`. -/
theorem compComparison_laurentPullback_comp (n : ℤ) :
    compComparison k g ((laurent L).piece n) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (laurentPullback g L n) ≫
          laurentPullback k (pullbackModule g L) n ≫
            (congrIso (LaurentComposition.compCmp k g L) n).hom =
      laurentPullback (k ≫ g) L n := by
  rw [laurentPullback_comp g k L n, compComparison_eq_compCmp_inv, Iso.inv_hom_id_assoc]

/-- **The comparison of the degreewise summands along a composite** is the composite of the
comparisons along `g` and along `k`, read through the contraction of the iterated pullback and
through the comparison of the Laurent pieces induced by `k^*g^*L ≅ (k ≫ g)^*L`. -/
theorem summandPullback_comp (n : ℤ) :
    compComparison k g (summand f M d L n) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (summandPullback M d L g n) ≫
          summandPullback M d (pullbackModule g L) k n ≫
            summandMap M (fun m => (congrIso (LaurentComposition.compCmp k g L) m).hom) n =
      summandPullback M d L (k ≫ g) n :=
  summand_comp_square ((pullbackFunctor (ringedSpaceHom k)).map_comp _ _)
    (pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom k)
      (inv (compComparison g f (M.piece (n * d)))) (laurentPullback g L (-n)))
    (compComparison_tensor k g ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)))
      ((laurent L).piece (-n)))
    (compComparison_comp_inv_assoc g k (M.piece (n * d)))
    (compComparison_laurentPullback_comp L g k (-n))

/-- **The comparison `g^*ℳ̃_T ≅ ℳ̃_{T'}` along a composite is the composite of the comparisons.**
For `k : T'' ⟶ T'` and `g : T' ⟶ T`, contracting `(k ≫ g)^*ℳ̃_T` to `k^*g^*ℳ̃_T`, comparing along
`g` and then along `k`, and identifying the module of the twice-pulled-back quadruple with that
of the quadruple pulled back along `k ≫ g` through `k^*g^*L ≅ (k ≫ g)^*L`, is the comparison
along `k ≫ g`. -/
theorem associatedSheafPullbackIso_comp (ψ : Twisting f A d L) :
    compComparison k g (Twisting.associatedSheaf M ψ) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (associatedSheafPullbackIso M d L g ψ).hom ≫
          (associatedSheafPullbackIso M d (pullbackModule g L) k (ψ.pullback g)).hom ≫
            (associatedSheafCongrIso M ((ψ.pullback g).pullback k) (ψ.pullback (k ≫ g))
              (LaurentComposition.compCmp k g L) (fun n => ψ.pullbackApp_comp g k n)).hom =
      (associatedSheafPullbackIso M d L (k ≫ g) ψ).hom := by
  refine (pullback_existsUnique_hom M d L (k ≫ g) ψ _
    (fun n => summandPullback M d L (k ≫ g) n ≫ Twisting.pureTensor M (ψ.pullback (k ≫ g)) n)
    (summandPullback_pureTensor_balanced M d L (k ≫ g) ψ)).unique (fun n => ?_)
    (associatedSheafPullbackIso_pureTensor M d L (k ≫ g) ψ)
  exact chain_square (compComparison_naturality k g (Twisting.pureTensor M ψ n))
    (((pullbackFunctor (ringedSpaceHom k)).map_comp _ _).symm.trans
      ((congrArg (pullbackFunctor (ringedSpaceHom k)).map
          (associatedSheafPullbackIso_pureTensor M d L g ψ n)).trans
        ((pullbackFunctor (ringedSpaceHom k)).map_comp _ _)))
    (associatedSheafPullbackIso_pureTensor M d (pullbackModule g L) k (ψ.pullback g) n)
    (pureTensor_associatedSheafCongrIso_hom M ((ψ.pullback g).pullback k) (ψ.pullback (k ≫ g))
      (LaurentComposition.compCmp k g L) (fun n => ψ.pullbackApp_comp g k n) n)
    (summandPullback_comp M d L g k n)

/-- Two morphisms out of `g^*ℳ̃_T` agree as soon as they agree on the pullbacks of the degreewise
pure tensors. -/
theorem pullback_associatedSheaf_hom_ext (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    {a b : (pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M ψ) ⟶ N}
    (h : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫ a =
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫ b) : a = b :=
  (pullback_existsUnique_hom M d L g ψ N
    (fun n => (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫ b)
    (fun p => by
      rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.Functor.map_comp, Twisting.relationLeft_pureTensor])).unique h
    (fun _ => rfl)

end Compose

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
