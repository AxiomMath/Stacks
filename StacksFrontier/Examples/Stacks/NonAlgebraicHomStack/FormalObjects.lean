module

public import StacksFrontier.AlgebraicGeometry.Stacks.HomStack.Basic
public import StacksFrontier.Examples.Stacks.HomStackAlgebraicStackUniverses

/-!
# Non-effective formal objects of the Hom-stack over `Spec k⟦t⟧`

Let `S = Spec k⟦t⟧`, let `X` be a scheme over `S` with thickenings `Xₙ = X ×_S Spec (k⟦t⟧/(tⁿ⁺¹))`
and let `𝒵` be a category fibred in groupoids over the big fppf site of `S` with a classifying
invariant with values in `H¹(-, A)` for an abelian sheaf `A` (for `𝒵 = [S/A]` this is the
classification of `A`-torsors by `H¹`, Stacks 03AJ). The fibre of the Hom-stack `Mor_S(X, 𝒵)`
over `T` is the fibre of `𝒵` over `X ×_S T`, so its isomorphism classes over `T` are classified
by `H¹(X ×_S T, A)`. The source's proof of Lemma 0AFB says: "unwinding definitions, it is enough
to check that `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective". This file proves that unwinding:
if `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective, then `Mor_S(X, 𝒵)` has a formal object over the
complete local ring `k⟦t⟧` which is not effective, and hence (Stacks 07X8) `Mor_S(X, 𝒵)` is not an
algebraic stack.

## Main definitions

* `Stacks.Examples.NonAlgebraicHomStack.powerSeriesFormalBase k`: `k⟦t⟧` as a complete local base
  over `S = Spec k⟦t⟧`.
* `Stacks.Examples.NonAlgebraicHomStack.prodTruncationIso`: `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹) ≅ Xₙ` in the
  big fppf site of `S`.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.exists_not_isEffective_homStack`: the non-surjectivity
  of `H¹(X, A) ⟶ lim H¹(Xₙ, A)` gives a formal object of `Mor_S(X, 𝒵)` which is not effective.
* `Stacks.Examples.NonAlgebraicHomStack.exists_not_restriction_homStack`: the same formal object,
  over `k⟦t⟧`, is not the system of restrictions of an object of `Mor_S(X, 𝒵)` over `S`; that is,
  the functor `Mor_S(X, 𝒵)(S) ⟶ lim Mor_S(X, 𝒵)(Sₙ)` of Lemma 0AFB is not essentially
  surjective.
* `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_homStack`: and then `Mor_S(X, 𝒵)` is
  not an algebraic stack.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Deformation.Artin AlgebraicGeometry.Stack

universe u w w'

namespace Stacks.Examples.NonAlgebraicHomStack

/-! ### Thickenings for equal ideals -/

section EqualIdeals

variable {A : Type u} [CommRing A]

/-- The base change of the `n`-th thickening along an equality of ideals. -/
def pullbackAdicIso {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I J : Ideal A} (h : I = J) (n : ℕ)
    (g : adicThickening A I n ⟶ Spec (.of A)) (hg : g = adicThickeningι A I n) :
    pullback f g ≅ pullback f (adicThickeningι A J n) := by
  subst h hg
  exact Iso.refl _

/-- The thickening for an ideal equal to `I`. -/
def adicThickeningIsoOfEq {I J : Ideal A} (h : I = J) (n : ℕ) :
    adicThickening A I n ≅ adicThickening A J n := by
  subst h
  exact Iso.refl _

@[reassoc (attr := simp)]
lemma pullbackAdicIso_hom_fst {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I J : Ideal A}
    (h : I = J) (n : ℕ) (g : adicThickening A I n ⟶ Spec (.of A))
    (hg : g = adicThickeningι A I n) :
    (pullbackAdicIso f h n g hg).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  subst h hg
  simp [pullbackAdicIso]

@[reassoc (attr := simp)]
lemma pullbackAdicIso_hom_snd {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I J : Ideal A}
    (h : I = J) (n : ℕ) (g : adicThickening A I n ⟶ Spec (.of A))
    (hg : g = adicThickeningι A I n) :
    (pullbackAdicIso f h n g hg).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (adicThickeningIsoOfEq h n).hom := by
  subst h hg
  simp [pullbackAdicIso, adicThickeningIsoOfEq]

@[reassoc (attr := simp)]
lemma adicThickeningIsoOfEq_succ {I J : Ideal A} (h : I = J) (n : ℕ) :
    (adicThickeningIsoOfEq h n).hom ≫ adicThickeningSucc A J n =
      adicThickeningSucc A I n ≫ (adicThickeningIsoOfEq h (n + 1)).hom := by
  subst h
  simp [adicThickeningIsoOfEq]

end EqualIdeals

/-! ### `k⟦t⟧` as a complete local base -/

variable (k : Type u) [Field k]

/-- The residue morphism `Spec k ⟶ Spec k⟦t⟧` is a closed immersion. -/
instance : IsClosedImmersion (adicThickeningι (PowerSeries k)
    (maximalIdeal (PowerSeries k)) 0) := by
  unfold adicThickeningι
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- `k⟦t⟧`, as a complete local base over `S = Spec k⟦t⟧` with structure morphism the identity. -/
abbrev powerSeriesFormalBase : FormalBase (base k) where
  R := PowerSeries k
  noetherian := inferInstance
  complete := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  toS := 𝟙 _
  residueLocallyFiniteType := by rw [Category.comp_id]; infer_instance
  residueQuasiCompact := by rw [Category.comp_id]; infer_instance

/-- The maximal ideal of the complete local base `k⟦t⟧` is `(t)`. -/
lemma powerSeriesFormalBase_maximalIdeal :
    maximalIdeal (powerSeriesFormalBase k).R = uniformizer k :=
  PowerSeries.maximalIdeal_eq_span_X

variable {k} (B : BigFppfSite.{u}) (hS : B.Contains (base k))

/-- The infinitesimal thickenings of `Spec k⟦t⟧` lie in the site. -/
lemma powerSeriesFormalBase_contains (hS : B.Contains (base k)) (n : ℕ) :
    B.Contains ((powerSeriesFormalBase k).truncation n) :=
  truncationContains B (base k) (powerSeriesFormalBase k) hS n

/-- The `n`-th thickening `Spec (k⟦t⟧ / 𝔪ⁿ⁺¹)`, as an object of the big fppf site over `S`. -/
abbrev truncationObj (n : ℕ) : BigFppfOver B (base k) hS :=
  truncationOver B (base k) hS (powerSeriesFormalBase k) (powerSeriesFormalBase_contains B hS) n

/-- `S = Spec k⟦t⟧` itself, as the object `baseOver` of the big fppf site over `S`. -/
abbrev powerSeriesBaseObj : BigFppfOver B (base k) hS :=
  baseOver B (base k) hS (powerSeriesFormalBase k) hS

/-- `S`, as an object of the big fppf site over itself, is final. -/
def isTerminalPowerSeriesBaseObj : IsTerminal (powerSeriesBaseObj B hS) :=
  Over.mkIdTerminal

variable {X : Scheme.{u}} (fX : X ⟶ base k) (hX : B.Contains X)
  (hXn : ∀ n, B.Contains (thickening fX n))

/-! ### `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹) ≅ Xₙ` -/

/-- The underlying scheme of `X ×_S T` in the big fppf site is the fibre product of schemes. -/
def prodToSchemeIso (T : BigFppfOver B (base k) hS) :
    (BigFppfOver.toScheme B (base k) hS).obj (totalObj B hS fX hX ⨯ T) ≅
      pullback fX (B.inclusion.map T.hom) :=
  ((Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (totalObj B hS fX hX) T)).map
    B.inclusion).isoPullback

@[reassoc (attr := simp)]
lemma prodToSchemeIso_hom_fst (T : BigFppfOver B (base k) hS) :
    (prodToSchemeIso B hS fX hX T).hom ≫ pullback.fst _ _ =
      (BigFppfOver.toScheme B (base k) hS).map prod.fst :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma prodToSchemeIso_hom_snd (T : BigFppfOver B (base k) hS) :
    (prodToSchemeIso B hS fX hX T).hom ≫ pullback.snd _ _ =
      (BigFppfOver.toScheme B (base k) hS).map prod.snd :=
  IsPullback.isoPullback_hom_snd _

/-- The `n`-th thickening of `k⟦t⟧` for its maximal ideal is the one for `(t)`. -/
def truncThickIso (n : ℕ) :
    (BigFppfOver.toScheme B (base k) hS).obj (truncationObj B hS n) ≅
      adicThickening (PowerSeries k) (uniformizer k) n :=
  adicThickeningIsoOfEq (powerSeriesFormalBase_maximalIdeal k) n

lemma truncThickIso_succ (n : ℕ) :
    (BigFppfOver.toScheme B (base k) hS).map (truncationOverSucc B (base k) hS
        (powerSeriesFormalBase k) (powerSeriesFormalBase_contains B hS) n) ≫
      (truncThickIso B hS (n + 1)).hom =
      (truncThickIso B hS n).hom ≫ adicThickeningSucc (PowerSeries k) (uniformizer k) n :=
  (adicThickeningIsoOfEq_succ (powerSeriesFormalBase_maximalIdeal k) n).symm

/-- The underlying scheme of `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹)` is `Xₙ`. -/
def prodTruncationSchemeIso (n : ℕ) :
    (BigFppfOver.toScheme B (base k) hS).obj (totalObj B hS fX hX ⨯ truncationObj B hS n) ≅
      thickening fX n :=
  prodToSchemeIso B hS fX hX (truncationObj B hS n) ≪≫
    pullbackAdicIso fX (powerSeriesFormalBase_maximalIdeal k) n _ (Category.comp_id _)

@[reassoc (attr := simp)]
lemma prodTruncationSchemeIso_hom_fst (n : ℕ) :
    (prodTruncationSchemeIso B hS fX hX n).hom ≫ pullback.fst _ _ =
      (BigFppfOver.toScheme B (base k) hS).map prod.fst := by
  exact (Category.assoc _ _ _).trans ((congrArg ((prodToSchemeIso B hS fX hX _).hom ≫ ·)
    (pullbackAdicIso_hom_fst _ _ _ _ _)).trans (prodToSchemeIso_hom_fst B hS fX hX _))

@[reassoc (attr := simp)]
lemma prodTruncationSchemeIso_hom_snd (n : ℕ) :
    (prodTruncationSchemeIso B hS fX hX n).hom ≫ pullback.snd _ _ =
      (BigFppfOver.toScheme B (base k) hS).map prod.snd ≫ (truncThickIso B hS n).hom := by
  exact (Category.assoc _ _ _).trans ((congrArg ((prodToSchemeIso B hS fX hX _).hom ≫ ·)
    (pullbackAdicIso_hom_snd _ _ _ _ _)).trans (prodToSchemeIso_hom_snd_assoc B hS fX hX _ _))

/-- `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹) ≅ Xₙ` in the big fppf site over `S`. -/
def prodTruncationIso (n : ℕ) :
    totalObj B hS fX hX ⨯ truncationObj B hS n ≅ thickeningObj B hS fX hXn n :=
  Over.isoMk (ObjectProperty.isoMk _ (X := (totalObj B hS fX hX ⨯ truncationObj B hS n).left)
      (Y := (thickeningObj B hS fX hXn n).left) (prodTruncationSchemeIso B hS fX hX n)) (by
    apply ObjectProperty.hom_ext
    exact (prodTruncationSchemeIso_hom_fst_assoc B hS fX hX n fX).trans <|
      congrArg (fun g ↦ B.inclusion.map g)
        (Over.w (prod.fst : totalObj B hS fX hX ⨯ truncationObj B hS n ⟶ _)))

lemma toScheme_prodTruncationIso_hom (n : ℕ) :
    (BigFppfOver.toScheme B (base k) hS).map (prodTruncationIso B hS fX hX hXn n).hom =
      (prodTruncationSchemeIso B hS fX hX n).hom :=
  rfl

/-- The isomorphisms `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹) ≅ Xₙ` are compatible with the transitions. -/
lemma prodTruncationIso_succ (n : ℕ) :
    prod.map (𝟙 _) (truncationOverSucc B (base k) hS (powerSeriesFormalBase k)
        (powerSeriesFormalBase_contains B hS) n) ≫ (prodTruncationIso B hS fX hX hXn (n + 1)).hom =
      (prodTruncationIso B hS fX hX hXn n).hom ≫ thickeningObjSucc B hS fX hXn n := by
  apply (BigFppfOver.toScheme B (base k) hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, toScheme_prodTruncationIso_hom,
    toScheme_prodTruncationIso_hom]
  change _ = _ ≫ thickeningSucc fX n
  apply pullback.hom_ext
  · exact ((Category.assoc _ _ _).trans
      (congrArg _ (prodTruncationSchemeIso_hom_fst B hS fX hX (n + 1)))).trans
      ((show (BigFppfOver.toScheme B (base k) hS).map (prod.map (𝟙 _)
          (truncationOverSucc B (base k) hS (powerSeriesFormalBase k)
            (powerSeriesFormalBase_contains B hS) n)) ≫
          (BigFppfOver.toScheme B (base k) hS).map prod.fst =
          (BigFppfOver.toScheme B (base k) hS).map prod.fst by
        rw [← Functor.map_comp, prod.map_fst, Category.comp_id]).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (thickeningSucc_toTotal fX n)).trans
        (prodTruncationSchemeIso_hom_fst B hS fX hX n))).symm)
  · have e2 : (BigFppfOver.toScheme B (base k) hS).map (prod.map (𝟙 (totalObj B hS fX hX))
          (truncationOverSucc B (base k) hS (powerSeriesFormalBase k)
            (powerSeriesFormalBase_contains B hS) n)) ≫
          (BigFppfOver.toScheme B (base k) hS).map prod.snd ≫ (truncThickIso B hS (n + 1)).hom =
        (BigFppfOver.toScheme B (base k) hS).map prod.snd ≫
          (BigFppfOver.toScheme B (base k) hS).map (truncationOverSucc B (base k) hS
            (powerSeriesFormalBase k) (powerSeriesFormalBase_contains B hS) n) ≫
          (truncThickIso B hS (n + 1)).hom := by
      rw [← Category.assoc, ← Functor.map_comp, prod.map_snd, Functor.map_comp, Category.assoc]
    have e4 : ((prodTruncationSchemeIso B hS fX hX n).hom ≫ thickeningSucc fX n) ≫
        pullback.snd _ _ = ((prodTruncationSchemeIso B hS fX hX n).hom ≫ pullback.snd _ _) ≫
          adicThickeningSucc (PowerSeries k) (uniformizer k) n := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _)
    exact ((Category.assoc _ _ _).trans
      (congrArg _ (prodTruncationSchemeIso_hom_snd B hS fX hX (n + 1)))).trans
      (e2.trans ((congrArg _ (truncThickIso_succ B hS n)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ adicThickeningSucc (PowerSeries k) (uniformizer k) n)
          (prodTruncationSchemeIso_hom_snd B hS fX hX n).symm).trans e4.symm))))

/-- `X ×_S S ≅ X` in the big fppf site over `S`, by the first projection. -/
def prodBaseIso : totalObj B hS fX hX ⨯ powerSeriesBaseObj B hS ≅ totalObj B hS fX hX where
  hom := prod.fst
  inv := prod.lift (𝟙 _) ((isTerminalPowerSeriesBaseObj B hS).from _)
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · exact (isTerminalPowerSeriesBaseObj B hS).hom_ext _ _
  inv_hom_id := by simp

/-- The isomorphisms `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹) ≅ Xₙ` and `X ×_S S ≅ X` are compatible with the
maps to `X`. -/
lemma prodTruncationIso_toTotal (n : ℕ) :
    prod.map (𝟙 _) (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
        (powerSeriesFormalBase_contains B hS) n) ≫ (prodBaseIso B hS fX hX).hom =
      (prodTruncationIso B hS fX hX hXn n).hom ≫ thickeningObjToTotal B hS fX hX hXn n := by
  apply (BigFppfOver.toScheme B (base k) hS).map_injective
  have h : prod.map (𝟙 _) (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
      (powerSeriesFormalBase_contains B hS) n) ≫ (prodBaseIso B hS fX hX).hom = prod.fst :=
    (prod.map_fst _ _).trans (Category.comp_id _)
  rw [h, Functor.map_comp, toScheme_prodTruncationIso_hom]
  exact (prodTruncationSchemeIso_hom_fst B hS fX hX n).symm

/-- Transport of a compatibility along isomorphisms: if `Φ t` corresponds to `s` under
isomorphisms `Φ T ≅ Y` and `Φ T' ≅ Y'`, then pulling back along `Φ t` the transport of an
element `x'` over `Y'` is the transport of its pullback along `s`. -/
lemma map_op_map_hom_op_eq {𝒞 : Type*} [Category 𝒞] (Φ : 𝒞 ⥤ 𝒞) (F : 𝒞ᵒᵖ ⥤ Type*)
    {T T' Y Y' : 𝒞} (t : T ⟶ T') (I : Φ.obj T ≅ Y) (I' : Φ.obj T' ≅ Y') (s : Y ⟶ Y')
    (h : Φ.map t ≫ I'.hom = I.hom ≫ s) {x' : F.obj (op Y')} {x : F.obj (op Y)}
    (hx : F.map s.op x' = x) :
    (Φ.op ⋙ F).map t.op (F.map I'.hom.op x') = F.map I.hom.op x := by
  rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ← Functor.map_comp_apply,
    ← op_comp, h, op_comp, Functor.map_comp_apply, hx]

/-! ### The non-effective formal object -/

variable [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})]
  (𝒜 : Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})

/-- The presheaf of sets `T ↦ H¹(T, A)` on the big fppf site over `S`. -/
abbrev h1Presheaf : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type w :=
  𝒜.cohomologyPresheaf 1 ⋙ forget AddCommGrpCat.{w}

/-- The compatible system on the objects `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹)` corresponding to a compatible
system on the thickenings `Xₙ`. -/
def prodTruncationSystem (c : CompatibleSystem B hS fX hXn 𝒜) (n : ℕ) :
    ((baseChangeFunctor (totalObj B hS fX hX)).op ⋙ h1Presheaf B hS 𝒜).obj
      (op (truncationObj B hS n)) :=
  (h1Presheaf B hS 𝒜).map (prodTruncationIso B hS fX hX hXn n).hom.op (c.1 n)

/-- The compatibility of a system on the thickenings, read in the presheaf `h1Presheaf`. -/
lemma h1Presheaf_map_thickeningObjSucc (c : CompatibleSystem B hS fX hXn 𝒜) (n : ℕ) :
    (h1Presheaf B hS 𝒜).map (thickeningObjSucc B hS fX hXn n).op (c.1 (n + 1)) = c.1 n :=
  c.2 n

lemma prodTruncationSystem_succ (c : CompatibleSystem B hS fX hXn 𝒜) (n : ℕ) :
    ((baseChangeFunctor (totalObj B hS fX hX)).op ⋙ h1Presheaf B hS 𝒜).map
        (truncationOverSucc B (base k) hS (powerSeriesFormalBase k)
          (powerSeriesFormalBase_contains B hS) n).op
        (prodTruncationSystem B hS fX hX hXn 𝒜 c (n + 1)) =
      prodTruncationSystem B hS fX hX hXn 𝒜 c n :=
  map_op_map_hom_op_eq (baseChangeFunctor (totalObj B hS fX hX)) (h1Presheaf B hS 𝒜)
    (truncationOverSucc B (base k) hS (powerSeriesFormalBase k)
      (powerSeriesFormalBase_contains B hS) n)
    (prodTruncationIso B hS fX hX hXn n) (prodTruncationIso B hS fX hX hXn (n + 1))
    (thickeningObjSucc B hS fX hXn n) (prodTruncationIso_succ B hS fX hX hXn n)
    (h1Presheaf_map_thickeningObjSucc B hS fX hXn 𝒜 c n)

/-- A compatible system `c ∈ lim H¹(Xₙ, A)` which is not the restriction of a class on `X` gives
a compatible system on the objects `X ×_S Spec (k⟦t⟧/𝔪ⁿ⁺¹)` which is not the restriction of a
class on `X ×_S S`. -/
lemma exists_ne_prodTruncationSystem (c : CompatibleSystem B hS fX hXn 𝒜)
    (hc : ∀ ζ, toCompatibleSystems B hS fX hX hXn 𝒜 ζ ≠ c)
    (y : ((baseChangeFunctor (totalObj B hS fX hX)).op ⋙ h1Presheaf B hS 𝒜).obj
      (op (powerSeriesBaseObj B hS))) :
    ∃ n, ((baseChangeFunctor (totalObj B hS fX hX)).op ⋙ h1Presheaf B hS 𝒜).map
        (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
          (powerSeriesFormalBase_contains B hS) n).op y ≠
      prodTruncationSystem B hS fX hX hXn 𝒜 c n := by
  let ζ := (h1Presheaf B hS 𝒜).map (prodBaseIso B hS fX hX).inv.op y
  have hne := hc ζ
  by_contra hall
  push Not at hall
  apply hne
  apply Subtype.ext
  funext n
  have hsq : (prodTruncationIso B hS fX hX hXn n).inv ≫ prod.map (𝟙 _)
      (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
        (powerSeriesFormalBase_contains B hS) n) =
      thickeningObjToTotal B hS fX hX hXn n ≫ (prodBaseIso B hS fX hX).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
      (prodTruncationIso_toTotal B hS fX hX hXn n)).trans (Category.assoc _ _ _))
  calc (h1Presheaf B hS 𝒜).map (thickeningObjToTotal B hS fX hX hXn n).op ζ
      = (h1Presheaf B hS 𝒜).map ((prodBaseIso B hS fX hX).inv.op ≫
          (thickeningObjToTotal B hS fX hX hXn n).op) y :=
        (Functor.map_comp_apply _ _ _ _).symm
    _ = (h1Presheaf B hS 𝒜).map ((prod.map (𝟙 _) (restrictionToBase B (base k) hS
          (powerSeriesFormalBase k) hS (powerSeriesFormalBase_contains B hS) n)).op ≫
          (prodTruncationIso B hS fX hX hXn n).inv.op) y := by
        rw [← op_comp, ← op_comp, hsq]
    _ = (h1Presheaf B hS 𝒜).map (prodTruncationIso B hS fX hX hXn n).inv.op
          ((h1Presheaf B hS 𝒜).map (prod.map (𝟙 _) (restrictionToBase B (base k) hS
            (powerSeriesFormalBase k) hS (powerSeriesFormalBase_contains B hS) n)).op y) :=
        Functor.map_comp_apply _ _ _ _
    _ = (h1Presheaf B hS 𝒜).map (prodTruncationIso B hS fX hX hXn n).inv.op
          ((h1Presheaf B hS 𝒜).map (prodTruncationIso B hS fX hX hXn n).hom.op (c.1 n)) :=
        congrArg _ (hall n)
    _ = c.1 n := by
        rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
          Functor.map_id_apply]

/-- An element of `lim H¹(Xₙ, A)` outside the image of `H¹(X, A)`. -/
lemma exists_forall_toCompatibleSystems_ne
    (hnot : ¬ Function.Surjective (toCompatibleSystems B hS fX hX hXn 𝒜)) :
    ∃ c, ∀ ζ, toCompatibleSystems B hS fX hX hXn 𝒜 ζ ≠ c := by
  by_contra h
  push Not at h
  exact hnot h

/-- **The source's unwinding of Lemma 0AFB.** Let `𝒵` be a category fibred in groupoids over the
big fppf site of `S = Spec k⟦t⟧` with a classifying invariant with values in `H¹(-, A)`. If the
comparison map `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective, then the Hom-stack `Mor_S(X, 𝒵)` has
a formal object over `k⟦t⟧` which is not effective in the sense of Stacks 07X7. -/
theorem exists_not_isEffective_homStack
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B (base k) hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    {cl : ∀ z : 𝒵.obj, (h1Presheaf B hS 𝒜).obj (op (𝒵.p.obj z))}
    (hcl : IsClassifyingInvariant (h1Presheaf B hS 𝒜) cl)
    (hnot : ¬ Function.Surjective (toCompatibleSystems B hS fX hX hXn 𝒜)) :
    ∃ ξ : FormalObject B (base k) hS (homStack (totalObj B hS fX hX) 𝒵).p,
      ¬ FormalObject.IsEffective B (base k) hS _
        (isFiberedInGroupoids_homStack (totalObj B hS fX hX) 𝒵 h𝒵) ξ := by
  obtain ⟨c, hc⟩ := exists_forall_toCompatibleSystems_ne B hS fX hX hXn 𝒜 hnot
  exact exists_not_isEffective_of_compatible (isFiberedInGroupoids_homStack _ 𝒵 h𝒵)
    (isClassifyingInvariant_homStackClass h𝒵 hcl) (powerSeriesFormalBase k) hS
    (powerSeriesFormalBase_contains B hS) (prodTruncationSystem B hS fX hX hXn 𝒜 c)
    (prodTruncationSystem_succ B hS fX hX hXn 𝒜 c)
    (exists_ne_prodTruncationSystem B hS fX hX hXn 𝒜 c hc)

/-- **Lemma 0AFB in the form of its statement, from the non-surjectivity on `H¹`.** Let `𝒵` be a
category fibred in groupoids over the big fppf site of `S = Spec k⟦t⟧` with a classifying
invariant with values in `H¹(-, A)`. If `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective, then the
functor `Mor_S(X, 𝒵)(S) ⟶ lim Mor_S(X, 𝒵)(Sₙ)` is not essentially surjective: there is a formal
object `ξ` of `Mor_S(X, 𝒵)` over `k⟦t⟧`, with `ξₙ` lying over `Sₙ = Spec (k⟦t⟧/𝔪ⁿ⁺¹)`, and no
object `x` of `Mor_S(X, 𝒵)` admits morphisms `ξₙ ⟶ x` lying over the closed immersions
`Sₙ ⟶ S`. In a category fibred in groupoids such morphisms are exactly the identifications of
`ξₙ` with the restrictions `x|_{Sₙ}`. -/
theorem exists_not_restriction_homStack
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B (base k) hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    {cl : ∀ z : 𝒵.obj, (h1Presheaf B hS 𝒜).obj (op (𝒵.p.obj z))}
    (hcl : IsClassifyingInvariant (h1Presheaf B hS 𝒜) cl)
    (hnot : ¬ Function.Surjective (toCompatibleSystems B hS fX hX hXn 𝒜)) :
    ∃ ξ : FormalObject B (base k) hS (homStack (totalObj B hS fX hX) 𝒵).p,
      ξ.base = powerSeriesFormalBase k ∧
      (∀ n, (homStack (totalObj B hS fX hX) 𝒵).p.obj (ξ.level n) = truncationObj B hS n) ∧
      ∀ (x : (homStack (totalObj B hS fX hX) 𝒵).obj) (r : ∀ n, ξ.level n ⟶ x),
        ¬ ∀ n, (homStack (totalObj B hS fX hX) 𝒵).p.IsHomLift
          (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
            (powerSeriesFormalBase_contains B hS) n) (r n) := by
  obtain ⟨c, hc⟩ := exists_forall_toCompatibleSystems_ne B hS fX hX hXn 𝒜 hnot
  exact exists_not_restriction_of_compatible (isFiberedInGroupoids_homStack _ 𝒵 h𝒵)
    (isClassifyingInvariant_homStackClass h𝒵 hcl) (powerSeriesFormalBase k) hS
    (powerSeriesFormalBase_contains B hS) (prodTruncationSystem B hS fX hX hXn 𝒜 c)
    (prodTruncationSystem_succ B hS fX hX hXn 𝒜 c)
    (exists_ne_prodTruncationSystem B hS fX hX hXn 𝒜 c hc)

/-- **The Hom-stack is not algebraic when the comparison on `H¹` is not surjective.** Let `𝒵` be
a category fibred in groupoids over the big fppf site of `S = Spec k⟦t⟧`, with the universes of
the 2-category of algebraic stacks, and with a classifying invariant with values in `H¹(-, A)`.
If `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective, then `Mor_S(X, 𝒵)` is not an algebraic stack:
by `exists_not_isEffective_homStack` it has a formal object which is not effective, and by
Stacks 07X8 (`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`) every formal
object of an algebraic stack is effective. -/
theorem not_isAlgebraicStack_homStack
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B (base k) hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    {cl : ∀ z : 𝒵.obj, (h1Presheaf B hS 𝒜).obj (op (𝒵.p.obj z))}
    (hcl : IsClassifyingInvariant (h1Presheaf B hS 𝒜) cl)
    (hnot : ¬ Function.Surjective (toCompatibleSystems B hS fX hX hXn 𝒜)) :
    ¬ IsAlgebraicStack.{u, w'} B (base k) hS (homStack (totalObj B hS fX hX) 𝒵) :=
  not_isAlgebraicStack_powerSeriesBase_of_not_isEffective B hS _
    (isFiberedInGroupoids_homStack _ 𝒵 h𝒵)
    (exists_not_isEffective_homStack B hS fX hX hXn 𝒜 𝒵 h𝒵 hcl hnot)

end Stacks.Examples.NonAlgebraicHomStack
