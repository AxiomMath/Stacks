module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula

/-!
# The Gysin homomorphism of a divisor as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8. Stacks 0B79
asserts that the rule assigning to every `g : X' ⟶ X` locally of finite type the Gysin map
`(i')^* : CH_k(X') ⟶ CH_{k-1}(D')`, `D' = D ×_X X'`, is a bivariant class of degree `1`.

## Main definitions

* `Stacks.Chow.gysinBivariantClass`: the bivariant class of degree `1` for `i : D ⟶ X` whose
  cap operation on every test scheme is the Gysin map of the pulled-back section.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_onChow_properChowPushforward`: the Gysin map commutes
  with proper pushforward on Chow groups, for a module on the source identified with the pullback
  of the module downstairs (Stacks 02TA).
* `Stacks.Chow.gysinSystemOfInvertible_onChow_flatPullbackChow`: the Gysin map commutes with flat
  pullback on Chow groups (Stacks 0B71).
* `Stacks.Chow.gysinBivariantCap_properChowPushforward`,
  `Stacks.Chow.gysinBivariantCap_flatPullbackChow`, `Stacks.Chow.gysinBivariantCap_gysin`: the
  three conditions of Stacks 0B76 for the Gysin cap operation.

## Implementation notes

The cap operation is `Stacks.Chow.gysinBivariantCap`: on a test scheme `g : T ⟶ X` it is the
Gysin map of the section `g^*s` of `g^*𝓛`, read on the base change `D ×_X T` through the
identification of Stacks 0B6Y. It is taken at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, whose first Chern class rule is that of the invertible
module, so the group the class lives in is `A^1(D ⟶ X)` of the source.

Each of the three conditions is proved on the test scheme `T` and transported to the chosen
pullbacks through Stacks 0B6Y. The third is the commutation of the Gysin maps of the two divisors
`Z(g^*s)` and `Z(t)` on `T`, `Stacks.Chow.gysinChowOfInvertible_comm`.

## References

* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding zeroScheme
open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The Gysin map along a proper morphism, with the module identified -/

/-- **Stacks 02TA, with the module on the source identified.** Let `u : A ⟶ B` be proper over the
base, let `LB` be an invertible module on `B` with a section `sB`, and let `LA` be an invertible
module on `A` with a section `sA`, identified with `u^* LB` by an isomorphism `φ` under which the
two zero schemes agree. Then for every morphism `j : Z(sA) ⟶ Z(sB)` filling the square over `u`,
`i_B^* u_* α = j_* i_A^* α`. -/
theorem gysinSystemOfInvertible_onChow_properChowPushforward (C : ChowSituation.{u})
    {A B : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (u : A ⟶ B) [IsProper u] (hu : u ≫ pB = pA) (LB : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property LB]
    (sB : Γ(LB, ⊤)) (LA : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property LA]
    (sA : Γ(LA, ⊤)) (φ : (Scheme.Modules.pullback u).obj LB ≅ LA)
    (hZ : pullbackZeroScheme u LB sB = zeroScheme A LA sA)
    (j : (zeroScheme A LA sA).subscheme ⟶ (zeroScheme B LB sB).subscheme) [IsProper j]
    (hj : j ≫ (zeroScheme B LB sB).subschemeι = (zeroScheme A LA sA).subschemeι ≫ u)
    (hjb : j ≫ ((zeroScheme B LB sB).subschemeι ≫ pB) = (zeroScheme A LA sA).subschemeι ≫ pA)
    (k : ℤ) (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C pA pB u hu (k + 1))
    (hfacj : ProperPushforwardFactorsThroughRationalEquivalence C
      ((zeroScheme A LA sA).subschemeι ≫ pA) ((zeroScheme B LB sB).subschemeι ≫ pB) j hjb k)
    (α : chowGroup C pA (k + 1)) :
    (gysinSystemOfInvertible C).onChow pB LB sB k
        (properChowPushforward C pA pB u hu (k + 1) hfacu α) =
      properChowPushforward C ((zeroScheme A LA sA).subschemeι ≫ pA)
        ((zeroScheme B LB sB).subschemeι ≫ pB) j hjb k hfacj
        ((gysinSystemOfInvertible C).onChow pA LA sA k α) := by
  rw [gysinSystemOfInvertible_isNaturalUnderProperPushforward C pA pB u hu LB sB k
    (zeroSchemePullbackHom u LB sB) (zeroSchemePullbackHom_subschemeι u LB sB) hfacu
    (properPushforwardDescends C _ _ _ _ _) α]
  obtain rfl : j = eqToHom (congrArg Scheme.IdealSheafData.subscheme hZ.symm) ≫
      zeroSchemePullbackHom u LB sB := by
    refine (cancel_mono (zeroScheme B LB sB).subschemeι).1 ?_
    rw [hj, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
      subschemeι_eqToHom hZ.symm]
  exact (properChowPushforward_eqToHom_comp_apply_of_heq C pA
    ((zeroScheme B LB sB).subschemeι ≫ pB) k hZ.symm (zeroSchemePullbackHom u LB sB)
    (zeroSchemeSquare_comp_structureMorphism C pA pB u hu LB sB _
      (zeroSchemePullbackHom_subschemeι u LB sB)) hjb hfacj
    (properPushforwardDescends C _ _ _ _ _) _ _
    (heq_gysinHomomorphismOnChowOfInvertible C pA k LA ((Scheme.Modules.pullback u).obj LB) sA
      (AlgebraicGeometry.pullbackGlobalSections u LB sB) φ.symm hZ.symm _ _) α).symm

/-- Proper pushforward commutes with transport along an equality of degrees. -/
private theorem chowGroupDegreeEquiv_properChowPushforward_aux (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA) {k l : ℤ} (hkl : k = l)
    (hfack : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k)
    (hfacl : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq l)
    (α : chowGroup C sA k) :
    chowGroupDegreeEquiv C sB hkl (properChowPushforward C sA sB q hq k hfack α) =
      properChowPushforward C sA sB q hq l hfacl (chowGroupDegreeEquiv C sA hkl α) := by
  subst hkl
  rfl

/-! ### The Gysin map and flat pullback, on Chow groups -/

/-- **Stacks 0B71 on Chow groups, for the Gysin system of an invertible module.** For `f : X' ⟶ X`
flat of relative dimension `r` and `g : Z(f^*s) ⟶ Z(s)` the morphism of Remark 0B6Y,
`(i')^* f^* β = g^* i^* β` for every class `β ∈ CH_{k+1}(X)`. -/
theorem gysinSystemOfInvertible_onChow_flatPullbackChow (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (pA : X' ⟶ C.S) [LocallyOfFiniteType pA] (hpA : f ≫ p = pA)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C pA p f hpA r hf (k + 1))
    (hg : zeroSchemePullbackHom f L s ≫ ((zeroScheme X L s).subschemeι ≫ p) =
      (pullbackZeroScheme f L s).subschemeι ≫ pA)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ pA) ((zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemePullbackHom f L s) hg r (relativeDimension_zeroSchemePullbackHom f L s r hf) k)
    (β : chowGroup C p (k + 1)) :
    (gysinSystemOfInvertible C).onChow pA ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C pA (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C pA p f hpA r hf (k + 1) hfac β)) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ pA)
        ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s) hg r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k hfac'
        ((gysinSystemOfInvertible C).onChow p L s k β) := by
  subst hpA
  induction β using QuotientAddGroup.induction_on with
  | H z =>
    have h0 := gysinHomomorphismOfInvertible_flatPullback_of_invertible C p f r hf k L s z
    have hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1 := by ring
    have hmk : chowGroupDegreeEquiv C (f ≫ p) hcast
        (flatPullbackChow C (f ≫ p) p f rfl r hf (k + 1) hfac
          (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) z)) =
        QuotientAddGroup.mk' (rationalEquivalences C (f ≫ p) (k + (r : ℤ) + 1))
          (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) z) := by
      rw [flatPullbackChow_mk]
      exact chowGroupDegreeEquiv_mk_eq_mk_of_val C (f ≫ p) hcast _ _
        (val_cycleGroup_cast C (f ≫ p) hcast _).symm
    exact (congrArg ((gysinSystemOfInvertible C).onChow (f ≫ p) ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) (k + (r : ℤ))) hmk).trans h0

/-- The Gysin map of a Gysin system commutes with the transport of a Chow group along an equality
of structure morphisms. -/
private theorem onChow_chowGroupCongr {C : ChowSituation.{u}} (G : GysinSystem C)
    {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (h : q = q') (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (m : ℤ) (x : chowGroup C q (m + 1)) :
    G.onChow q' L s m (chowGroupCongr C h (m + 1) x) =
      chowGroupCongr C (congrArg ((zeroScheme T L s).subschemeι ≫ ·) h) m (G.onChow q L s m x) := by
  subst h
  rfl

/-- Pushforward along an isomorphism absorbs the transport of a Chow group along an equality of
the structure morphism of the source. -/
private theorem chowPushforwardOfIso_chowGroupCongr_source (C : ChowSituation.{u})
    {A B : Scheme.{u}} {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (hA : sA = sA') (u : A ⟶ B) [IsIso u]
    (hu : u ≫ sB = sA') (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA' sB u hu k (chowGroupCongr C hA k x) =
      chowPushforwardOfIso C sA sB u (hu.trans hA.symm) k x := by
  subst hA
  rfl

/-! ### The cap operation and proper pushforward -/

section Cap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- A base change square of the test schemes induces a commuting square on the divisors. -/
private theorem gysinDivisorBaseChangeIso_hom_comp_snd_comp {T T' : Scheme.{u}} (g : T ⟶ X)
    (h : T' ⟶ T)
    (h' : pullback (gysinTripleInclusion L s) (h ≫ g) ⟶ pullback (gysinTripleInclusion L s) g)
    (w : pullback.snd (gysinTripleInclusion L s) (h ≫ g) ≫ h =
      h' ≫ pullback.snd (gysinTripleInclusion L s) g) :
    (gysinDivisorBaseChangeIso L s (h ≫ g)).hom ≫ h' ≫ pullback.snd (gysinTripleInclusion L s) g =
      (gysinTripleDivisor L s (h ≫ g)).subschemeι ≫ h := by
  rw [← w, ← Category.assoc, gysinDivisorBaseChangeIso_hom_snd]

/-- **Condition (1) of Stacks 0B76 for the Gysin cap operation.** Capping with the Gysin map of
the divisor commutes with proper pushforward along a proper morphism `h : T' ⟶ T` of test
schemes and its base change `h'`. -/
theorem gysinBivariantCap_properChowPushforward {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (gysinTripleInclusion L s) (h ≫ g) ⟶ pullback (gysinTripleInclusion L s) g)
    [IsProper h']
    (sq : IsPullback (pullback.snd (gysinTripleInclusion L s) (h ≫ g)) h' h
      (pullback.snd (gysinTripleInclusion L s) g))
    (k : ℤ) (hh : h ≫ (g ≫ sX) = (h ≫ g) ≫ sX)
    (hh' : h' ≫ (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) =
      pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hh k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
      (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) h' hh'
      (k - 1))
    (α : chowGroup C ((h ≫ g) ≫ sX) k) :
    gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g k
        (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h hh k hfac α) =
      properChowPushforward C
        (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) h' hh'
        (k - 1) hfac' (gysinBivariantCap C (gysinSystemOfInvertible C) sX L s (h ≫ g) k α) := by
  set Ψ := gysinDivisorBaseChangeIso L s g
  set Ψ' := gysinDivisorBaseChangeIso L s (h ≫ g)
  set j : (gysinTripleDivisor L s (h ≫ g)).subscheme ⟶ (gysinTripleDivisor L s g).subscheme :=
    Ψ'.hom ≫ h' ≫ Ψ.inv with hjdef
  have hj : j ≫ (gysinTripleDivisor L s g).subschemeι =
      (gysinTripleDivisor L s (h ≫ g)).subschemeι ≫ h := by
    have h1 : Ψ.inv ≫ (gysinTripleDivisor L s g).subschemeι =
        pullback.snd (gysinTripleInclusion L s) g := by
      rw [Iso.inv_comp_eq, gysinDivisorBaseChangeIso_hom_snd]
    rw [hjdef, Category.assoc, Category.assoc, h1,
      gysinDivisorBaseChangeIso_hom_comp_snd_comp L s g h h' sq.w]
  have hjb : j ≫ ((gysinTripleDivisor L s g).subschemeι ≫ (g ≫ sX)) =
      (gysinTripleDivisor L s (h ≫ g)).subschemeι ≫ ((h ≫ g) ≫ sX) := by
    rw [← Category.assoc, hj, Category.assoc, hh]
  have hcomp : j ≫ Ψ.hom = Ψ'.hom ≫ h' := by simp [hjdef]
  rw [gysinBivariantCap_apply, gysinBivariantCap_apply,
    chowGroupDegreeEquiv_properChowPushforward_aux C _ _ h hh _ hfac
      (properPushforwardDescends C _ _ _ _ _),
    gysinSystemOfInvertible_onChow_properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h hh
      (gysinTripleModule L g) (gysinTripleSection L s g) (gysinTripleModule L (h ≫ g))
      (gysinTripleSection L s (h ≫ g)) ((Scheme.Modules.pullbackComp h g).app L)
      (zeroScheme_pullback_pullback h g L s) j hj hjb (k - 1) _
      (properPushforwardDescends C _ _ _ _ _)]
  have hw : (Ψ'.hom ≫ h') ≫
      (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) =
      (gysinTripleDivisor L s (h ≫ g)).subschemeι ≫ ((h ≫ g) ≫ sX) := by
    rw [Category.assoc, hh', gysinDivisorBaseChangeIso_hom_comp_structureMorphism]
  unfold chowPushforwardOfIso
  refine (properChowPushforward_comp_apply C _ _ _ j Ψ.hom (Ψ'.hom ≫ h') hcomp hjb
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g) hw (k - 1)
    _ _ (properPushforwardDescends C _ _ _ _ _) _).symm.trans ?_
  exact properChowPushforward_comp_apply C _ _ _ Ψ'.hom h' (Ψ'.hom ≫ h') rfl
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX (h ≫ g)) hh' hw (k - 1)
    _ _ _ _

/-- **Condition (2) of Stacks 0B76 for the Gysin cap operation.** Capping with the Gysin map of
the divisor commutes with flat pullback along a flat morphism `h : T' ⟶ T` of test schemes of
relative dimension `r` and its base change `h'`. -/
theorem gysinBivariantCap_flatPullbackChow {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (gysinTripleInclusion L s) (h ≫ g) ⟶ pullback (gysinTripleInclusion L s) g)
    [LocallyOfFiniteType h'] [Flat h']
    (sq : IsPullback (pullback.snd (gysinTripleInclusion L s) (h ≫ g)) h' h
      (pullback.snd (gysinTripleInclusion L s) g))
    (k : ℤ) (hh : h ≫ (g ≫ sX) = (h ≫ g) ≫ sX)
    (hh' : h' ≫ (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) =
      pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
    (hr' : AlgebraicGeometry.RelativeDimension h' r)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hh r hr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
      (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) h' hh' r hr'
      (k - 1))
    (α : chowGroup C (g ≫ sX) k) :
    HEq (gysinBivariantCap C (gysinSystemOfInvertible C) sX L s (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h hh r hr k hfac α))
      (flatPullbackChow C
        (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) h' hh' r
        hr' (k - 1) hfac' (gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g k α)) := by
  set Ψ := gysinDivisorBaseChangeIso L s g
  set Ψ' := gysinDivisorBaseChangeIso L s (h ≫ g)
  set p : T' ⟶ C.S := (h ≫ g) ≫ sX with hp
  have hZZ : pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g) =
      gysinTripleDivisor L s (h ≫ g) := zeroScheme_pullback_pullback h g L s
  set d := zeroSchemePullbackHom h (gysinTripleModule L g) (gysinTripleSection L s g)
  set u₁ : (pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g)).subscheme ⟶
      pullback (gysinTripleInclusion L s) (h ≫ g) :=
    eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ) ≫ Ψ'.hom with hu₁def
  have hsq : d ≫ Ψ.hom = u₁ ≫ h' := by
    refine (cancel_mono (pullback.snd (gysinTripleInclusion L s) g)).1 ?_
    rw [Category.assoc, gysinDivisorBaseChangeIso_hom_snd, hu₁def, Category.assoc,
      Category.assoc, gysinDivisorBaseChangeIso_hom_comp_snd_comp L s g h h' sq.w,
      ← Category.assoc, subschemeι_eqToHom hZZ]
    exact zeroSchemePullbackHom_subschemeι h (gysinTripleModule L g) (gysinTripleSection L s g)
  have hd : d ≫ ((gysinTripleDivisor L s g).subschemeι ≫ (g ≫ sX)) =
      (pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g)).subschemeι ≫ p :=
    zeroSchemePullbackHom_comp h (gysinTripleModule L g) (gysinTripleSection L s g) C (g ≫ sX)
      p hh
  have hu₁ : u₁ ≫ (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫
      (gysinTripleInclusion L s ≫ sX)) =
      (pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g)).subschemeι ≫ p := by
    rw [hu₁def, Category.assoc, gysinDivisorBaseChangeIso_hom_comp_structureMorphism,
      ← Category.assoc, subschemeι_eqToHom hZZ]
  have key : ∀ (a b : ℤ) (_hab : a = b) (x : chowGroup C p (a + 1))
      (y : chowGroup C p (b + 1)), HEq x y →
      HEq (chowPushforwardOfIso C
          ((pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g)).subschemeι ≫ p)
          (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
          u₁ hu₁ a ((gysinSystemOfInvertible C).onChow p
            ((Scheme.Modules.pullback h).obj (gysinTripleModule L g))
            (AlgebraicGeometry.pullbackGlobalSections h (gysinTripleModule L g)
              (gysinTripleSection L s g)) a x))
        (chowPushforwardOfIso C
          ((pullbackZeroScheme h (gysinTripleModule L g) (gysinTripleSection L s g)).subschemeι ≫ p)
          (pullback.fst (gysinTripleInclusion L s) (h ≫ g) ≫ (gysinTripleInclusion L s ≫ sX))
          u₁ hu₁ b ((gysinSystemOfInvertible C).onChow p
            ((Scheme.Modules.pullback h).obj (gysinTripleModule L g))
            (AlgebraicGeometry.pullbackGlobalSections h (gysinTripleModule L g)
              (gysinTripleSection L s g)) b y)) := by
    intro a b hab x y hxy
    subst hab
    rw [eq_of_heq hxy]
  rw [gysinBivariantCap_apply, gysinBivariantCap_apply,
    flatPullbackChow_chowPushforwardOfIso C _ _ _ _ Ψ.hom
      (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g) u₁ hu₁ d hd h' hh' hsq r
      (relativeDimension_zeroSchemePullbackHom h _ _ r hr) hr' (k - 1)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hfac',
    ← gysinSystemOfInvertible_onChow_flatPullbackChow C (g ≫ sX) h r hr (k - 1)
      (gysinTripleModule L g) (gysinTripleSection L s g) p hh
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hd,
    ← gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C h g p L s,
    chowPushforwardOfIso_comp_apply]
  refine key _ _ (by ring) _ _ ?_
  refine (chowGroupDegreeEquiv_heq C p _ _).trans ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C p _ _).symm
  exact flatPullbackChow_heq_of_degree C p (g ≫ sX) h hh r hr (by ring) _ _
    (chowGroupDegreeEquiv_heq C (g ≫ sX) _ α).symm

/-- The identification of the intersection of the two divisors on the test scheme with the zero
scheme of the pulled-back section on the base change lies over the identification of
Stacks 0B6Y. -/
private theorem gysinBivariantCap_gysin_comparison {T : Scheme.{u}} (g : T ⟶ X) (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤))
    (e : pullback (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≅
      (zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subscheme)
    (he : e.hom ≫ (zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι =
      bivariantBaseChangeMap (gysinTripleInclusion L s) g (zeroScheme T M t).subschemeι)
    (e₀ : (zeroSchemeInter (gysinTripleModule L g) M (gysinTripleSection L s g) t).subscheme ≅
      (zeroSchemeInter M (gysinTripleModule L g) t (gysinTripleSection L s g)).subscheme)
    (he₀ : e₀.hom ≫ (zeroSchemeInter M (gysinTripleModule L g) t
        (gysinTripleSection L s g)).subschemeι ≫ (zeroScheme T M t).subschemeι =
      (zeroSchemeInter (gysinTripleModule L g) M (gysinTripleSection L s g) t).subschemeι ≫
        (zeroScheme T (gysinTripleModule L g) (gysinTripleSection L s g)).subschemeι) :
    ((e₀.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (zeroScheme_pullback_comp (zeroScheme T M t).subschemeι g L s)) ≫
      (gysinDivisorBaseChangeIso L s ((zeroScheme T M t).subschemeι ≫ g)).hom) ≫ e.hom) ≫
      (zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι =
      (zeroSchemeInter (gysinTripleModule L g) M (gysinTripleSection L s g) t).subschemeι ≫
        (gysinDivisorBaseChangeIso L s g).hom := by
  have hb : bivariantBaseChangeMap (gysinTripleInclusion L s) g (zeroScheme T M t).subschemeι ≫
      pullback.snd (gysinTripleInclusion L s) g =
      pullback.snd (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≫
        (zeroScheme T M t).subschemeι := by
    simp [bivariantBaseChangeMap]
  refine (cancel_mono (pullback.snd (gysinTripleInclusion L s) g)).1 ?_
  rw [Category.assoc, Category.assoc, ← Category.assoc e.hom, he, hb]
  simp only [Category.assoc, gysinDivisorBaseChangeIso_hom_snd,
    gysinDivisorBaseChangeIso_hom_snd_assoc]
  rw [← Category.assoc (eqToHom _), subschemeι_eqToHom
    (zeroScheme_pullback_comp (zeroScheme T M t).subschemeι g L s), he₀]

/-- **Condition (3) of Stacks 0B76 for the Gysin cap operation.** Capping with the Gysin map of
the divisor `D = Z(s)` commutes with the Gysin map of the zero scheme `D'` of a section `t` of an
invertible module `M` on a test scheme `T`. -/
theorem gysinBivariantCap_gysin {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (k : ℤ)
    (e : pullback (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≅
      (zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subscheme)
    (he : e.hom ≫ (zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι =
      bivariantBaseChangeMap (gysinTripleInclusion L s) g (zeroScheme T M t).subschemeι)
    (hbase : e.hom ≫ ((zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι ≫ pullback.fst (gysinTripleInclusion L s) g ≫
          (gysinTripleInclusion L s ≫ sX)) =
      pullback.fst (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≫
        (gysinTripleInclusion L s ≫ sX))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≫
        (gysinTripleInclusion L s ≫ sX))
      ((zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι ≫ pullback.fst (gysinTripleInclusion L s) g ≫
          (gysinTripleInclusion L s ≫ sX)) e.hom hbase (k - 1))
    (α : chowGroup C (g ≫ sX) (k + 1)) :
    properChowPushforward C
        (pullback.fst (gysinTripleInclusion L s) ((zeroScheme T M t).subschemeι ≫ g) ≫
          (gysinTripleInclusion L s ≫ sX))
        ((zeroScheme (pullback (gysinTripleInclusion L s) g)
          ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
            M t)).subschemeι ≫ pullback.fst (gysinTripleInclusion L s) g ≫
            (gysinTripleInclusion L s ≫ sX)) e.hom hbase (k - 1) hfac
        (gysinBivariantCap C (gysinSystemOfInvertible C) sX L s
          ((zeroScheme T M t).subschemeι ≫ g) k
          (chowGroupCongr C (Category.assoc (zeroScheme T M t).subschemeι g sX).symm k
            ((gysinSystemOfInvertible C).onChow (g ≫ sX) M t k α))) =
      (gysinSystemOfInvertible C).onChow
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX))
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t) (k - 1)
        (Eq.mp (congrArg (chowGroup C
            (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)))
          (by omega : (k + 1) - 1 = (k - 1) + 1))
          (gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g (k + 1) α)) := by
  obtain ⟨e₀, he₀⟩ := exists_iso_zeroSchemeInter (gysinTripleModule L g) M
    (gysinTripleSection L s g) t
  have hZ' := zeroScheme_pullback_comp (zeroScheme T M t).subschemeι g L s
  have hk₁ : k + 1 - 1 = k - 1 + 1 := by omega
  have hk₂ : k + 1 = k - 1 + 1 + 1 := by omega
  conv_rhs => rw [eqMp_chowGroup C _ hk₁,
    gysinBivariantCap_apply,
    chowGroupDegreeEquiv_chowPushforwardOfIso C _ _ (gysinDivisorBaseChangeIso L s g).hom
      (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g)
      hk₁,
    GysinSystem.onChow_chowGroupDegreeEquiv (gysinSystemOfInvertible C) _ _ _
      hk₁ (show k + 1 - 1 + 1 = k - 1 + 1 + 1 by omega),
    chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  conv_lhs =>
    arg 2
    rw [gysinBivariantCap_apply]
    arg 2
    arg 2
    rw [← chowGroupCongr_chowGroupDegreeEquiv]
    arg 2
    rw [GysinSystem.onChow_chowGroupDegreeEquiv (gysinSystemOfInvertible C) _ _ _
      (show k = k - 1 + 1 by omega) hk₂]
  conv_lhs =>
    arg 2
    arg 2
    rw [← gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C
      (zeroScheme T M t).subschemeι g (((zeroScheme T M t).subschemeι ≫ g) ≫ sX) L s]
    arg 2
    rw [onChow_chowGroupCongr]
  conv_lhs =>
    arg 2
    arg 2
    rw [chowPushforwardOfIso_chowGroupCongr_source]
  have h73 := gysinChowOfInvertible_comm C (g ≫ sX) (k - 1) (gysinTripleModule L g) M
    (gysinTripleSection L s g) t e₀ he₀
    (chowGroupDegreeEquiv C (g ≫ sX) hk₂ α)
  simp only [← gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible] at h73
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    rw [← h73]
  conv_lhs =>
    arg 2
    rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  have hj := gysinBivariantCap_gysin_comparison L s g M t e he e₀ he₀
  have hjb := (by
    rw [← Category.assoc, hj, Category.assoc,
      gysinDivisorBaseChangeIso_hom_comp_structureMorphism] :
    ((e₀.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.subscheme hZ') ≫
      (gysinDivisorBaseChangeIso L s ((zeroScheme T M t).subschemeι ≫ g)).hom) ≫ e.hom) ≫
      ((zeroScheme (pullback (gysinTripleInclusion L s) g)
        ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g)
          M t)).subschemeι ≫ pullback.fst (gysinTripleInclusion L s) g ≫
          (gysinTripleInclusion L s ≫ sX)) =
      (zeroSchemeInter (gysinTripleModule L g) M (gysinTripleSection L s g) t).subschemeι ≫
        ((gysinTripleDivisor L s g).subschemeι ≫ g ≫ sX))
  have hfinal := gysinSystemOfInvertible_onChow_properChowPushforward C
    ((gysinTripleDivisor L s g).subschemeι ≫ g ≫ sX)
    (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX))
    (gysinDivisorBaseChangeIso L s g).hom
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g)
    ((Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s) g)).obj M)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (gysinTripleInclusion L s) g) M t)
    (zeroSchemeRestrictModule (gysinTripleModule L g) M (gysinTripleSection L s g))
    (restrictSectionToZeroScheme (gysinTripleModule L g) M (gysinTripleSection L s g) t)
    ((Scheme.Modules.pullbackComp (gysinDivisorBaseChangeIso L s g).hom
        (pullback.snd (gysinTripleInclusion L s) g)).app M ≪≫
      eqToIso (congrArg (fun q ↦ (Scheme.Modules.pullback q).obj M)
        (gysinDivisorBaseChangeIso_hom_snd L s g)))
    (zeroScheme_pullback_comp_eq (gysinDivisorBaseChangeIso L s g).hom
      (pullback.snd (gysinTripleInclusion L s) g) (gysinTripleDivisor L s g).subschemeι
      (gysinDivisorBaseChangeIso_hom_snd L s g) M t)
    ((e₀.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.subscheme hZ') ≫
      (gysinDivisorBaseChangeIso L s ((zeroScheme T M t).subschemeι ≫ g)).hom) ≫ e.hom)
    hj hjb (k - 1) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (g ≫ sX) (gysinTripleModule L g)
      (gysinTripleSection L s g) (k - 1 + 1)
      (chowGroupDegreeEquiv C (g ≫ sX) hk₂ α))
  refine Eq.trans ?_ hfinal.symm
  exact Eq.symm (properChowPushforward_comp_apply C _ _ _ _ e.hom _ rfl _ hbase hjb (k - 1) _
    hfac _ _)

/-! ### The Gysin bivariant class -/

/-- Let `(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8 on a scheme `X` locally of finite
type over the base. The rule assigning to every `g : X' ⟶ X` locally of finite type the Gysin map
`(i')^* : CH_k(X') ⟶ CH_{k-1}(D')` of the pulled-back section, where `D' = D ×_X X'`, is a
bivariant class of degree `1` for `i`: the class below caps by that Gysin map on every test
scheme. -/
@[stacks 0B79]
def gysinBivariantClass :
    { c : BivariantClass C (gysinSystemOfInvertible C) (gysinTripleInclusion L s ≫ sX) sX
        (gysinTripleInclusion L s) rfl 1 //
      IsGysinBivariantClass C (gysinSystemOfInvertible C) sX L s c } :=
  ⟨{ cap := fun g _ k ↦ gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g k
     cap_properPushforward := by
       intro T T' g _ h _ h' sq hfst k α
       have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
       exact gysinBivariantCap_properChowPushforward C sX L s g h h' sq k _ _ _ _ α
     cap_flatPullbackChow := by
       intro T T' g _ h _ _ r hr h' sq hfst k α
       have : LocallyOfFiniteType h' :=
         MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
       have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
       exact gysinBivariantCap_flatPullbackChow C sX L s g h r hr h' sq k _ _ _ _ _ α
     cap_gysin := by
       intro T g _ M _ t k _ _ _ _ e he hbase α
       exact gysinBivariantCap_gysin C sX L s g M t k e he hbase _ α },
    fun _ _ _ _ ↦ rfl⟩

end Cap

end Stacks.Chow

end
