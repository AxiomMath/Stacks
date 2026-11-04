module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence

/-!
# Base change of a scheme over a field to an algebraic closure

Let `k` be a field with an algebraically closed extension `Ω` and let `X` be a scheme over `k`.
Write `X_Ω` for the base change and suppose that `X_Ω` is connected. Then `X` is connected, the
composite of the induced homomorphisms of étale fundamental groups

```
π₁(X_Ω) ⟶ π₁(X) ⟶ π₁(Spec k)
```

is trivial, and `π₁(X) ⟶ π₁(Spec k)` is surjective. Exactness at `π₁(X)` is proved under the
hypothesis that every finite étale cover of `X` splitting over `X_Ω` comes from `Spec k`.

## Main results

* `AlgebraicGeometry.connectedSpace_of_connectedSpace_pullback_specMap_algebraMap`: if `X_Ω` is
  connected, so is `X`.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_isAlgClosed`: a finite
  étale cover of `Spec k` becomes a finite coproduct of copies of `Spec Ω`.
* `AlgebraicGeometry.etaleFundamentalGroupMap_comp_eq_one_of_isFiniteCoproductOfTerminal`: the
  composite homomorphism attached to two composable morphisms of connected schemes is trivial as
  soon as the composite base-change functor lands in finite coproducts of copies of the source.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_pullback_isAlgClosed`:
  base change of a finite étale cover of `Spec k` to `X_Ω` is a finite coproduct of copies of
  `X_Ω`.
* `AlgebraicGeometry.etaleFundamentalGroupMap_comp_eq_one_isAlgClosed`: the composite
  `π₁(X_Ω) → π₁(X) → π₁(Spec k)` is trivial.
* `AlgebraicGeometry.isConnected_finiteEtaleBaseChange_isAlgClosed`: a connected finite étale
  cover of `Spec k` stays connected after base change to `X`.
* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_isAlgClosed`: base change of finite
  étale covers along `X ⟶ Spec k` is fully faithful.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_isAlgClosed`: the homomorphism
  `π₁(X) → π₁(Spec k)` is surjective.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_isAlgClosed`: the sequence
  `π₁(X_Ω) → π₁(X) → π₁(Spec k) → 1` is exact, provided every finite étale cover of `X` that
  splits over `X_Ω` comes from `Spec k`.

## References

* [Stacks Project, Tag 0BTX](https://stacks.math.columbia.edu/tag/0BTX)
* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-- The residue field of an algebraically closed field is separably closed. -/
private theorem isSepClosed_residueField_of_isAlgClosed (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    IsSepClosed (IsLocalRing.ResidueField Ω) :=
  have : IsAlgClosed (IsLocalRing.ResidueField Ω) :=
    IsAlgClosed.of_ringEquiv Ω _ ((RingEquiv.quotientBot Ω).symm.trans
      (Ideal.quotEquivOfEq IsLocalRing.maximalIdeal_eq_bot.symm))
  inferInstance

/-- If the base change of a scheme `X` over `k` to a field extension `Ω` is connected, then so is
`X`. -/
@[stacks 0BTX "connectedness of `X`, implicit in the statement since `π₁(X)` appears in it"]
theorem connectedSpace_of_connectedSpace_pullback_specMap_algebraMap
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))] :
    ConnectedSpace ↥X :=
  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).surjective.connectedSpace
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).continuous

/-- **A finite étale cover of `Spec k` splits over an algebraically closed extension.** Its base
change to `Spec Ω` is a finite coproduct of copies of `Spec Ω`. -/
@[ega "IV 2.7.3" "more general"]
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (V : FiniteEtaleOver (Spec (.of k))) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj V) :=
  have := isSepClosed_residueField_of_isAlgClosed Ω
  isFiniteCoproductOfTerminal_of_henselian_isSepClosed Ω _

/-- Let `a : X'' ⟶ X'` and
`b : X' ⟶ X` be morphisms of connected schemes and let `x` be a geometric point of `X''`. If
every finite étale cover of `X` becomes a finite coproduct of copies of `X''` after base change
along `b` and then along `a`, then the composite

```
π₁(X'', x) ⟶ π₁(X', a ∘ x) ⟶ π₁(X, b ∘ a ∘ x)
```

is the trivial homomorphism. -/
theorem etaleFundamentalGroupMap_comp_eq_one_of_isFiniteCoproductOfTerminal
    {X'' X' X : Scheme.{u}} [ConnectedSpace ↥X''] [ConnectedSpace ↥X'] [ConnectedSpace ↥X]
    (a : X'' ⟶ X') (b : X' ⟶ X) (x : GeometricPoint X'')
    (hsplit : ∀ V : FiniteEtaleOver X, IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange a).obj ((finiteEtaleBaseChange b).obj V))) :
    (etaleFundamentalGroupMap b (x.map a)).toMonoidHom.comp
      (etaleFundamentalGroupMap a x).toMonoidHom = 1 := by
  let F := finiteEtaleFiberFintypeFunctor X ((x.map a).map b)
  let F' := finiteEtaleFiberFintypeFunctor X' (x.map a)
  let F'' := finiteEtaleFiberFintypeFunctor X'' x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso b (x.map a)
  let t' := finiteEtaleFiberFintypeFunctorBaseChangeIso a x
  let d := galoisFunctorDataOfFiberIso F F' (finiteEtaleBaseChange b) t
  let d' := galoisFunctorDataOfFiberIso F' F'' (finiteEtaleBaseChange a) t'
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X ((x.map a).map b)
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X' (x.map a)
  let _gF'' : IsGaloisCategory (setValuedFiberFunctor F'') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X'' x
  have hone : d.hom.toMonoidHom.comp d'.hom.toMonoidHom = 1 :=
    (comp_hom_eq_one_iff_forall_isFiniteCoproductOfTerminal F F' F''
      (finiteEtaleBaseChange b) (finiteEtaleBaseChange a) t t' d d').mpr hsplit
  ext ρ
  obtain ⟨σ, hσ⟩ := (autMulEquivEtaleFundamentalGroup X'' x).surjective ρ
  have hd' := autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom a x d' σ
  have hd := autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom b (x.map a) d (d'.hom σ)
  have hz : d.hom (d'.hom σ) = 1 := by simpa using DFunLike.congr_fun hone σ
  show etaleFundamentalGroupMap b (x.map a) (etaleFundamentalGroupMap a x ρ) = 1
  rw [← hσ, ← hd', ← hd, hz, map_one]

/-- **The composite base change of a finite étale cover of `Spec k` to `X_Ω` splits**: base
change along `f : X ⟶ Spec k` and then along the projection `X_Ω ⟶ X` gives a finite coproduct
of copies of `X_Ω`. -/
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_pullback_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (V : FiniteEtaleOver (Spec (.of k))) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj
        ((finiteEtaleBaseChange f).obj V)) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hg
  have hex := exactFunctor_finiteEtaleBaseChange (pullback.snd f g) x
  have h₁ : PreservesFiniteLimits (finiteEtaleBaseChange (pullback.snd f g)) := hex.1
  have h₂ : PreservesFiniteColimits (finiteEtaleBaseChange (pullback.snd f g)) := hex.2
  have hsplit : IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (pullback.snd f g)).obj ((finiteEtaleBaseChange g).obj V)) :=
    isFiniteCoproductOfTerminal_map _
      (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_isAlgClosed k Ω V)
  exact isFiniteCoproductOfTerminal_of_iso (((finiteEtaleBaseChangeComp (pullback.snd f g) g
      (pullback.fst f g ≫ f) pullback.condition).app V).symm ≪≫
    (finiteEtaleBaseChangeComp (pullback.fst f g) f (pullback.fst f g ≫ f) rfl).app V) hsplit

/-- For a field `k` with an
algebraically closed extension `Ω`, a scheme `X` over `k` whose base change `X_Ω` is connected,
and a geometric point `x` of `X_Ω`, the composite

```
π₁(X_Ω, x) ⟶ π₁(X, x) ⟶ π₁(Spec k, x)
```

is the trivial homomorphism. -/
@[stacks 0BTX "triviality of the composite `π₁(X_k̄) → π₁(X) → π₁(Spec k)`",
  sga "1 XIII 4.0" "vu = 1"]
theorem etaleFundamentalGroupMap_comp_eq_one_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    (etaleFundamentalGroupMap f
          (x.map (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))).toMonoidHom.comp
        (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) x).toMonoidHom = 1 := by
  have : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  exact etaleFundamentalGroupMap_comp_eq_one_of_isFiniteCoproductOfTerminal _ f x
    (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_pullback_isAlgClosed k Ω f x)

/-! ### Surjectivity of `π₁(X) → π₁(Spec k)` -/

/-- **A scheme finite over the spectrum of a field is discrete.** -/
@[ega "II 6.1.7" "special case"]
theorem discreteTopology_of_isFinite_over_field (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [IsFinite p] : DiscreteTopology ↥Y := by
  have h : p ⁻¹' {(default : ↥(Spec (.of k)))} = (Set.univ : Set ↥Y) :=
    Set.eq_univ_of_forall fun a ↦ Subsingleton.elim _ _
  rw [← isDiscrete_univ_iff, ← h]
  exact p.isDiscrete_preimage_singleton default

/-- **A connected scheme finite over the spectrum of a field has at most one point.** -/
theorem subsingleton_of_isFinite_over_field (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [IsFinite p] [ConnectedSpace ↥Y] : Subsingleton ↥Y := by
  have := discreteTopology_of_isFinite_over_field k p
  refine ⟨fun a b ↦ ?_⟩
  rcases isClopen_iff.mp (isClopen_discrete ({a} : Set ↥Y)) with h | h
  · exact absurd (h ▸ rfl : a ∈ (∅ : Set ↥Y)) (Set.notMem_empty a)
  · exact (Set.eq_univ_iff_forall.mp h b).symm

/-- **A connected finite étale scheme over `Spec k` has a surjective `Ω`-point over `Spec k`,
for `Ω` an algebraically closed extension of `k`.** -/
theorem exists_surjective_lift_specMap_algebraMap (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))
    [IsFinite p] [Etale p] [ConnectedSpace ↥Y] :
    ∃ l : Spec (.of Ω) ⟶ Y,
      l ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧ Surjective l := by
  have hsub := subsingleton_of_isFinite_over_field k p
  obtain ⟨v⟩ : Nonempty ↥Y := inferInstance
  obtain ⟨l, hl, hlv⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) v (Subsingleton.elim _ _)
  exact ⟨l, hl, ⟨fun y ↦ ⟨default, hlv.trans (hsub.elim v y)⟩⟩⟩

/-- **A connected finite étale scheme over `Spec k` stays connected after base change to a
scheme whose own base change to `Ω` is connected.** -/
@[ega "III 4.3.4" "special case"]
theorem connectedSpace_pullback_of_connectedSpace_pullback_specMap_algebraMap
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : Y ⟶ Spec (.of k))
    [IsFinite p] [Etale p] [ConnectedSpace ↥Y]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))] :
    ConnectedSpace ↥(pullback p f) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hg
  obtain ⟨l, hl, hlsurj⟩ := exists_surjective_lift_specMap_algebraMap k Ω p
  have hw : (pullback.snd f g ≫ l) ≫ p = pullback.fst f g ≫ f := by
    rw [Category.assoc, hl, ← pullback.condition]
  let m : pullback f g ⟶ pullback p f :=
    pullback.lift (pullback.snd f g ≫ l) (pullback.fst f g) hw
  have hm1 : m ≫ pullback.fst p f = pullback.snd f g ≫ l := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd p f = pullback.fst f g := pullback.lift_snd _ _ _
  have hbig : IsPullback (pullback.snd f g) (m ≫ pullback.snd p f) (l ≫ p) f := by
    rw [hm2, hl]
    exact (IsPullback.of_hasPullback f g).flip
  have hsq : IsPullback (pullback.snd f g) m l (pullback.fst p f) :=
    hbig.of_bot hm1.symm (IsPullback.of_hasPullback p f)
  have hmsurj : Surjective m := MorphismProperty.of_isPullback (P := @Surjective) hsq hlsurj
  exact m.surjective.connectedSpace m.continuous

/-- A categorically connected finite étale cover of `Spec k` stays categorically connected after
base change to `X`, as soon as the base change of `X` to an algebraically closed extension `Ω` of
`k` is connected. -/
theorem isConnected_finiteEtaleBaseChange_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (V : FiniteEtaleOver (Spec (.of k))) (hV : PreGaloisCategory.IsConnected V) :
    PreGaloisCategory.IsConnected ((finiteEtaleBaseChange f).obj V) := by
  have hVfin : IsFinite (V.hom : V.left ⟶ Spec (.of k)) := V.prop.1
  have hVet : Etale (V.hom : V.left ⟶ Spec (.of k)) := V.prop.2
  have hVconn : ConnectedSpace ↥V.left := connectedSpace_left_of_isConnected V hV
  have hconn : ConnectedSpace ↥(pullback (V.hom : V.left ⟶ Spec (.of k)) f) :=
    connectedSpace_pullback_of_connectedSpace_pullback_specMap_algebraMap k Ω f
      (Y := V.left) V.hom
  exact @isConnected_of_connectedSpace_left _ ((finiteEtaleBaseChange f).obj V) hconn

/-- Base change of finite étale covers along `f : X ⟶ B` between connected schemes, with `X`
carrying a geometric point `x`, induces a surjection on fundamental groups and is fully faithful
as soon as it preserves connected objects. -/
private theorem surjective_and_fullyFaithful_finiteEtaleBaseChange {X B : Scheme.{u}}
    [ConnectedSpace ↥X] [ConnectedSpace ↥B] (f : X ⟶ B) (x : GeometricPoint X)
    (h : ∀ V : FiniteEtaleOver B, PreGaloisCategory.IsConnected V →
      PreGaloisCategory.IsConnected ((finiteEtaleBaseChange f).obj V)) :
    Function.Surjective (galoisFunctorDataOfFiberIso (finiteEtaleFiberFintypeFunctor B (x.map f))
      (finiteEtaleFiberFintypeFunctor X x) (finiteEtaleBaseChange f)
      (finiteEtaleFiberFintypeFunctorBaseChangeIso f x)).hom ∧
    Nonempty (finiteEtaleBaseChange f).FullyFaithful := by
  let H := finiteEtaleBaseChange f
  let F := finiteEtaleFiberFintypeFunctor B (x.map f)
  let F' := finiteEtaleFiberFintypeFunctor X x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso f x
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor B (x.map f)
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X x
  let star := finiteEtaleOverTerminal B
  let star' := finiteEtaleOverTerminal X
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange f x
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have T := surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs
  exact ⟨(T.out 3 1).mp h, (T.out 3 2).mp h⟩

/-- **Base change of finite étale covers along `X ⟶ Spec k` is fully faithful**, for a field `k`
with an algebraically closed extension `Ω` and a scheme `X` over `k` whose base change `X_Ω` is
connected. -/
theorem fullyFaithful_finiteEtaleBaseChange_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint X) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    Nonempty (finiteEtaleBaseChange f).FullyFaithful := by
  have : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  exact (surjective_and_fullyFaithful_finiteEtaleBaseChange f x
    (isConnected_finiteEtaleBaseChange_isAlgClosed k Ω f)).2

/-- For a field `k` with an algebraically closed
extension `Ω`, a scheme `X` over `k` whose base change `X_Ω` is connected, and a geometric point
`x` of `X`, the induced homomorphism

```
π₁(X, x) ⟶ π₁(Spec k, x)
```

is surjective. -/
@[stacks 0BTX "surjectivity of `π₁(X) → π₁(Spec k)`", sga "7 I 5.2" "surjectivity of π₁(X_η"]
theorem surjective_etaleFundamentalGroupMap_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint X) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    Function.Surjective (etaleFundamentalGroupMap f x) := by
  have : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  let B := Spec (CommRingCat.of k)
  let d := galoisFunctorDataOfFiberIso (finiteEtaleFiberFintypeFunctor B (x.map f))
    (finiteEtaleFiberFintypeFunctor X x) (finiteEtaleBaseChange f)
    (finiteEtaleFiberFintypeFunctorBaseChangeIso f x)
  have hdsurj : Function.Surjective d.hom :=
    (surjective_and_fullyFaithful_finiteEtaleBaseChange f x
      (isConnected_finiteEtaleBaseChange_isAlgClosed k Ω f)).1
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup B (x.map f)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup X x σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom f x d σ, hσ]
  exact (autMulEquivEtaleFundamentalGroup B (x.map f)).apply_symm_apply ρ

/-! ### Exactness at `π₁(X)` -/

/-- **A finite étale cover of `X` coming from `Spec k` splits over `X_Ω`**: its base change to
`X_Ω` is a finite coproduct of copies of `X_Ω`. -/
theorem isFiniteCoproductOfTerminal_of_essImage_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (V : FiniteEtaleOver X) (hV : (finiteEtaleBaseChange f).essImage V) :
    IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj V) := by
  obtain ⟨W, ⟨e⟩⟩ := hV
  exact isFiniteCoproductOfTerminal_of_iso ((finiteEtaleBaseChange _).mapIso e)
    (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_pullback_isAlgClosed k Ω f x W)

/-- For a field `k` with an algebraically closed extension `Ω` and a scheme `X` over `k`
whose base change `X_Ω` is connected, the sequence

```
π₁(X_Ω, x) → π₁(X, x) → π₁(Spec k, x) → 1
```

is exact as soon as every finite étale cover of `X` whose base change to `X_Ω` is a finite
coproduct of copies of `X_Ω` comes from `Spec k`. -/
theorem isExactSequence_etaleFundamentalGroupMap_isAlgClosed
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hback : ∀ V : FiniteEtaleOver X, IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj V) →
      (finiteEtaleBaseChange f).essImage V) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    IsExactSequence
      (etaleFundamentalGroupMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) x)
      (etaleFundamentalGroupMap f
        (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))) := by
  have : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  exact isExactSequence_etaleFundamentalGroupMap
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) f x
    (fullyFaithful_finiteEtaleBaseChange_isAlgClosed k Ω f
      (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))))
    (fun V ↦ ⟨isFiniteCoproductOfTerminal_of_essImage_isAlgClosed k Ω f x V, hback V⟩)

end AlgebraicGeometry

end
