module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FieldExtensionStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.CohenMacaulay.LocusBaseChange
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksFrontier.RingTheory.Serre.FlatAscent

/-!
# Cohen-Macaulay local rings after extension of the ground field

Let a scheme `X` over a field `k` be base changed to a field extension `K / k`. The local ring
at a point of the base change is Cohen-Macaulay exactly when the local ring at its image in `X`
is Cohen-Macaulay. For a locally Noetherian scheme the extension is required to be finitely
generated; for a scheme locally of finite type over `k`, the extension is arbitrary.

Both statements come from one criterion in which the hypothesis is the disjunction "one of the
two extensions `κ(x)/k`, `K/k` is essentially of finite type". A finitely generated field
extension is essentially of finite type, which gives the first; a scheme locally of finite type
over `k` has stalks essentially of finite type over `k`, which gives the second.

A finitely generated field extension `K = k(x₁, …, xₙ)` is `Algebra.EssFiniteType k K`, since
`IntermediateField.fg_top_iff` reads `(⊤ : IntermediateField k K).FG ↔ Algebra.EssFiniteType k K`;
this is the spelling already used for the same phrase in the ring-level Tags 045M and 045N, and
it covers transcendental extensions such as `k(t)/k`, which are not finitely generated as
`k`-algebras.

## Main results

* `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_iff_of_finiteType_fieldExtension` treats a
  finitely generated extension of the ground field.
* `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_iff_of_locallyOfFiniteType` treats an
  arbitrary field extension when the scheme is locally of finite type over the ground field.
* `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_baseChange_iff` is the common criterion,
  with the essential-finite-type disjunction as its hypothesis.

## Implementation notes

Cohen-Macaulayness of a local ring `R` is `IsCohenMacaulayLocalRing R`. The base change is the
categorical pullback of the structure morphism along `Spec K ⟶ Spec k`, and the condition that
`x'` lies over `x` is the corresponding equality on underlying points. The two assertions in
the source are independent and are therefore stated separately.

The chain below presents the local ring of the base change as a localization of the
pushout `𝒪_{X,x} ⊗_k K` (Stacks 0C4Y) and transfers Cohen-Macaulayness across the resulting
flat local homomorphism, whose closed fibre is a localization of `κ(x) ⊗_k K`.

## References

* [Stacks Project, Tag 045P](https://stacks.math.columbia.edu/tag/045P)
-/

@[expose] public section

open CategoryTheory Limits
open RingTheory.Sequence
open IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- A local ring which is a localization of `A` is the localization of `A` at the contraction of
its maximal ideal. -/
private lemma localization_isLocalizationAtPrime_of_localTarget
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (M : Submonoid A) [IsLocalization M C] [IsLocalRing C] :
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap (algebraMap A C)) := by
  let p := (IsLocalRing.maximalIdeal C).comap (algebraMap A C)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  change IsLocalization p.primeCompl C
  exact IsLocalization.of_le_of_exists_dvd M p.primeCompl
    (fun x hx => IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units C ⟨x, hx⟩))
    fun x hx => (IsLocalization.algebraMap_isUnit_iff (R := A) (S := C) (M := M)).mp
      (IsLocalRing.notMem_maximalIdeal.mp (by simpa [p] using hx))

/-- Transport of a localization at a prime along a ring isomorphism. -/
private noncomputable def localizationAtPrimeCongr {B C : Type*} [CommRing B] [CommRing C]
    (e : B ≃+* C) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime] (h : P = Q.comap e) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv (M := P.primeCompl) (T := Q.primeCompl)
    (Localization.AtPrime P) (Localization.AtPrime Q) e <| by
    refine Submonoid.ext fun x => ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact fun hx => hy (by simpa [h] using hx)
    · intro hx
      exact ⟨e.symm x, fun hy => hx (by simpa [h] using hy), by simp⟩

/-- **Cohen–Macaulayness across a base field extension, for the concrete tensor product.** Let
`k` be a field, `S` a `k`-algebra with `K ⊗[k] S` Noetherian, `K/k` a field extension, `𝔮 ⊆ S` a
prime and `𝔮_K ⊆ K ⊗[k] S` a prime lying over it, and assume that one of the field extensions
`κ(𝔮)/k`, `K/k` is essentially of finite type. Then `S_𝔮` is Cohen–Macaulay if and only if
`(K ⊗[k] S)_{𝔮_K}` is.

This is Stacks 045N with its hypothesis "`K/k` is finitely generated" weakened to the
disjunction that Lemma 045M actually needs. -/
@[ega "IV 6.7.1" "Clause (i), special case",
  ega "IV 6.7.1.1" "more general",
  sga "3 VIA 1.1.1" "special case"]
private theorem isMaximalCohenMacaulay_localizationAtPrime_iff (k S K : Type*) [Field k]
    [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    (q : Ideal S) [q.IsPrime] (qK : Ideal (K ⊗[k] S)) [qK.IsPrime]
    (hqK : q = qK.comap Algebra.TensorProduct.includeRight.toRingHom)
    [IsNoetherianRing (Localization.AtPrime q)]
    [IsNoetherianRing (Localization.AtPrime qK)]
    (hfg : Algebra.EssFiniteType k q.ResidueField ∨ Algebra.EssFiniteType k K) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) ↔
      Module.IsMaximalCohenMacaulay (Localization.AtPrime qK) (Localization.AtPrime qK) := by
  have : Module.Flat S (K ⊗[k] S) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv
  have : qK.LiesOver q := ⟨hqK⟩
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)) := by
    rw [Localization.AtPrime.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  rw [Module.isMaximalCohenMacaulay_self_iff_of_flat (Localization.AtPrime q)
    (Localization.AtPrime qK)]
  refine (and_iff_left ?_).symm
  -- the prime of the fibre ring `κ(𝔮) ⊗[S] (K ⊗[k] S)` sitting above `𝔮_K`
  set Q : Ideal (q.Fiber (K ⊗[k] S)) :=
    ((PrimeSpectrum.primesOverOrderIsoFiber S (K ⊗[k] S) q)
      ⟨qK, inferInstance, inferInstance⟩).asIdeal with hQdef
  have hQ : Q.comap (Algebra.TensorProduct.includeRight :
      (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S)) = qK := by
    rw [hQdef, ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  have e2 := Stacks.Serre.DepthConditionAscent.localizationAtPrimeAlgEquivOfEq hQ
  have hIeq : (maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)) =
      q.map (algebraMap S (Localization.AtPrime qK)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmapE : ((q.map (algebraMap S (K ⊗[k] S))).map (algebraMap (K ⊗[k] S)
        (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeRight :
          (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S)))))).map
        (e2 : _ →+* Localization.AtPrime qK) =
      q.map (algebraMap S (Localization.AtPrime qK)) := by
    have hcomp : (e2 : _ →+* Localization.AtPrime qK).comp (algebraMap S (Localization.AtPrime
        (Q.comap (Algebra.TensorProduct.includeRight :
          (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S))))) =
        algebraMap S (Localization.AtPrime qK) :=
      RingHom.ext fun x => by
        rw [RingHom.comp_apply,
          IsScalarTower.algebraMap_apply S (K ⊗[k] S) (Localization.AtPrime qK),
          IsScalarTower.algebraMap_apply S (K ⊗[k] S) (Localization.AtPrime
            (Q.comap (Algebra.TensorProduct.includeRight :
              (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S))))]
        exact e2.commutes _
    rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S (K ⊗[k] S) (Localization.AtPrime
        (Q.comap (Algebra.TensorProduct.includeRight :
          (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S)))), hcomp]
  have E := (Ideal.Fiber.algEquivAux₂ q Q).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ e2.toRingEquiv (hIeq.trans hmapE.symm))
  have hnt : Nontrivial (Localization.AtPrime qK ⧸
      (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  have hlocF : IsLocalRing (Localization.AtPrime qK ⧸
      (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime qK)
      (Localization.AtPrime qK ⧸ (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)))) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hdepth := Module.depth_eq_depth_self_of_surjective_algebraMap
    (A := Localization.AtPrime qK)
    (B := Localization.AtPrime qK ⧸ (maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) hsurj
  have hdepthE := Module.depth_self_eq_of_ringEquiv
    (A := Localization.AtPrime Q)
    (B := Localization.AtPrime qK ⧸ (maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) E
  have hdimE := ringKrullDim_eq_of_ringEquiv
    (R := Localization.AtPrime Q)
    (S := Localization.AtPrime qK ⧸ (maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) E
  rw [hdepth, ← hdepthE, ← hdimE]
  -- the fibre ring is `κ(𝔮) ⊗[k] K`, Cohen–Macaulay by Stacks 045M
  exact Stacks.CohenMacaulay.FiniteTypeBaseChange.isMaximalCohenMacaulay_localization_of_ringEquiv
    (((Algebra.TensorProduct.congr (AlgEquiv.refl : q.ResidueField ≃ₐ[S] q.ResidueField)
        (Algebra.TensorProduct.commRight k S K).symm).toRingEquiv).trans
      (Algebra.TensorProduct.cancelBaseChange k S q.ResidueField q.ResidueField K).toRingEquiv)
    (Algebra.TensorProduct.isNoetherianRing_and_isCohenMacaulay_of_essFiniteType k
      q.ResidueField K hfg).2 Q

/-- A ring isomorphism of local rings transfers Noetherianity and Cohen–Macaulayness. -/
private lemma isNoetherianRing_and_isMaximalCohenMacaulay_of_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    (e : A ≃+* B) :
    IsNoetherianRing B ∧ (Module.IsMaximalCohenMacaulay A A ↔ Module.IsMaximalCohenMacaulay B B) :=
  ⟨isNoetherianRing_of_ringEquiv A e, Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e⟩

/-- The same comparison for an abstract pushout square of algebras and abstract models of the
two local rings. -/
private theorem isMaximalCohenMacaulay_pushoutAtPrime_iff
    (k K S T : Type*) [Field k] [Field K] [CommRing S] [CommRing T]
    [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime]
    [r.LiesOver q]
    (hfg : Algebra.EssFiniteType k q.ResidueField ∨ Algebra.EssFiniteType k K)
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [IsLocalRing Sq]
    [IsNoetherianRing Sq]
    (Tr : Type*) [CommRing Tr] [Algebra T Tr] [IsLocalization.AtPrime Tr r] [IsLocalRing Tr]
    [IsNoetherianRing Tr] :
    Module.IsMaximalCohenMacaulay Sq Sq ↔ Module.IsMaximalCohenMacaulay Tr Tr := by
  obtain ⟨_, hS⟩ := isNoetherianRing_and_isMaximalCohenMacaulay_of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl Sq (Localization.AtPrime q)).toRingEquiv
  obtain ⟨_, hT⟩ := isNoetherianRing_and_isMaximalCohenMacaulay_of_ringEquiv
    (IsLocalization.algEquiv r.primeCompl Tr (Localization.AtPrime r)).toRingEquiv
  rw [hS, hT]
  let e : K ⊗[k] S ≃+* T := (Algebra.IsPushout.equiv k K S T).toRingEquiv
  have he : (e : K ⊗[k] S →+* T).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom = algebraMap S T := by
    refine RingHom.ext fun s => ?_
    change (Algebra.IsPushout.equiv k K S T) (1 ⊗ₜ[k] s) = algebraMap S T s
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  let rK : Ideal (K ⊗[k] S) := r.comap (e : K ⊗[k] S →+* T)
  have : rK.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨_, hrK'⟩ := isNoetherianRing_and_isMaximalCohenMacaulay_of_ringEquiv
    (localizationAtPrimeCongr e rK r rfl).symm
  rw [hrK']
  have hrK : q = rK.comap Algebra.TensorProduct.includeRight.toRingHom := by
    rw [show rK = r.comap (e : K ⊗[k] S →+* T) from rfl, Ideal.comap_comap, he]
    exact Ideal.LiesOver.over
  exact isMaximalCohenMacaulay_localizationAtPrime_iff k S K q rK hrK hfg

/-- The local ring at a point of a scheme locally of finite type over a field is essentially of
finite type over that field. -/
private lemma essFiniteType_stalk_over_field_of_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let R := (Spec (.of k)).presheaf.stalk (f.base x)
  let A := X.presheaf.stalk x
  let _ : Algebra k A := (fieldToStalk f x).hom.toAlgebra
  let _ : Algebra k R := StructureSheaf.stalkAlgebra k (f.base x)
  let _ : Algebra R A := (f.stalkMap x).hom.toAlgebra
  have hcat : CommRingCat.ofHom (algebraMap k R) ≫ f.stalkMap x = fieldToStalk f x := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (f.base x) (by simp)) ≫ f.stalkMap x =
        (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial
    rw [Category.assoc,
      Scheme.Hom.germ_stalkMap (f := f) (U := ⊤) (x := x) (hx := by simp)]
    simp
  have hmap : algebraMap k A = (algebraMap R A).comp (algebraMap k R) := by
    simpa [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom hcat.symm
  let _ : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' (by simpa [R, A] using hmap)
  have hclosed : f.base x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hsurj : Function.Surjective (algebraMap k R) := by
    let eR : R ≅ .of k :=
      (Spec (.of k)).presheaf.stalkCongr (Inseparable.of_eq hclosed) ≪≫
        stalkClosedPointIso (.of k)
    have heq : (algebraMap k R) = eR.inv.hom := by
      ext s
      change (StructureSheaf.toStalk k (f.base x)).hom s = _
      dsimp only [eR, Iso.trans_inv]
      rw [stalkClosedPointIso_inv]
      change (StructureSheaf.toStalk k (f.base x)).hom s =
        (StructureSheaf.toStalk k (IsLocalRing.closedPoint k) ≫
          (Spec (.of k)).presheaf.stalkSpecializes
            (Inseparable.of_eq hclosed).le).hom s
      exact congrArg
        (fun h : .of k ⟶ (Spec (.of k)).presheaf.stalk (f.base x) => h.hom s)
        (StructureSheaf.toStalk_stalkSpecializes
          (R := k) (Inseparable.of_eq hclosed).le).symm
    exact heq ▸ (ConcreteCategory.bijective_of_isIso eR.inv).surjective
  have hR : Algebra.EssFiniteType k R :=
    RingHom.essFiniteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  have hRA : Algebra.EssFiniteType R A := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  exact Algebra.EssFiniteType.comp k R A

/-- Cohen–Macaulayness of the local ring of a scheme over a field is unchanged by extending the
ground field, provided one of the two residue extensions is essentially of finite type. -/
@[ega "IV 6.3.5" "special case", ega "IV 6.7.2" "more general", sga "3 VIA 1.1.1" "more general"]
public theorem isCohenMacaulayLocalRing_stalk_baseChange_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx' : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x)
    [IsNoetherianRing (X.presheaf.stalk x)]
    [IsNoetherianRing
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x')]
    (hfg : letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
      Algebra.EssFiniteType k (X.presheaf.stalk x) ∨ Algebra.EssFiniteType k K) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x') := by
  let pX := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let A : Type u := X.presheaf.stalk x
  let B : Type u := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x'
  let α := fieldToStalk f x
  let β : CommRingCat.of k ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (algebraMap k K)
  let _ : Algebra k A := α.hom.toAlgebra
  let T : CommRingCat := stalkBaseChangeRing (K := K) f x
  let _ : Algebra k T := (α ≫ pushout.inl α β).hom.toAlgebra
  let _ : Algebra A T := (pushout.inl α β).hom.toAlgebra
  let _ : Algebra K T := (pushout.inr α β).hom.toAlgebra
  let _ : IsScalarTower k A T := .of_algebraMap_eq' rfl
  let _ : IsScalarTower k K T := .of_algebraMap_eq' (by
    change (α ≫ pushout.inl α β).hom = (β ≫ pushout.inr α β).hom
    exact congrArg CommRingCat.Hom.hom (pushout.condition))
  have hPO : IsPushout α β (pushout.inl α β) (pushout.inr α β) :=
    ⟨⟨pushout.condition⟩, ⟨pushoutIsPushout α β⟩⟩
  have hPO' : Algebra.IsPushout k A K T :=
    (CommRingCat.isPushout_iff_isPushout).mp hPO
  let _ : Algebra.IsPushout k K A T := (Algebra.IsPushout.comm k A K T).mp hPO'
  obtain ⟨θ, ψ, φ, hθA, hθK, hψA, hψK, hφA, hφK, hθψ, hloc⟩ :=
    stalkOfBaseChange_isLocalization f x x' hx'
  let ρ := (X.presheaf.stalkCongr (.of_eq hx'.symm)).hom ≫ pX.stalkMap x'
  let _ : Algebra T B := φ.hom.toAlgebra
  let _ : Algebra A B := ρ.hom.toAlgebra
  let _ : IsScalarTower A T B := .of_algebraMap_eq' (by
    change ρ.hom = (algebraMap T B).comp (algebraMap A T)
    exact congrArg CommRingCat.Hom.hom hφA.symm)
  let p₀ : Ideal (residueBaseChangeRing f x) := RingHom.ker ψ.hom
  let p : Ideal T := Ideal.comap θ.hom p₀
  have hp₀ : p₀.IsPrime := RingHom.ker_isPrime _
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hloc' : IsLocalization.AtPrime B p := by
    simpa [p, p₀, stalkBaseChangePrime] using hloc
  have hcontract : p.comap (algebraMap A T) = IsLocalRing.maximalIdeal A := by
    have hpB : p = (IsLocalRing.maximalIdeal B).comap (algebraMap T B) :=
      (IsLocalization.AtPrime.under_maximalIdeal B p).symm
    rw [hpB, Ideal.comap_comap,
      show (algebraMap T B).comp (algebraMap A T) = ρ.hom from congrArg CommRingCat.Hom.hom hφA]
    exact IsLocalRing.maximalIdeal_comap _
  let q : Ideal A := IsLocalRing.maximalIdeal A
  let _ : q.LiesOver q := ⟨rfl⟩
  let _ : p.LiesOver q := ⟨hcontract.symm⟩
  let _ : IsLocalization.AtPrime A q :=
    localization_isLocalizationAtPrime_of_localTarget
      (A := A) (C := A) (M := IsUnit.submonoid A)
  have hfg' : Algebra.EssFiniteType k q.ResidueField ∨ Algebra.EssFiniteType k K := by
    cases hfg with
    | inl hA =>
      let _ : Algebra.EssFiniteType k A := hA
      exact .inl (Algebra.EssFiniteType.comp k A q.ResidueField)
    | inr hK => exact .inr hK
  simpa [A, B] using
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).trans
    ((isMaximalCohenMacaulay_pushoutAtPrime_iff k K A T q p hfg' A B).trans
      (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).symm)

/-- **Stacks Project, Tag 045P.** Cohen-Macaulayness of local rings is unchanged after a
finitely generated extension of the ground field of a locally Noetherian scheme.

The extension may be transcendental: `K = k(x₁, …, xₙ)` is finitely generated as a field
extension, which is `Algebra.EssFiniteType k K` by `IntermediateField.fg_top_iff`, and not
finitely generated as a `k`-algebra. The base change is again locally Noetherian, by Tag 038R;
that is what makes the local ring on the right a Noetherian local ring. -/
@[stacks 045P "finitely generated field extension",
  ega "IV 6.7.8" "(ii)",
  ega "IV 6.7.1" "F = O_X, CM clause",
  ega "IV 6.7.2" "special case",
  sga "3 VIA 1.1.1" "more general"]
public theorem isCohenMacaulayLocalRing_stalk_iff_of_finiteType_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx' : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x) :
    letI : IsLocallyNoetherian
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme) :=
      (isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x') := by
  let _ : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  let _ : IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme) :=
    (isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
  exact isCohenMacaulayLocalRing_stalk_baseChange_iff k K X f x x' hx' (.inr inferInstance)

attribute [-instance] IsRegularRing.toIsNoetherian IsRegularLocalRing.toIsNoetherian in
/-- **Stacks Project, Tag 045P.** Cohen-Macaulayness of local rings is unchanged after an
arbitrary extension of the ground field when the scheme is locally of finite type over that
field. -/
@[stacks 045P "arbitrary field extension for a locally finite type scheme",
  ega "IV 6.7.8" "(ii)",
  ega "IV 6.7.1" "F = O_X, CM clause"]
public theorem isCohenMacaulayLocalRing_stalk_iff_of_locallyOfFiniteType
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx' : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x') := by
  have : IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  exact isCohenMacaulayLocalRing_stalk_baseChange_iff k K X f x x' hx'
    (.inl (essFiniteType_stalk_over_field_of_locallyOfFiniteType k X f x))

end AlgebraicGeometry

end
