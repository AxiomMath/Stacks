module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.Saturation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.HenselianFlattening
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The local flattening situation at a point of a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes, `F` a module on `X`, and let `x` be a point of `X`
above a point `s` of `S`. The local homomorphism `𝒪_{S, s} → 𝒪_{X, x}` together with the stalk
`F_x` is the standing data of Stacks Tag 05MK. This file attaches that data to the geometry and
identifies the flatness condition of Stacks Tag 05ML, tested on the local ring of a pointed
scheme `(T, t)` over `(S, s)`, with flatness of the pullback of `F` to `X ×_S T` over `T` at
every point lying above both `x` and `t`.

The identification runs through the local rings of the fibre product. At a point `y` of
`X ×_S T` the local ring is a localization of `𝒪_{X, x} ⊗_{𝒪_{S, s}} 𝒪_{T, t}`
(`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`), at the prime which is the
contraction of the maximal ideal; that prime contains the extensions of the maximal ideals of
`𝒪_{X, x}` and of `𝒪_{T, t}`, and the stalk of the pullback of `F` at `y` is the base change of
`F_x` along `𝒪_{X, x} → 𝒪_{X ×_S T, y}` (Stacks Tag 0098). Conversely every prime of the tensor
product containing those two extensions is the image of a point of the fibre product above `x`
and above `t`: the comparison morphism `AlgebraicGeometry.stalkTensorToPullback` carries it to
such a point, and being a preimmersion it is injective, so the two descriptions match prime by
prime.

## Main definitions

* `AlgebraicGeometry.stalkFlatAtPointSituation` is the situation of Stacks Tag 05MK attached to
  `f`, `F`, `x` and `s`.
* `AlgebraicGeometry.pointedStalkLocalAlgebra` is the local ring of `T` at `t`, read as a local
  `𝒪_{S, s}`-algebra with local structure homomorphism.
* `AlgebraicGeometry.stalkTensorToPullback` is the comparison morphism
  `Spec (𝒪_{X, x} ⊗_{𝒪_{S, s}} 𝒪_{T, t}) ⟶ X ×_S T`.

## Main results

* `AlgebraicGeometry.condition_iff_forall_isFlatOverAt`: the condition of Stacks Tag 05ML for
  `AlgebraicGeometry.stalkFlatAtPointSituation` tested on `𝒪_{T, t}` holds exactly when the
  pullback of `F` is flat over `T` at every point of `X ×_S T` above `x` and `t`.
* `AlgebraicGeometry.exists_tensorPrime_over_pullback_point` is the prime-by-prime form of that
  equivalence at one point of the fibre product.
* `AlgebraicGeometry.isPreimmersion_stalkTensorToPullback` and the two projection formulas
  `AlgebraicGeometry.stalkTensorToPullback_fst`,
  `AlgebraicGeometry.stalkTensorToPullback_snd` describe the comparison morphism.

## Implementation notes

The algebra structure `𝒪_{S, s} → 𝒪_{X, x}` is the stalk map of `f` precomposed with the
transport `eqToHom` along `f x = s`, so that the two points may be named independently; the
same convention is used for `𝒪_{S, s} → 𝒪_{T, t}`. The module structure on a stalk is Mathlib's
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`, which is
also the one `AlgebraicGeometry.IsFlatOverAt` uses, so no transport is needed between the
geometric and the ring-theoretic sides.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The local flattening situation of Stacks Tag 05MK attached to a pointed morphism of
schemes and a module on the source: the base is the local ring of the target at `s`, the
algebra is the local ring of the source at `x`, and the module is the stalk of `F` at `x`. -/
def stalkFlatAtPointSituation {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (s : S) (hxs : f x = s) : Module.FlatAtPointSituation.{u, u, u} :=
  letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  letI : IsLocalHom (algebraMap (S.presheaf.stalk s) (X.presheaf.stalk x)) := by
    change IsLocalHom (eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom
    exact CommRingCat.isLocalHom_comp _ (f.stalkMap x)
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  { A := S.presheaf.stalk s
    B := X.presheaf.stalk x
    M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x }

/-- The base of `stalkFlatAtPointSituation` is the local ring of the target at `s`. -/
@[simp]
lemma stalkFlatAtPointSituation_A {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (s : S) (hxs : f x = s) :
    (stalkFlatAtPointSituation f F x s hxs).A = S.presheaf.stalk s := rfl

/-- The algebra of `stalkFlatAtPointSituation` is the local ring of the source at `x`. -/
@[simp]
lemma stalkFlatAtPointSituation_B {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (s : S) (hxs : f x = s) :
    (stalkFlatAtPointSituation f F x s hxs).B = X.presheaf.stalk x := rfl

/-- The module of `stalkFlatAtPointSituation` is the stalk of `F` at `x`. -/
@[simp]
lemma stalkFlatAtPointSituation_M {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (s : S) (hxs : f x = s) :
    (stalkFlatAtPointSituation f F x s hxs).M =
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x := rfl

/-- The local ring of a pointed scheme over `(S, s)`, as an object of the category of local
`𝒪_{S,s}`-algebras with local structure homomorphism. -/
def pointedStalkLocalAlgebra {S T : Scheme.{u}} (g : T ⟶ S) (s : S) (t : T) (ht : g t = s) :
    LocalAlgCat.{u, u} (S.presheaf.stalk s) :=
  letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  letI : IsLocalHom (algebraMap (S.presheaf.stalk s) (T.presheaf.stalk t)) := by
    change IsLocalHom (eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom
    exact CommRingCat.isLocalHom_comp _ (g.stalkMap t)
  { carrier := T.presheaf.stalk t }

/-- The carrier of `pointedStalkLocalAlgebra` is the local ring of `T` at `t`. -/
@[simp]
lemma pointedStalkLocalAlgebra_carrier {S T : Scheme.{u}} (g : T ⟶ S) (s : S) (t : T)
    (ht : g t = s) :
    (pointedStalkLocalAlgebra g s t ht).carrier = T.presheaf.stalk t := rfl

/-- The comparison morphism from the spectrum of the tensor product of the two local rings
over the local ring of the base into the fibre product of the two schemes. -/
def stalkTensorToPullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s) :
    let A := S.presheaf.stalk s
    let B := X.presheaf.stalk x
    let R := T.presheaf.stalk t
    letI : Algebra A B :=
      ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
    letI : Algebra A R :=
      ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
    Spec (.of (TensorProduct A B R)) ⟶ pullback f g := by
  let A := S.presheaf.stalk s
  let B := X.presheaf.stalk x
  let R := T.presheaf.stalk t
  letI : Algebra A B :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  letI : Algebra A R :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  exact (pullbackSpecIso A B R).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A R))) f g
      (X.fromSpecStalk x) (T.fromSpecStalk t) (S.fromSpecStalk s)
      (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk f x hxs.symm)
      (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk g t ht.symm)

/-- The comparison morphism followed by the first projection is the first inclusion into the
tensor product followed by the canonical morphism out of the spectrum of the local ring. -/
lemma stalkTensorToPullback_fst {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s) :
    let A := S.presheaf.stalk s
    let B := X.presheaf.stalk x
    let R := T.presheaf.stalk t
    letI : Algebra A B :=
      ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
    letI : Algebra A R :=
      ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
    stalkTensorToPullback f g x t s hxs ht ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* TensorProduct A B R)) ≫
        X.fromSpecStalk x := by
  dsimp only [stalkTensorToPullback]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

/-- The comparison morphism followed by the second projection is the second inclusion into
the tensor product followed by the canonical morphism out of the spectrum of the local
ring. -/
lemma stalkTensorToPullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s) :
    let A := S.presheaf.stalk s
    let B := X.presheaf.stalk x
    let R := T.presheaf.stalk t
    letI : Algebra A B :=
      ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
    letI : Algebra A R :=
      ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
    stalkTensorToPullback f g x t s hxs ht ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : R →+* TensorProduct A B R)) ≫
        T.fromSpecStalk t := by
  dsimp only [stalkTensorToPullback]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

/-- The comparison morphism from the spectrum of the tensor product of the local rings is a
preimmersion. -/
lemma isPreimmersion_stalkTensorToPullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s) :
    IsPreimmersion (stalkTensorToPullback f g x t s hxs ht) := by
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  let : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : Flat (T.fromSpecStalk t) := flat_fromSpecStalk T t
  have hpre := (BaseChangeStalk.flat_isPreimmersion_pullbackMap_of_comp_mono
    (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (X.presheaf.stalk x))))
    (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (T.presheaf.stalk t))))
    (S.fromSpecStalk s) (X.fromSpecStalk x) (T.fromSpecStalk t) f g
    (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk f x hxs.symm)
    (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk g t ht.symm)).2
  have : IsPreimmersion (pullback.map
      (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (X.presheaf.stalk x))))
      (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (T.presheaf.stalk t))))
      f g (X.fromSpecStalk x) (T.fromSpecStalk t) (S.fromSpecStalk s)
      (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk f x hxs.symm)
      (BaseChangeStalk.specMap_eqToHom_stalkMap_fromSpecStalk g t ht.symm)) := hpre
  exact inferInstanceAs (IsPreimmersion ((pullbackSpecIso _ _ _).inv ≫ _))

/-- If a morphism out of `Spec Q` restricts along a map from the stalk at `y` to the canonical
morphism, then a prime containing the extension of the maximal ideal is sent over `y`. -/
private lemma apply_eq_of_comp_eq_specMap_fromSpecStalk {Z Y : Scheme.{u}} (p : Z ⟶ Y) (y : Y)
    {Q : Type u} [CommRing Q] (ι : Y.presheaf.stalk y →+* Q) (q : Ideal Q) (hq : q.IsPrime)
    (hle : Ideal.map ι (IsLocalRing.maximalIdeal _) ≤ q) (Φ : Spec (.of Q) ⟶ Z)
    (h : Φ ≫ p = Spec.map (CommRingCat.ofHom ι) ≫ Y.fromSpecStalk y) : p (Φ ⟨q, hq⟩) = y := by
  let pt : ↥(Spec (.of Q)) := ⟨q, hq⟩
  have hpoint : Spec.map (CommRingCat.ofHom ι) pt = IsLocalRing.closedPoint _ :=
    PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (hq.comap ι).ne_top
      (Ideal.map_le_iff_le_comap.mp hle)).symm
  change p (Φ pt) = y
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, hpoint,
    Scheme.fromSpecStalk_closedPoint]

/-- A prime of `Q` at which a local map `Q → C` pulls back the maximal ideal contains the
extension of the maximal ideal along any `ι : B → Q` factoring a local map `B → C`. -/
private lemma map_maximalIdeal_le_comap_maximalIdeal {B Q C : Type u} [CommRing B] [CommRing Q]
    [CommRing C] [IsLocalRing B] [IsLocalRing C] (ι : B →+* Q) (φ : Q →+* C) (ψ : B →+* C)
    [IsLocalHom ψ] (h : φ.comp ι = ψ) :
    Ideal.map ι (IsLocalRing.maximalIdeal B) ≤ Ideal.comap φ (IsLocalRing.maximalIdeal C) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, h]
  exact (IsLocalRing.maximalIdeal_comap ψ).ge

/-- The two ways of mapping `Spec C` into the base through the stalk of `p` at `z` agree. -/
private lemma specMap_comp_specMap_comp_fromSpecStalk {P Y : Scheme.{u}} (p : P ⟶ Y) (z : P)
    {Q : Type u} [CommRing Q] (ι : Y.presheaf.stalk (p z) →+* Q) (φ : Q →+* P.presheaf.stalk z)
    (h : φ.comp ι = (p.stalkMap z).hom) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ι) ≫
      Y.fromSpecStalk (p z) = P.fromSpecStalk z ≫ p := by
  rw [← Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom ι ≫ CommRingCat.ofHom φ = p.stalkMap z from CommRingCat.hom_ext h]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk p

/-- A prime of the tensor product of the two local rings which contains the extensions of
both maximal ideals is carried by the comparison morphism to a point of the fibre product
lying over `x` and over `t`. -/
lemma stalkTensorToPullback_projections_of_maximal_comap
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s) :
    let A := S.presheaf.stalk s
    let B := X.presheaf.stalk x
    let R := T.presheaf.stalk t
    letI : Algebra A B :=
      ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
    letI : Algebra A R :=
      ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
    ∀ (q : Ideal (TensorProduct A B R)) (hq : q.IsPrime),
      Ideal.map Algebra.TensorProduct.includeLeftRingHom
          (IsLocalRing.maximalIdeal B) ≤ q →
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (IsLocalRing.maximalIdeal R) ≤ q →
      pullback.fst f g (stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩) = x ∧
        pullback.snd f g (stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩) = t := by
  intro A B R q hq hqB hqR
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  let : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  exact ⟨apply_eq_of_comp_eq_specMap_fromSpecStalk _ x _ q hq hqB _
    (stalkTensorToPullback_fst f g x t s hxs ht),
    apply_eq_of_comp_eq_specMap_fromSpecStalk _ t _ q hq hqR _
    (stalkTensorToPullback_snd f g x t s hxs ht)⟩

/-- A localization of a commutative ring which happens to be local is the localization at the
prime contracted from its maximal ideal. -/
lemma isLocalization_primeCompl_of_comap_maximalIdeal
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [IsLocalRing C] (M : Submonoid R) [IsLocalization M C]
    (q : Ideal R) [q.IsPrime]
    (hq : q = Ideal.comap (algebraMap R C) (IsLocalRing.maximalIdeal C)) :
    IsLocalization q.primeCompl C := by
  have hsat : M.saturation = q.primeCompl.saturation := by
    ext a
    have hM : a ∈ M.saturation.toSubmonoid ↔ IsUnit (algebraMap R C a) := by
      change a ∈ M.saturation ↔ _
      exact IsLocalization.mem_saturation_iff_isUnit_algebraMap M C
    have hQ : a ∈ q.primeCompl.saturation.toSubmonoid ↔ a ∉ q := by
      change a ∈ q.primeCompl.saturation ↔ _
      rw [Submonoid.mem_saturation_iff]
      refine ⟨fun ⟨b, hb⟩ ha ↦ hb (q.mul_mem_right b ha), fun ha ↦ ⟨1, by simpa using ha⟩⟩
    rw [hM, hQ, hq]
    simpa only [Ideal.mem_comap] using
      (IsLocalRing.notMem_maximalIdeal (R := C) (x := algebraMap R C a)).symm
  exact IsLocalization.of_saturation_eq M q.primeCompl hsat

/-- Localizing the base change `Q ⊗[B] M` at a prime `q` of `Q` gives the base change of `M`
to the localization of `Q` at `q`, so the two have the same flatness over a ring acting
through `Q`. -/
lemma flat_localizedModule_tensor_iff
    {B Q R C M : Type u} [CommRing B] [CommRing Q] [CommRing R] [CommRing C]
    [Algebra B Q] [Algebra R Q] [Algebra Q C] [Algebra B C] [Algebra R C]
    [IsScalarTower B Q C] [IsScalarTower R Q C]
    [AddCommGroup M] [Module B M]
    (q : Ideal Q) [q.IsPrime] [IsLocalization q.primeCompl C] :
    Module.Flat R (LocalizedModule q.primeCompl (TensorProduct B Q M)) ↔
      Module.Flat R (TensorProduct B C M) := by
  let e₁ := IsLocalizedModule.linearEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl (TensorProduct B Q M))
    (TensorProduct.mk Q C (TensorProduct B Q M) 1)
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q C C M
  exact Module.Flat.equiv_iff ((e₁.trans (e₂.restrictScalars Q)).restrictScalars R)

/-- **At a point of the fibre product lying over the two chosen points, flatness of the
pulled-back module is flatness of a localized base change of the stalk.** The local ring of
the fibre product at such a point is a localization of the tensor product of the two local
rings at a prime containing the extensions of both maximal ideals, that prime is carried to
the point by the comparison morphism, and the two flatness conditions correspond. -/
lemma exists_tensorPrime_over_pullback_point
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (F : X.Modules)
    (x : X) (s : S) (t : T) (hxs : f x = s) (ht : g t = s)
    (y : ↥(pullback f g))
    (hyT : pullback.snd f g y = t) (hyX : pullback.fst f g y = x) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
      ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
      ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    letI : Algebra (T.presheaf.stalk t)
        (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x) (T.presheaf.stalk t)) :=
      Algebra.TensorProduct.rightAlgebra
    ∃ (q : Ideal (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x)
        (T.presheaf.stalk t))) (hq : q.IsPrime),
      letI := hq
      Ideal.map Algebra.TensorProduct.includeLeftRingHom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≤ q ∧
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) ≤ q ∧
      stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩ = y ∧
      (IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y ↔
        Module.Flat (T.presheaf.stalk t)
          (LocalizedModule q.primeCompl
            (TensorProduct (X.presheaf.stalk x)
              (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x)
                (T.presheaf.stalk t))
              (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)))) := by
  subst x
  subst t
  subst s
  let : Algebra (S.presheaf.stalk (f (pullback.fst f g y)))
      (X.presheaf.stalk (pullback.fst f g y)) :=
    ((eqToHom rfl ≫ f.stalkMap (pullback.fst f g y)).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (pullback.fst f g y)))
      (T.presheaf.stalk (pullback.snd f g y)) :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫
      g.stalkMap (pullback.snd f g y)).hom).toAlgebra
  let : Module (X.presheaf.stalk (pullback.fst f g y))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf
        (pullback.fst f g y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      F.val _
  let : Algebra (T.presheaf.stalk (pullback.snd f g y))
      (TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
        (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y))) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨φ₀, hleft₀, hright₀, N₀, hN₀⟩ :=
    BaseChangeStalk.pullback_stalk_isLocalization f g y
  let φ : TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
      (X.presheaf.stalk (pullback.fst f g y))
      (T.presheaf.stalk (pullback.snd f g y)) →+*
      (pullback f g).presheaf.stalk y := φ₀
  let : Algebra (TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
      (X.presheaf.stalk (pullback.fst f g y))
      (T.presheaf.stalk (pullback.snd f g y)))
      ((pullback f g).presheaf.stalk y) := φ.toAlgebra
  have hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom =
      ((pullback.fst f g).stalkMap y).hom := hleft₀
  have hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap y).hom := hright₀
  let N : Submonoid (TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
      (X.presheaf.stalk (pullback.fst f g y))
      (T.presheaf.stalk (pullback.snd f g y))) := N₀
  have hN : IsLocalization N ((pullback f g).presheaf.stalk y) := hN₀
  have : IsLocalHom ((pullback.fst f g).stalkMap y).hom :=
    (pullback.fst f g).toLRSHom.prop y
  have : IsLocalHom ((pullback.snd f g).stalkMap y).hom :=
    (pullback.snd f g).toLRSHom.prop y
  have hqprime : (Ideal.comap φ
      (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk y))).IsPrime :=
    Ideal.comap_isPrime φ _
  have hqB := map_maximalIdeal_le_comap_maximalIdeal
    (Algebra.TensorProduct.includeLeftRingHom :
      X.presheaf.stalk (pullback.fst f g y) →+* _) φ _ hleft
  have hqR := map_maximalIdeal_le_comap_maximalIdeal
    (Algebra.TensorProduct.includeRight.toRingHom :
      T.presheaf.stalk (pullback.snd f g y) →+* _) φ _ hright
  have : IsLocalization (Ideal.comap φ
      (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk y))).primeCompl
      ((pullback f g).presheaf.stalk y) :=
    isLocalization_primeCompl_of_comap_maximalIdeal N _ rfl
  have hfac : Spec.map (CommRingCat.ofHom φ) ≫
      stalkTensorToPullback f g (pullback.fst f g y) (pullback.snd f g y)
        (f (pullback.fst f g y)) rfl ht =
      (pullback f g).fromSpecStalk y := by
    apply pullback.hom_ext
    · rw [Category.assoc, stalkTensorToPullback_fst]
      have key := specMap_comp_specMap_comp_fromSpecStalk (pullback.fst f g) y
        Algebra.TensorProduct.includeLeftRingHom φ hleft
      exact key
    · rw [Category.assoc, stalkTensorToPullback_snd]
      have key := specMap_comp_specMap_comp_fromSpecStalk (pullback.snd f g) y
        Algebra.TensorProduct.includeRight.toRingHom φ hright
      exact key
  have hpoint : stalkTensorToPullback f g (pullback.fst f g y) (pullback.snd f g y)
      (f (pullback.fst f g y)) rfl ht ⟨_, hqprime⟩ = y := by
    change (Spec.map (CommRingCat.ofHom φ) ≫
      stalkTensorToPullback f g (pullback.fst f g y) (pullback.snd f g y)
        (f (pullback.fst f g y)) rfl ht)
      (IsLocalRing.closedPoint ((pullback f g).presheaf.stalk y)) = y
    rw [hfac]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨_, hqprime, hqB, hqR, hpoint, ?_⟩
  let : Module ((pullback f g).presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val y
  let : Algebra (X.presheaf.stalk (pullback.fst f g y))
      ((pullback f g).presheaf.stalk y) :=
    ((pullback.fst f g).stalkMap y).hom.toAlgebra
  let : Algebra (T.presheaf.stalk (pullback.snd f g y))
      ((pullback f g).presheaf.stalk y) :=
    ((pullback.snd f g).stalkMap y).hom.toAlgebra
  have : IsScalarTower (X.presheaf.stalk (pullback.fst f g y))
      (TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
        (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y)))
      ((pullback f g).presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' hleft.symm
  have : IsScalarTower (T.presheaf.stalk (pullback.snd f g y))
      (TensorProduct (S.presheaf.stalk (f (pullback.fst f g y)))
        (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y)))
      ((pullback f g).presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' hright.symm
  let : Module (T.presheaf.stalk (pullback.snd f g y))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val.presheaf y) :=
    Module.compHom _ ((pullback.snd f g).stalkMap y).hom
  have : IsScalarTower (T.presheaf.stalk (pullback.snd f g y))
      ((pullback f g).presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val.presheaf y) :=
    IsScalarTower.of_compHom _ _ _
  obtain ⟨e₀, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    (pullback.fst f g).toLRSHom.toShHom F y
  let e : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val.presheaf y ≃ₗ[
        (pullback f g).presheaf.stalk y]
      TensorProduct (X.presheaf.stalk (pullback.fst f g y))
        ((pullback f g).presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf
          (pullback.fst f g y)) := e₀
  exact (Module.Flat.equiv_iff (e.restrictScalars
      (T.presheaf.stalk (pullback.snd f g y)))).trans
    (flat_localizedModule_tensor_iff
      (B := X.presheaf.stalk (pullback.fst f g y))
      (R := T.presheaf.stalk (pullback.snd f g y))
      (C := (pullback f g).presheaf.stalk y)
      (M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf
        (pullback.fst f g y)) _).symm


/-- **The local flattening condition of Stacks Tag 05ML at a pointed base change is flatness
of the pulled-back module along the distinguished fibre.** For a pointed morphism
`(T, t) ⟶ (S, s)`, the condition of Stacks Tag 05ML for the local flattening situation at
`(x, s)` tested on the local ring of `T` at `t` holds exactly when the pullback of `F` to
`X ×_S T` is flat over `T` at every point above both `x` and `t`. -/
lemma condition_iff_forall_isFlatOverAt
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (F : X.Modules)
    (x : X) (s : S) (t : T) (hxs : f x = s) (ht : g t = s) :
    (stalkFlatAtPointSituation f F x s hxs).Condition
        (pointedStalkLocalAlgebra g s t ht) ↔
      ∀ y : ↥(pullback f g), pullback.snd f g y = t → pullback.fst f g y = x →
        IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y := by
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  let : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  let : Algebra (T.presheaf.stalk t)
      (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x) (T.presheaf.stalk t)) :=
    Algebra.TensorProduct.rightAlgebra
  have hcond : (stalkFlatAtPointSituation f F x s hxs).Condition
        (pointedStalkLocalAlgebra g s t ht) ↔
      ∀ (q : Ideal (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x)
          (T.presheaf.stalk t))) (hq : q.IsPrime),
        letI := hq
        Ideal.map Algebra.TensorProduct.includeRight.toRingHom
            (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) +
          Ideal.map Algebra.TensorProduct.includeLeftRingHom
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≤ q →
          Module.Flat (T.presheaf.stalk t)
            (LocalizedModule q.primeCompl
              (TensorProduct (X.presheaf.stalk x)
                (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x)
                  (T.presheaf.stalk t))
                (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))) :=
    Iff.rfl
  rw [hcond]
  constructor
  · intro hc y hyT hyX
    obtain ⟨q, hq, hqB, hqR, -, he⟩ :=
      exists_tensorPrime_over_pullback_point f g F x s t hxs ht y hyT hyX
    exact he.mpr (hc q hq (sup_le hqR hqB))
  · intro hflat q hq hqBR
    let := hq
    have hpre : IsPreimmersion (stalkTensorToPullback f g x t s hxs ht) :=
      isPreimmersion_stalkTensorToPullback f g x t s hxs ht
    obtain ⟨hyX, hyT⟩ := stalkTensorToPullback_projections_of_maximal_comap f g x t s hxs ht
      q hq (le_sup_right.trans hqBR) (le_sup_left.trans hqBR)
    obtain ⟨q', hq', -, -, hp, he⟩ := exists_tensorPrime_over_pullback_point f g F x s t
      hxs ht (stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩) hyT hyX
    obtain rfl : q' = q := congrArg PrimeSpectrum.asIdeal
      ((IsPreimmersion.isEmbedding (stalkTensorToPullback f g x t s hxs ht)).injective hp)
    exact he.mp (hflat _ hyT hyX)

end AlgebraicGeometry

end
