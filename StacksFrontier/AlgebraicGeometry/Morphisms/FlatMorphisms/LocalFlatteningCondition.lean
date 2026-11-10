module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StalkFlatteningSituation
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.FlatteningBridge
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType

/-!
# The flatness condition of Stacks 05ML at a point of a scheme

Let `f : X ⟶ S` be locally of finite type, `F` an `𝒪_X`-module, `x ∈ X` a point over `s ∈ S`, and
`(T, t) ⟶ (S, s)` a pointed scheme. The local flattening problem of Stacks 05MK attached to `x`
is the stalk `F_x` over `𝒪_{X,x}` over `𝒪_{S,s}`, and Stacks 05ML asks flatness of the base change
to `𝒪_{T,t}` at the primes of `𝒪_{X,x} ⊗ 𝒪_{T,t}` over both maximal ideals. This file proves that
this algebraic condition is the geometric one: `F_T` is flat over `T` at every point of `X_T`
lying over `t` and `x`. This is the translation underlying the scheme-theoretic reformulation of
Stacks 05PG.

## Main definitions

* `AlgebraicGeometry.LocalFlattening.modulesStalk`: the stalk of an `𝒪_X`-module, read over the
  `CommRingCat`-valued structure presheaf, with its `𝒪_{X,x}`-module structure.
* `AlgebraicGeometry.LocalFlattening.localFlatSituation`: the local flattening problem at a point.
* `AlgebraicGeometry.LocalFlattening.pointedStalkLocalAlgebra`: the local ring of a pointed scheme
  over `(S, s)`, as a local `𝒪_{S,s}`-algebra.
* `AlgebraicGeometry.LocalFlattening.IsFlatAtPrime`: the condition of Stacks 05ML at one prime.

## Main results

* `AlgebraicGeometry.LocalFlattening.finite_modulesStalk`: stalks of finite type modules are
  finite, in the `modulesStalk` spelling.
* `AlgebraicGeometry.LocalFlattening.conditionOn_iff_forall_isFlatAtPrime` and
  `AlgebraicGeometry.LocalFlattening.isFlatAtPrime_iff_flat_tensor`: the condition prime by prime,
  and at one prime through a localization.
* `AlgebraicGeometry.LocalFlattening.condition_iff_forall_isFlatOverAt`: the condition of
  Stacks 05ML for the local flattening problem at `x` and the local ring of `(T, t)` is flatness
  of `F_T` over `T` at the points of `X_T` above `t` and `x`.

## Implementation notes

The point of `X_T` at a prime `q` of `𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{T,t}` is the image of `q` under the
canonical morphism `Spec(𝒪_{X,x} ⊗ 𝒪_{T,t}) ⟶ X_T`, which is a flat preimmersion; conversely the
local ring of `X_T` at a point is a localization of that tensor product
(`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`), and the stalk of the pulled
back module is the base change of the stalk (Stacks 0098). This module does not import the
henselian flattening theorem: that import brings a second, propositionally but not definitionally
equal, module structure on stalks into scope.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PH](https://stacks.math.columbia.edu/tag/05PH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.LocalFlattening

open Opposite TopologicalSpace

/-- The stalk map at a point over `y`, composed with the canonical morphism from the spectrum of
the local ring of `Y` at `y`, is the canonical morphism from the spectrum of the local ring of
`X` followed by `g`. -/
theorem specMap_pointedStalkMap_fromSpecStalk
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
    let e : CommRingCat.of (Y.presheaf.stalk y) ⟶
        CommRingCat.of (Y.presheaf.stalk (g x)) :=
      eqToHom (congrArg Y.presheaf.stalk h).symm
    Spec.map (e ≫ g.stalkMap x) ≫ Y.fromSpecStalk y =
      X.fromSpecStalk x ≫ g := by
  subst y
  simp [Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The stalk at `x` of an `𝒪_X`-module, read over the `CommRingCat`-valued structure presheaf
of `X`, which is where Mathlib's module structure over `𝒪_{X,x}` lives and the spelling used by
`AlgebraicGeometry.IsFlatOverAt`. -/
def modulesStalk {X : Scheme.{u}} (F : X.Modules) (x : X) : AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (@PresheafOfModules.presheaf _ _ (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) F.val) x

/-- Mathlib's `𝒪_{X,x}`-module structure on the stalk of an `𝒪_X`-module. -/
instance modulesStalk.instModule {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (modulesStalk F x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The stalk of a module of finite type on a scheme is a finite module over the local ring. -/
theorem finite_modulesStalk {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (x : X) : Module.Finite (X.presheaf.stalk x) (modulesStalk F x) :=
  SheafOfModules.finite_stalk X.sheaf F x

/-- The stalk map `𝒪_{S,s} ⟶ 𝒪_{X,x}` of `f` at a point `x` over `s`. -/
abbrev pointedStalkMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (s : S) (hxs : f x = s) :
    S.presheaf.stalk s ⟶ X.presheaf.stalk x :=
  eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x

/-- The pointed stalk map is a local homomorphism. -/
instance isLocalHom_pointedStalkMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (s : S)
    (hxs : f x = s) : IsLocalHom (pointedStalkMap f x s hxs).hom :=
  CommRingCat.isLocalHom_comp _ (f.stalkMap x)

/-- The local flattening problem of Stacks 05MK at a point `x` of `X` over `s`: the stalk
`𝒪_{X,x}` over `𝒪_{S,s}` and the stalk `F_x`. -/
abbrev localFlatSituation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (x : X) (s : S) (hxs : f x = s) :
    Module.FlatAtPointSituation.{u, u, u} :=
  letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    (pointedStalkMap f x s hxs).hom.toAlgebra
  { A := S.presheaf.stalk s
    B := X.presheaf.stalk x
    M := modulesStalk F x
    isLocalHomAB := isLocalHom_pointedStalkMap f x s hxs }

/-- The local ring of a pointed scheme over `(S, s)`, as an object of the category of local
`𝒪_{S,s}`-algebras of Stacks 05MK. -/
abbrev pointedStalkLocalAlgebra
    {S T : Scheme.{u}} (g : T ⟶ S) (s : S) (t : T) (ht : g t = s) :
    LocalAlgCat.{u, u} (S.presheaf.stalk s) :=
  letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    (pointedStalkMap g t s ht).hom.toAlgebra
  { carrier := T.presheaf.stalk t
    isLocalHom := isLocalHom_pointedStalkMap g t s ht }

private lemma pullbackMap_comp_mono_isIso {A B W Z : Scheme.{u}}
    (a : A ⟶ W) (b : B ⟶ W) (i : W ⟶ Z) [Mono i] :
    IsIso (pullback.map a b (a ≫ i) (b ≫ i) (𝟙 A) (𝟙 B) i
      (by simp) (by simp)) := by
  let k : pullback (a ≫ i) (b ≫ i) ⟶ pullback a b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      ((cancel_mono i).mp (by simpa only [Category.assoc] using
        (pullback.condition : pullback.fst (a ≫ i) (b ≫ i) ≫ (a ≫ i) =
          pullback.snd (a ≫ i) (b ≫ i) ≫ (b ≫ i))))
  refine ⟨⟨k, ?_, ?_⟩⟩
  · ext <;> simp [k, pullback.map, Category.assoc]
  · ext <;> simp [k, pullback.map, Category.assoc]

private lemma flat_stalkTensorToPullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : X) (t : T) (s : S) (hxs : f x = s) (ht : g t = s)
    [IsIso (S.fromSpecStalk s)] :
    Flat (stalkTensorToPullback f g x t s hxs ht) := by
  let A := S.presheaf.stalk s
  let B := X.presheaf.stalk x
  let R := T.presheaf.stalk t
  let : Algebra A B :=
    ((eqToHom (congrArg S.presheaf.stalk hxs).symm ≫ f.stalkMap x).hom).toAlgebra
  let : Algebra A R :=
    ((eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t).hom).toAlgebra
  let iX := X.fromSpecStalk x
  let iT := T.fromSpecStalk t
  let iS := S.fromSpecStalk s
  have hB : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ iS = iX ≫ f :=
    specMap_pointedStalkMap_fromSpecStalk f x s hxs
  have hR : Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ iS = iT ≫ g :=
    specMap_pointedStalkMap_fromSpecStalk g t s ht
  let α := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let β := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let m₀ := pullback.map α β (α ≫ iS) (β ≫ iS) (𝟙 _) (𝟙 _) iS
    (by simp) (by simp)
  have hB' : (α ≫ iS) ≫ 𝟙 S = iX ≫ f := by simpa only [Category.comp_id] using hB
  have hR' : (β ≫ iS) ≫ 𝟙 S = iT ≫ g := by simpa only [Category.comp_id] using hR
  let m₁ := pullback.map (α ≫ iS) (β ≫ iS) f g iX iT (𝟙 S) hB' hR'
  have hm₁ : Flat m₁ :=
    MorphismProperty.pullbackMap (P := @Flat) (flat_fromSpecStalk X x) (flat_fromSpecStalk T t)
      hB' hR'
  have hm₀ : IsIso m₀ := by
    dsimp [m₀]
    exact pullbackMap_comp_mono_isIso α β iS
  have hcomp : pullback.map α β f g iX iT iS hB hR = m₀ ≫ m₁ := by
    ext <;> simp [m₀, m₁, pullback.map, Category.assoc]
  change Flat ((pullbackSpecIso A B R).inv ≫
      pullback.map α β f g iX iT iS hB hR)
  rw [hcomp]
  infer_instance

/-- The flatness condition of Stacks 05ML at one prime `q` of `B' = B ⊗_A R`: the localization
at `q` of `M' = B' ⊗_B M` is flat over `R`, for the `R`-action restricted along `R → B'`. -/
def IsFlatAtPrime (S : Module.FlatAtPointSituation.{u, u, u}) (R : Type u) [CommRing R]
    [Algebra S.A R] (q : Ideal (TensorProduct S.A S.B R)) [q.IsPrime] : Prop :=
  letI : Algebra R (TensorProduct S.A S.B R) :=
    (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom.toAlgebra
  letI : Module R (LocalizedModule q.primeCompl
      (TensorProduct S.B (TensorProduct S.A S.B R) S.M)) :=
    Module.compHom _ (algebraMap R (TensorProduct S.A S.B R))
  Module.Flat R (LocalizedModule q.primeCompl (TensorProduct S.B (TensorProduct S.A S.B R) S.M))

/-- **Stacks Project, Tag 05ML**, prime by prime: the condition holds exactly when the base change
is flat at every prime of `B ⊗_A R` containing the extensions of the two maximal ideals. -/
theorem conditionOn_iff_forall_isFlatAtPrime (S : Module.FlatAtPointSituation.{u, u, u})
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra S.A R] :
    S.ConditionOn R ↔
      letI : Algebra R (TensorProduct S.A S.B R) :=
        (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom.toAlgebra
      ∀ (q : Ideal (TensorProduct S.A S.B R)) (_hq : q.IsPrime),
        Ideal.map (algebraMap R (TensorProduct S.A S.B R)) (IsLocalRing.maximalIdeal R) ⊔
            Ideal.map (algebraMap S.B (TensorProduct S.A S.B R))
              (IsLocalRing.maximalIdeal S.B) ≤ q →
          IsFlatAtPrime S R q :=
  S.conditionOn_iff_flatAtClosedFiberPrimes R

/-- If `C` is the localization of `B' = B ⊗_A R` at `q`, the condition at `q` is flatness over `R`
of `C ⊗_B M`. -/
theorem isFlatAtPrime_iff_flat_tensor (S : Module.FlatAtPointSituation.{u, u, u})
    (R : Type u) [CommRing R] [Algebra S.A R] (q : Ideal (TensorProduct S.A S.B R)) [q.IsPrime]
    (C : Type u) [CommRing C] [Algebra (TensorProduct S.A S.B R) C]
    [IsLocalization q.primeCompl C] [Algebra S.B C] [Algebra R C]
    [IsScalarTower S.B (TensorProduct S.A S.B R) C]
    (hR : ∀ r : R, algebraMap R C r =
      algebraMap (TensorProduct S.A S.B R) C (Algebra.TensorProduct.includeRight r)) :
    IsFlatAtPrime S R q ↔ Module.Flat R (TensorProduct S.B C S.M) := by
  let : Algebra R (TensorProduct S.A S.B R) :=
    (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom.toAlgebra
  have : IsScalarTower R (TensorProduct S.A S.B R) C :=
    IsScalarTower.of_algebraMap_eq hR
  let N := TensorProduct S.B (TensorProduct S.A S.B R) S.M
  let : Module R (LocalizedModule q.primeCompl N) :=
    Module.compHom _ (algebraMap R (TensorProduct S.A S.B R))
  let : SMul R (LocalizedModule q.primeCompl N) :=
    (Module.compHom (LocalizedModule q.primeCompl N)
      (algebraMap R (TensorProduct S.A S.B R))).toSMul
  have : IsScalarTower R (TensorProduct S.A S.B R) (LocalizedModule q.primeCompl N) :=
    IsScalarTower.of_compHom R _ _
  let e₁ := IsLocalizedModule.linearEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl N)
    (TensorProduct.mk (TensorProduct S.A S.B R) C N 1)
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange S.B
    (TensorProduct S.A S.B R) C C S.M
  exact Module.Flat.equiv_iff
    ((e₁.trans (e₂.restrictScalars (TensorProduct S.A S.B R))).restrictScalars R)

/-- `BaseChangeStalk.pullback_stalk_isLocalization` with the point of the base named, the two
structure maps being the pointed stalk maps. -/
private lemma pullback_stalk_isLocalization_at {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (y : pullback (C := Scheme.{u}) f g) (s : S) (hxs : f (pullback.fst f g y) = s)
    (hts : g (pullback.snd f g y) = s) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y)) :=
      (pointedStalkMap f _ s hxs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk (pullback.snd f g y)) :=
      (pointedStalkMap g _ s hts).hom.toAlgebra
    ∃ φ : TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y)) →+* (pullback f g).presheaf.stalk y,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = ((pullback.fst f g).stalkMap y).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap y).hom ∧
      letI : Algebra (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y))) ((pullback f g).presheaf.stalk y) :=
        φ.toAlgebra
      ∃ N : Submonoid (TensorProduct (S.presheaf.stalk s)
          (X.presheaf.stalk (pullback.fst f g y)) (T.presheaf.stalk (pullback.snd f g y))),
        IsLocalization N ((pullback f g).presheaf.stalk y) := by
  subst hxs
  exact BaseChangeStalk.pullback_stalk_isLocalization f g y

/-- If `φ ∘ i` is a local homomorphism `ψ`, then `i` maps the maximal ideal into the preimage
of the maximal ideal under `φ`. -/
private lemma map_maximalIdeal_le_comap_of_comp_eq {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [IsLocalRing A] [IsLocalRing C] (i : A →+* B) (φ : B →+* C) (ψ : A →+* C)
    [IsLocalHom ψ] (h : φ.comp i = ψ) :
    (IsLocalRing.maximalIdeal A).map i ≤ (IsLocalRing.maximalIdeal C).comap φ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, h]
  exact (IsLocalRing.maximalIdeal_comap ψ).ge

/-- A ring map from the tensor product of the stalks to the stalk of the pullback, compatible
with the two projections, factors `fromSpecStalk` through `stalkTensorToPullback`. -/
private lemma specMap_comp_stalkTensorToPullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (y : pullback (C := Scheme.{u}) f g) (s : S) (hxs : f (pullback.fst f g y) = s)
    (hts : g (pullback.snd f g y) = s) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y)) :=
      (pointedStalkMap f _ s hxs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk (pullback.snd f g y)) :=
      (pointedStalkMap g _ s hts).hom.toAlgebra
    ∀ φ : TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y))
        (T.presheaf.stalk (pullback.snd f g y)) →+* (pullback f g).presheaf.stalk y,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = ((pullback.fst f g).stalkMap y).hom →
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap y).hom →
      Spec.map (CommRingCat.ofHom φ) ≫ stalkTensorToPullback f g _ _ s hxs hts =
        (pullback f g).fromSpecStalk y := by
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk (pullback.fst f g y)) :=
    (pointedStalkMap f _ s hxs).hom.toAlgebra
  let : Algebra (S.presheaf.stalk s) (T.presheaf.stalk (pullback.snd f g y)) :=
    (pointedStalkMap g _ s hts).hom.toAlgebra
  intro φ hleft hright
  apply pullback.hom_ext
  · rw [Category.assoc, stalkTensorToPullback_fst, ← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ CommRingCat.ofHom φ =
        (pullback.fst f g).stalkMap y from CommRingCat.hom_ext hleft]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk _
  · rw [Category.assoc, stalkTensorToPullback_snd, ← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ CommRingCat.ofHom φ =
        (pullback.snd f g).stalkMap y from CommRingCat.hom_ext hright]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk _

private lemma exists_tensorPrime_over_pullback_point
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules)
    (x : X) (s : S) (t : T) (hxs : f x = s) (ht : g t = s)
    (y : pullback (C := Scheme.{u}) f g)
    (hyT : pullback.snd f g y = t) (hyX : pullback.fst f g y = x) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
      (pointedStalkMap f x s hxs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
      (pointedStalkMap g t s ht).hom.toAlgebra
    ∃ (q : Ideal (TensorProduct (S.presheaf.stalk s) (X.presheaf.stalk x)
        (T.presheaf.stalk t))) (hq : q.IsPrime),
      Ideal.map Algebra.TensorProduct.includeLeftRingHom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≤ q ∧
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) ≤ q ∧
      stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩ = y ∧
      (AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
        ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y ↔
        @IsFlatAtPrime (localFlatSituation f F x s hxs) (T.presheaf.stalk t) _ _ q hq) := by
  subst hyX hyT
  let pX : pullback f g ⟶ X := pullback.fst f g
  let pT : pullback f g ⟶ T := pullback.snd f g
  let A := S.presheaf.stalk s
  let B := X.presheaf.stalk (pX y)
  let R := T.presheaf.stalk (pT y)
  let C := (pullback f g).presheaf.stalk y
  let : Algebra A B := (pointedStalkMap f (pX y) s hxs).hom.toAlgebra
  let : Algebra A R := (pointedStalkMap g (pT y) s ht).hom.toAlgebra
  obtain ⟨φ, hleft, hright, ⟨N, hN⟩⟩ := pullback_stalk_isLocalization_at f g y s hxs ht
  let Q := TensorProduct A B R
  let : Algebra Q C := φ.toAlgebra
  let q : Ideal Q := (IsLocalRing.maximalIdeal C).comap φ
  have : q.IsPrime := Ideal.comap_isPrime φ _
  let : IsLocalization N C := hN
  let : IsLocalization q.primeCompl C :=
    isLocalization_primeCompl_of_comap_maximalIdeal N q rfl
  have hpoint : stalkTensorToPullback f g (pX y) (pT y) s hxs ht ⟨q, inferInstance⟩ = y := by
    change (Spec.map (CommRingCat.ofHom φ) ≫ stalkTensorToPullback f g (pX y) (pT y) s hxs ht)
      (IsLocalRing.closedPoint C) = y
    rw [specMap_comp_stalkTensorToPullback f g y s hxs ht φ hleft hright]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨q, inferInstance, map_maximalIdeal_le_comap_of_comp_eq _ φ _ hleft,
    map_maximalIdeal_le_comap_of_comp_eq _ φ _ hright, hpoint, ?_⟩
  let M := modulesStalk F (pX y)
  let Ppre : PresheafOfModules
      ((pullback f g).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    ((modulePullback pX.toLRSHom.toShHom).obj F).val
  let P := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Ppre.presheaf y
  let : Algebra B C := (pX.stalkMap y).hom.toAlgebra
  let : Algebra R C := (pT.stalkMap y).hom.toAlgebra
  let : Algebra B Q := Algebra.TensorProduct.leftAlgebra
  let : Algebra R Q := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B Q C := IsScalarTower.of_algebraMap_eq' hleft.symm
  have : IsScalarTower R Q C := IsScalarTower.of_algebraMap_eq' hright.symm
  let : Module R P := Module.compHom P (pT.stalkMap y).hom
  have : IsScalarTower R C P := IsScalarTower.of_compHom R C P
  let e := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv pX.toLRSHom.toShHom F y)
  exact (Module.Flat.equiv_iff (e.restrictScalars R)).trans
    (isFlatAtPrime_iff_flat_tensor (localFlatSituation f F (pX y) s hxs) R q C
      (fun r => (RingHom.congr_fun hright r).symm)).symm

/-- **The condition of Stacks 05ML at a point, read geometrically.** For the local flattening
problem at `x` over `s` and the local ring of a pointed scheme `(T, t)` over `(S, s)`, the
condition holds exactly when the pullback of `F` to `X ×_S T` is flat over `T` at every point
lying over `t` and `x`. -/
theorem condition_iff_forall_isFlatOverAt
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules)
    (x : X) (s : S) (t : T) (hxs : f x = s) (ht : g t = s) :
    (localFlatSituation f F x s hxs).Condition
        (pointedStalkLocalAlgebra g s t ht) ↔
      ∀ y : pullback (C := Scheme.{u}) f g,
        pullback.snd f g y = t → pullback.fst f g y = x →
          AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
            ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y := by
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    (pointedStalkMap f x s hxs).hom.toAlgebra
  let : Algebra (S.presheaf.stalk s) (T.presheaf.stalk t) :=
    (pointedStalkMap g t s ht).hom.toAlgebra
  change (localFlatSituation f F x s hxs).ConditionOn (T.presheaf.stalk t) ↔ _
  rw [conditionOn_iff_forall_isFlatAtPrime]
  constructor
  · intro h y hyT hyX
    obtain ⟨q, hq, hqB, hqR, _, he⟩ :=
      exists_tensorPrime_over_pullback_point f g F x s t hxs ht y hyT hyX
    exact he.mpr (h q hq (sup_le hqR hqB))
  · intro h q hq hqBR
    let := hq
    have hqB : Ideal.map Algebra.TensorProduct.includeLeftRingHom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≤ q :=
      le_sup_right.trans hqBR
    have hqR : Ideal.map Algebra.TensorProduct.includeRight.toRingHom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) ≤ q :=
      le_sup_left.trans hqBR
    obtain ⟨hyX, hyT⟩ := stalkTensorToPullback_projections_of_maximal_comap
      f g x t s hxs ht q hq hqB hqR
    obtain ⟨q', hq', _, _, hp, he⟩ := exists_tensorPrime_over_pullback_point
      f g F x s t hxs ht (stalkTensorToPullback f g x t s hxs ht ⟨q, hq⟩) hyT hyX
    obtain rfl : q' = q := congrArg PrimeSpectrum.asIdeal
      ((isPreimmersion_stalkTensorToPullback f g x t s hxs ht).isEmbedding.injective hp)
    exact he.mp (h _ hyT hyX)

end AlgebraicGeometry.LocalFlattening
