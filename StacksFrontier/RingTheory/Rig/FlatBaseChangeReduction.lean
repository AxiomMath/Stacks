module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.Rig.FlatEtaleLocalization
public import StacksFrontier.RingTheory.Rig.FlatIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Finite

/-!
# Replacing the base of a rig-flat base change by a completed principal localization

For an ideal `K` of a ring `T` and `f : T`, the completed principal localization `T_{\{f\}}` is
`Rig.CompletedAway K f`, the adic completion of `T[1/f]` along the extension of `K`. Only the
quotients `T ⧸ Kⁿ` enter `T_{\{f\}}`, so a homomorphism which is bijective on all of them induces
a bijection of completed principal localizations; in particular a ring and its adic completion
have the same completed principal localizations. For homomorphisms `A → B` and `A → C` of adic
rings, with `C` Noetherian, and `f ∈ C`, this gives an identification
`(B ⊗̂_A C)_{\{f\}} = B ⊗̂_A C_{\{f\}}` compatible with the maps out of `C_{\{f\}}`, and if
`A → C` is continuous, adic and topologically of finite type then so is `A → C_{\{f\}}`.

## Main results

* `Rig.bijective_quotientMap_pow_awayMap`: a homomorphism bijective on the quotients by the
  powers of an ideal stays so after inverting an element.
* `Rig.bijective_completedAwayMap_of_quotientMap_bijective`: such a homomorphism induces a
  bijection of completed principal localizations.
* `Rig.bijective_completedAwayMap_algebraMap_adicCompletion`: completing the ring first does not
  change its completed principal localizations.
* `Rig.bijective_completedAwayMap_coe_completion`: the same for the uniform completion along a
  finitely generated ideal of definition, and
  `Rig.bijective_completedAwayMap_coe_completedTensorProduct` for the tensor-product topology,
  so the completed principal localizations of `B ⊗̂_A C` are those of `B ⊗_A C`.
* `Rig.bijective_quotientMap_tensorProduct_map`: tensoring preserves levelwise bijectivity.
* `Rig.bijective_adicCompletionMap_tensorProduct_map`: hence base change preserves being an
  adic completion — completing the second factor does not change the completed tensor
  product.
* `Rig.isAdic_of_isAdic_of_pow_le_of_pow_le` and `Rig.isAdic_map_includeRight_of_isAdic`: ideals
  with mutually cofinal powers define the same adic topology, so every ideal of definition of
  `C` extends to one of `B ⊗[A] C`.
* `Rig.tensorProductEquivAway_comp_map` and `Rig.map_tensorProductEquivAway_ideal`:
  `(B ⊗[A] C)[1/f] = B ⊗[A] C[1/f]`, compatibly with the maps from `B ⊗[A] C` and with the
  extension of an ideal of `C`.
* `Rig.ringEquiv_trans_symm_trans_apply`: a composite of four isomorphisms followed on one
  element.
* `Rig.adicCompletionCongr_of`, `Rig.ofBijective_adicCompletionMap_of` and
  `Rig.ofBijective_completedAwayMap_of`: each comparison read on the image of the uncompleted
  ring.
* `Rig.nonempty_ringEquiv_completedTensorProduct_completedAway`: the identification
  `(B ⊗̂_A C)_{f} = B ⊗̂_A C_{f}`, as an isomorphism of rings.
* `Rig.map_map_algebraMap_completedAway`: the ideal of definition of `C_{\{f\}}` extended from
  `C` is the extension of its extension to `C[1/f]`.
* `Rig.exists_ringEquiv_completion_adicCompletion_away`: a composite of four comparisons of
  completions joining five rings, together with its value on elements matched by them.
* `Rig.exists_ringEquiv_completedTensorProduct_completedAway_apply`: the identification
  `(B ⊗̂_A C)_{f} = B ⊗̂_A C_{f}` together with its value on the image of `C`.
* `Rig.exists_ringEquiv_comp_algebraMap_eq_completedAwayMap`: under the identification,
  `C_{\{f\}} → B ⊗̂[A] C_{\{f\}}` is the map `C_{\{f\}} → (B ⊗̂[A] C)_{\{f\}}`.
* `Rig.isNoetherianAdic_completedAway`: a completed principal localization of a Noetherian adic
  ring along one of its ideals of definition is again a Noetherian adic ring.
* `Rig.completedAway_adicFiniteType_comp`: if `A → C` is continuous, adic and topologically of
  finite type, then so is the composite `A → C → C_{f}`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGM](https://stacks.math.columbia.edu/tag/0GGM)
* [Stacks Project, Tag 0GGP](https://stacks.math.columbia.edu/tag/0GGP)
* [Stacks Project, Tag 0GBZ](https://stacks.math.columbia.edu/tag/0GBZ)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public section

namespace Rig

open scoped TensorProduct

universe u

/-! ### Completed principal localizations detect only the level-`n` quotients -/

/-- The map of principal localizations composed with the structure map. -/
theorem awayMap_comp_algebraMap {X Y : Type*} [CommRing X] [CommRing Y] (g : X →+* Y) (x : X) :
    (IsLocalization.Away.map (Localization.Away x) (Localization.Away (g x)) g x).comp
        (algebraMap X (Localization.Away x)) =
      (algebraMap Y (Localization.Away (g x))).comp g := by
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply]
  exact IsLocalization.map_eq _ _

/-- The extension of a power of `J` to the localization away from `x`, pushed into the
localization of `Y`, is the extension of its image. -/
theorem map_pow_awayMap {X Y : Type*} [CommRing X] [CommRing Y] (g : X →+* Y) (J : Ideal X)
    (x : X) (n : ℕ) :
    ((J ^ n).map (algebraMap X (Localization.Away x))).map
        (IsLocalization.Away.map (Localization.Away x) (Localization.Away (g x)) g x) =
      ((J ^ n).map g).map (algebraMap Y (Localization.Away (g x))) := by
  rw [Ideal.map_map, awayMap_comp_algebraMap, ← Ideal.map_map]

/-- **Levelwise bijectivity localizes.** If `g` induces a bijection `X ⧸ Jⁿ → Y ⧸ Jⁿ·Y`, then
the induced map of localizations away from `x` and `g x` is bijective modulo the extension of
`Jⁿ·Y`. -/
theorem bijective_quotientMap_map_pow_awayMap {X Y : Type*} [CommRing X] [CommRing Y]
    (g : X →+* Y) (J : Ideal X) (x : X) (n : ℕ)
    (h : Function.Bijective (Ideal.quotientMap ((J ^ n).map g) g Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      (((J ^ n).map g).map (algebraMap Y (Localization.Away (g x))))
      (IsLocalization.Away.map (Localization.Away x) (Localization.Away (g x)) g x)
      (map_pow_awayMap g J x n ▸ Ideal.le_comap_map)) := by
  classical
  let XL := Localization.Away x
  let YL := Localization.Away (g x)
  let Jn : Ideal X := J ^ n
  let JnY : Ideal Y := Jn.map g
  let e : (X ⧸ Jn) ≃+* (Y ⧸ JnY) := RingEquiv.ofBijective _ h
  have he (a : X) : e (Ideal.Quotient.mk Jn a) = Ideal.Quotient.mk JnY (g a) := rfl
  let : Algebra (X ⧸ Jn) (YL ⧸ JnY.map (algebraMap Y YL)) :=
    ((algebraMap (Y ⧸ JnY) (YL ⧸ JnY.map (algebraMap Y YL))).comp e.toRingHom).toAlgebra
  have hM : (Algebra.algebraMapSubmonoid (X ⧸ Jn) (Submonoid.powers x)).map e.toMonoidHom =
      Algebra.algebraMapSubmonoid (Y ⧸ JnY) (Submonoid.powers (g x)) := by
    rw [Algebra.algebraMapSubmonoid_powers, Algebra.algebraMapSubmonoid_powers,
      Submonoid.map_powers]
    exact congrArg Submonoid.powers (he x)
  have : IsLocalization (Algebra.algebraMapSubmonoid (X ⧸ Jn) (Submonoid.powers x))
      (YL ⧸ JnY.map (algebraMap Y YL)) :=
    IsLocalization.of_ringEquiv_left e hM (fun _ ↦ rfl)
  refine IsLocalization.bijective
    (M := Algebra.algebraMapSubmonoid (X ⧸ Jn) (Submonoid.powers x)) _ ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply]
  exact congrArg (Ideal.Quotient.mk (JnY.map (algebraMap Y YL))) (IsLocalization.map_eq _ _)

/-- Bijectivity of a map of quotients only depends on the ideals up to equality. -/
private theorem bijective_quotientMap_of_eq {P Q : Type*} [CommRing P] [CommRing Q] (G : P →+* Q)
    {K₁ K₂ : Ideal P} {S₁ S₂ : Ideal Q} (hK : K₁ = K₂) (hS : S₁ = S₂)
    {h₁ : K₁ ≤ S₁.comap G} {h₂ : K₂ ≤ S₂.comap G}
    (h : Function.Bijective (Ideal.quotientMap S₁ G h₁)) :
    Function.Bijective (Ideal.quotientMap S₂ G h₂) := by
  subst hK hS
  exact h

/-- **Levelwise bijectivity localizes.** If `g` induces a bijection `X ⧸ Jⁿ → Y ⧸ Jⁿ·Y`, then
the induced map of localizations away from `x` and `g x` is bijective modulo the extension of the
`n`-th power of the extension of `J`. -/
theorem bijective_quotientMap_pow_awayMap {X Y : Type*} [CommRing X] [CommRing Y]
    (g : X →+* Y) (J : Ideal X) (x : X) (n : ℕ)
    (h : Function.Bijective (Ideal.quotientMap ((J ^ n).map g) g Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      (((J.map (algebraMap X (Localization.Away x))) ^ n).map
        (IsLocalization.Away.map (Localization.Away x) (Localization.Away (g x)) g x))
      (IsLocalization.Away.map (Localization.Away x) (Localization.Away (g x)) g x)
      Ideal.le_comap_map) := by
  refine bijective_quotientMap_of_eq _ (Ideal.map_pow _ J n) ?_
    (bijective_quotientMap_map_pow_awayMap g J x n h)
  rw [← Ideal.map_pow]
  exact (map_pow_awayMap g J x n).symm

/-- `Stacks.Nagata.PthRootDescent.mapAdicCompletion` is `adicCompletionMap` of the structure
map. -/
theorem mapAdicCompletion_eq_adicCompletionMap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J) :
    Stacks.Nagata.PthRootDescent.mapAdicCompletion I J h =
      adicCompletionMap (algebraMap A B) I J h :=
  RingHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ by
    rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion, adicCompletionMap_evalₐ]

/-- If `J = I·B` and `f` is bijective modulo `Iⁿ` for every `n`, then `adicCompletionMap f I J`
is bijective. -/
theorem adicCompletionMap_bijective_of_quotientMap_bijective_of_eq {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B) (hJ : I.map f = J)
    (h : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)) :
    Function.Bijective (adicCompletionMap f I J (le_of_eq hJ)) := by
  subst hJ
  exact Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective f I h

/-- **A homomorphism which is bijective on all the level-`n` quotients induces a bijection of
completed principal localizations.** A homomorphism `φ : T →+* D` inducing bijections
`T ⧸ Kⁿ → D ⧸ Kⁿ·D` for every `n` induces a bijection `T_{\{f\}} → D_{\{φ f\}}`. -/
theorem bijective_completedAwayMap_of_quotientMap_bijective {T D : Type*} [CommRing T]
    [CommRing D] (φ : T →+* D) (K : Ideal T) (f : T)
    (h : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap ((K ^ n).map φ) φ Ideal.le_comap_map)) :
    Function.Bijective (RingHom.completedAwayMap φ K f) := by
  let TL := Localization.Away f
  let DL := Localization.Away (φ f)
  let φloc := IsLocalization.Away.map TL DL φ f
  let : Algebra TL DL := φloc.toAlgebra
  have hloc (n : ℕ) : Function.Bijective
      (Ideal.quotientMap (((K.map (algebraMap T TL)) ^ n).map φloc) φloc Ideal.le_comap_map) :=
    bijective_quotientMap_pow_awayMap φ K f n (h n)
  have hJ : (K.map (algebraMap T TL)).map φloc = (K.map φ).map (algebraMap D DL) := by
    rw [Ideal.map_map, awayMap_comp_algebraMap, ← Ideal.map_map]
  show Function.Bijective (Stacks.Nagata.PthRootDescent.mapAdicCompletion
    (K.map (algebraMap T TL)) ((K.map φ).map (algebraMap D DL)) (le_of_eq hJ))
  rw [mapAdicCompletion_eq_adicCompletionMap]
  exact adicCompletionMap_bijective_of_quotientMap_bijective_of_eq φloc _ _ hJ hloc

/-- The canonical map to an adic completion is bijective on every level-`n` quotient. -/
theorem bijective_quotientMap_pow_algebraMap_adicCompletion {T : Type*} [CommRing T]
    (K : Ideal T) (hK : K.FG) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((K ^ n).map (algebraMap T (AdicCompletion K T)))
      (algebraMap T (AdicCompletion K T)) Ideal.le_comap_map) := by
  let That := AdicCompletion K T
  let φ : T →+* That := algebraMap T That
  let e : (That ⧸ (K ^ n).map φ) ≃+* (T ⧸ K ^ n) :=
    (Ideal.quotEquivOfEq (AdicCompletion.ker_evalₐ_eq_map_pow K hK n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ K n))
  have he (y : That) : e (Ideal.Quotient.mk ((K ^ n).map φ) y) =
      AdicCompletion.evalₐ K n y := by
    simp only [e, RingEquiv.trans_apply]
    rfl
  have hinv : Ideal.quotientMap ((K ^ n).map φ) φ Ideal.le_comap_map = e.symm.toRingHom :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ by
      have hmk : e (Ideal.Quotient.mk ((K ^ n).map φ) (φ a)) =
          Ideal.Quotient.mk (K ^ n) a := by
        rw [he]; exact AdicCompletion.evalₐ_of K n a
      simp only [RingHom.comp_apply]
      refine e.injective ?_
      rw [Ideal.quotientMap_mk, hmk]
      exact (e.apply_symm_apply (Ideal.Quotient.mk (K ^ n) a)).symm)
  rw [hinv]
  exact e.symm.bijective

/-- **Completing the ring first does not change the completed principal localization.** For a
finitely generated ideal `K` of a ring `T` and an element `f : T`, the canonical map from the
completed principal localization `T_{\{f\}}` to that of the adic completion `T^∧` at the image
of `f` is bijective. -/
theorem bijective_completedAwayMap_algebraMap_adicCompletion {T : Type*} [CommRing T]
    (K : Ideal T) (hK : K.FG) (f : T) :
    Function.Bijective (RingHom.completedAwayMap (algebraMap T (AdicCompletion K T)) K f) :=
  bijective_completedAwayMap_of_quotientMap_bijective _ K f
    (bijective_quotientMap_pow_algebraMap_adicCompletion K hK)

/-- Levelwise bijectivity is unaffected by an isomorphism of the target. -/
theorem bijective_quotientMap_pow_of_ringEquiv {X Y Z : Type*} [CommRing X] [CommRing Y]
    [CommRing Z] (φ : X →+* Y) (ε : Y ≃+* Z) (J : Ideal X) (n : ℕ)
    (h : Function.Bijective (Ideal.quotientMap ((J ^ n).map (ε.toRingHom.comp φ))
      (ε.toRingHom.comp φ) Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap ((J ^ n).map φ) φ Ideal.le_comap_map) := by
  have hJ : (J ^ n).map (ε.toRingHom.comp φ) = ((J ^ n).map φ).map ε.toRingHom :=
    (Ideal.map_map _ _).symm
  let δ : (Y ⧸ (J ^ n).map φ) ≃+* (Z ⧸ (J ^ n).map (ε.toRingHom.comp φ)) :=
    Ideal.quotientEquiv _ _ ε hJ
  have heq : Ideal.quotientMap ((J ^ n).map (ε.toRingHom.comp φ)) (ε.toRingHom.comp φ)
        Ideal.le_comap_map =
      δ.toRingHom.comp (Ideal.quotientMap ((J ^ n).map φ) φ Ideal.le_comap_map) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have hpt (u : X ⧸ J ^ n) :
      Ideal.quotientMap ((J ^ n).map (ε.toRingHom.comp φ)) (ε.toRingHom.comp φ)
          Ideal.le_comap_map u =
        δ (Ideal.quotientMap ((J ^ n).map φ) φ Ideal.le_comap_map u) :=
    DFunLike.congr_fun heq u
  refine ⟨fun u v huv ↦ h.1 ?_, fun z ↦ ?_⟩
  · rw [hpt, hpt, huv]
  · obtain ⟨u, hu⟩ := h.2 (δ z)
    refine ⟨u, δ.injective ?_⟩
    rwa [← hpt]

/-- **A ring and its completion have the same completed principal localizations.**  For a
finitely generated ideal `K` defining the topology of `T`, the canonical map `T → T^∧` to the
uniform completion induces a bijection `T_{\{f\}} → (T^∧)_{\{f\}}` for every `f : T`. -/
theorem bijective_completedAwayMap_coe_completion {T : Type u} [CommRing T] [UniformSpace T]
    [IsTopologicalRing T] [IsUniformAddGroup T] (K : Ideal T) (hKfg : K.FG) (hKadic : IsAdic K)
    (f : T) :
    Function.Bijective (RingHom.completedAwayMap
      (UniformSpace.Completion.coeRingHom : T →+* UniformSpace.Completion T) K f) := by
  let ε := AdicCompletionBridge.adicCompletionRingEquiv K hKadic
  have hcomp : ε.toRingHom.comp (UniformSpace.Completion.coeRingHom : T →+* _) =
      algebraMap T (AdicCompletion K T) :=
    RingHom.ext fun x ↦ by
      show ε (x : UniformSpace.Completion T) = _
      rw [AdicCompletionBridge.adicCompletionRingEquiv_coe]
      exact (AdicCompletion.algebraMap_apply K x).symm
  refine bijective_completedAwayMap_of_quotientMap_bijective _ K f (fun n ↦ ?_)
  refine bijective_quotientMap_pow_of_ringEquiv _ ε K n ?_
  rw [hcomp]
  exact bijective_quotientMap_pow_algebraMap_adicCompletion _ hKfg n

/-- **The completed principal localization of a completed tensor product is the completed
principal localization of the ordinary tensor product.** Let `A → B` and `A → C` be
homomorphisms of linearly topologized rings carrying a finitely generated ideal of definition
`I` of `A` to ideals of definition, so that the tensor-product topology on `B ⊗[A] C` is the
`I`-adic one.  Then for every `f : B ⊗[A] C` the canonical map `B ⊗[A] C → B ⊗̂[A] C` induces a
bijection `(B ⊗[A] C)_{\{f\}} → (B ⊗̂[A] C)_{\{f\}}`. -/
theorem bijective_completedAwayMap_coe_completedTensorProduct {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (I : Ideal A) (hI : I.FG) (hB : IsAdic (I.map (algebraMap A B)))
    (hC : IsAdic (I.map (algebraMap A C))) (f : B ⊗[A] C) :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
    Function.Bijective (RingHom.completedAwayMap
      (UniformSpace.Completion.coeRingHom : (B ⊗[A] C) →+*
        TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))
      (I.map (algebraMap A (B ⊗[A] C))) f) := by
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : IsTopologicalRing (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := C)
  let : IsUniformAddGroup (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  exact bijective_completedAwayMap_coe_completion _ (hI.map _)
    (TopologicalRing.isAdic_tensorProduct_map_algebraMap I hB hC) f

/-! ### Tensoring preserves the comparison of level-`n` quotients -/

/-- Base change along `B` commutes with an algebra map in the second variable. -/
theorem tensorProduct_map_comp_includeRight {A B M N : Type u} [CommRing A] [CommRing B]
    [CommRing M] [CommRing N] [Algebra A B] [Algebra A M] [Algebra A N] (g : M →ₐ[A] N) :
    ((Algebra.TensorProduct.map (AlgHom.id A B) g).comp
        Algebra.TensorProduct.includeRight : M →ₐ[A] B ⊗[A] N) =
      Algebra.TensorProduct.includeRight.comp g :=
  AlgHom.ext fun _ ↦ rfl

/-- The extension to `B ⊗[A] N` of the image of an ideal `L` of `M` is the image of the
extension of `L` to `B ⊗[A] M`. -/
theorem tensorProduct_map_map_ideal {A B M N : Type u} [CommRing A] [CommRing B] [CommRing M]
    [CommRing N] [Algebra A B] [Algebra A M] [Algebra A N] (g : M →ₐ[A] N) (L : Ideal M) :
    (L.map (Algebra.TensorProduct.includeRight : M →ₐ[A] B ⊗[A] M).toRingHom).map
        (Algebra.TensorProduct.map (AlgHom.id A B) g).toRingHom =
      (L.map g.toRingHom).map
        (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg L.map (congrArg AlgHom.toRingHom (tensorProduct_map_comp_includeRight g))

/-- **Tensoring preserves levelwise bijectivity.** If an `A`-algebra map `g : M →ₐ[A] N` induces
a bijection `M ⧸ L → N ⧸ L·N`, then `B ⊗[A] M → B ⊗[A] N` induces a bijection on the quotients
by the extensions of `L` and of `L·N`. -/
theorem bijective_quotientMap_tensorProduct_map {A B M N : Type u} [CommRing A] [CommRing B]
    [CommRing M] [CommRing N] [Algebra A B] [Algebra A M] [Algebra A N] (g : M →ₐ[A] N)
    (L : Ideal M)
    (h : Function.Bijective (Ideal.quotientMap (L.map g.toRingHom) g.toRingHom
      Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      ((L.map g.toRingHom).map
        (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N).toRingHom)
      (Algebra.TensorProduct.map (AlgHom.id A B) g).toRingHom
      (Ideal.map_le_iff_le_comap.mp (le_of_eq (tensorProduct_map_map_ideal g L)))) := by
  let Q : (M ⧸ L) ≃ₐ[A] (N ⧸ L.map g.toRingHom) :=
    AlgEquiv.ofBijective (Ideal.quotientMapₐ (L.map g.toRingHom) g Ideal.le_comap_map) h
  let eM : B ⊗[A] (M ⧸ L) ≃ₐ[A]
      (B ⊗[A] M) ⧸ L.map (Algebra.TensorProduct.includeRight : M →ₐ[A] B ⊗[A] M).toRingHom :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := A) A M B L
  let eN : B ⊗[A] (N ⧸ L.map g.toRingHom) ≃ₐ[A] (B ⊗[A] N) ⧸ (L.map g.toRingHom).map
      (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N).toRingHom :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := A) A N B (L.map g.toRingHom)
  let Φ : B ⊗[A] (M ⧸ L) ≃ₐ[A] B ⊗[A] (N ⧸ L.map g.toRingHom) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) Q
  have heq : Ideal.quotientMap
        ((L.map g.toRingHom).map
          (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N).toRingHom)
        (Algebra.TensorProduct.map (AlgHom.id A B) g).toRingHom
        (Ideal.map_le_iff_le_comap.mp (le_of_eq (tensorProduct_map_map_ideal g L))) =
      (eN.toRingEquiv.toRingHom.comp Φ.toRingEquiv.toRingHom).comp
        eM.symm.toRingEquiv.toRingHom := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun t ↦ ?_)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [heq]
  simp only [RingHom.coe_comp]
  exact eN.bijective.comp (Φ.bijective.comp eM.symm.bijective)

/-- **Base change preserves being an adic completion.** If an `A`-algebra map `g : M →ₐ[A] N`
induces bijections `M ⧸ Lⁿ → N ⧸ Lⁿ·N` for every `n` — for instance the map from `M` to its
`L`-adic completion — then `B ⊗[A] M → B ⊗[A] N` induces a bijection of the completions along
the extensions of `L` and of `L·N`.

So completing the second factor of a tensor product does not change the completion of the
tensor product: `B ⊗̂[A] M = B ⊗̂[A] M^∧`. -/
theorem bijective_adicCompletionMap_tensorProduct_map {A B M N : Type u} [CommRing A]
    [CommRing B] [CommRing M] [CommRing N] [Algebra A B] [Algebra A M] [Algebra A N]
    (g : M →ₐ[A] N) (L : Ideal M)
    (h : ∀ n : ℕ, Function.Bijective (Ideal.quotientMap ((L ^ n).map g.toRingHom) g.toRingHom
      Ideal.le_comap_map)) :
    Function.Bijective (adicCompletionMap
      (Algebra.TensorProduct.map (AlgHom.id A B) g).toRingHom
      (L.map (Algebra.TensorProduct.includeRight : M →ₐ[A] B ⊗[A] M).toRingHom)
      ((L.map g.toRingHom).map
        (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N).toRingHom)
      (le_of_eq (tensorProduct_map_map_ideal g L))) := by
  refine adicCompletionMap_bijective_of_quotientMap_bijective_of_eq _ _ _
    (tensorProduct_map_map_ideal g L) (fun n ↦ ?_)
  refine bijective_quotientMap_of_eq _ (Ideal.map_pow _ L n) ?_
    (bijective_quotientMap_tensorProduct_map (B := B) g (L ^ n) (h n))
  rw [← Ideal.map_pow]
  exact (tensorProduct_map_map_ideal g (L ^ n)).symm

/-! ### Ideals with mutually cofinal powers -/

/-- **Mutually cofinal ideals define the same adic topology.**  If the topology of `R` is the
`K`-adic one and the powers of `J` and `K` are mutually cofinal, then it is the `J`-adic
topology as well. -/
@[ega "I 10.12.1" "Final affine step"]
theorem isAdic_of_isAdic_of_pow_le_of_pow_le {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {J K : Ideal R} (hK : IsAdic K) {m n : ℕ} (hm : K ^ m ≤ J)
    (hn : J ^ n ≤ K) : IsAdic J := by
  obtain ⟨hKopen, hKcofinal⟩ := isAdic_iff.mp hK
  refine (isIdealOfDefinition_iff_isAdic ⟨K, hK⟩ J).mp ⟨?_, fun U hU ↦ ?_⟩
  · exact Ideal.isOpen_of_isOpen_subideal hm (hKopen m)
  · obtain ⟨q, hq⟩ := hKcofinal U hU
    refine ⟨n * q, Set.Subset.trans (SetLike.coe_subset_coe.mpr ?_) hq⟩
    rw [pow_mul]
    exact pow_le_pow_left' hn q

/-- **Every ideal of definition of `C` extends to one of `B ⊗[A] C`.** If `I` is an ideal of `A`
whose extensions to `B` and `C` are ideals of definition and `J` is an ideal of definition of `C`,
then `J · (B ⊗[A] C)` is an ideal of definition of the tensor-product topology. -/
theorem isAdic_map_includeRight_of_isAdic {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] (I : Ideal A)
    (hB : IsAdic (I.map (algebraMap A B))) (hC : IsAdic (I.map (algebraMap A C))) (J : Ideal C)
    (hJ : IsAdic J) :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    IsAdic (J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) := by
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : IsTopologicalRing (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := C)
  have hK : IsAdic (I.map (algebraMap A (B ⊗[A] C))) :=
    TopologicalRing.isAdic_tensorProduct_map_algebraMap I hB hC
  have hIT : (I.map (algebraMap A C)).map
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom =
      I.map (algebraMap A (B ⊗[A] C)) := by
    rw [Ideal.map_map]
    exact congrArg I.map (RingHom.ext fun a ↦
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).commutes a)
  obtain ⟨n, h1, h2⟩ := TopologicalRing.IsIdealOfDefinition.exists_pow_le_and_pow_le
    (isIdealOfDefinition_of_isAdic hJ) (isIdealOfDefinition_of_isAdic hC)
  refine isAdic_of_isAdic_of_pow_le_of_pow_le hK (m := n) (n := n) ?_ ?_
  · rw [← hIT, ← Ideal.map_pow]
    exact Ideal.map_mono h2
  · rw [← Ideal.map_pow, ← hIT]
    exact Ideal.map_mono h1

/-! ### Inverting an element of the second factor -/

section Away

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

private instance awayIsScalarTower (f : C) : IsScalarTower A C (Localization.Away f) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- **Inverting an element of `C` in `B ⊗[A] C` is base change of the localization.** The
isomorphism `B ⊗[A] C[1/f] ≃ (B ⊗[A] C)[1/(1 ⊗ f)]` commutes with the maps from `B ⊗[A] C`. -/
theorem tensorProductEquivAway_comp_map (f : C) :
    (IsLocalization.Away.tensorProductEquivTMulRight A B f
          (Localization.Away f)).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A B)
          (IsScalarTower.toAlgHom A C (Localization.Away f))).toRingHom =
      algebraMap (B ⊗[A] C) (Localization.Away ((1 : B) ⊗ₜ[A] f)) := by
  refine RingHom.ext fun t ↦ ?_
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The extension of an ideal of `C` to `B ⊗[A] C[1/f]` corresponds, under the identification
`B ⊗[A] C[1/f] = (B ⊗[A] C)[1/(1 ⊗ f)]`, to its extension to `(B ⊗[A] C)[1/(1 ⊗ f)]`. -/
theorem map_tensorProductEquivAway_ideal (f : C) (J : Ideal C) :
    ((J.map (algebraMap C (Localization.Away f))).map
          (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f).toRingHom).map
        (IsLocalization.Away.tensorProductEquivTMulRight A B f
          (Localization.Away f)).toRingEquiv.toRingHom =
      (J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).map
        (algebraMap (B ⊗[A] C) (Localization.Away ((1 : B) ⊗ₜ[A] f))) := by
  simp only [Ideal.map_map]
  congr 1
  exact RingHom.ext fun c ↦ by simp

end Away

/-! ### The completed principal localization of a Noetherian adic ring -/

/-- The ideal of definition of a completed principal localization, extended from the ring
itself, is the extension of its extension to the principal localization. -/
theorem map_map_algebraMap_completedAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) :
    (K.map (algebraMap R (Localization.Away g))).map
        (algebraMap (Localization.Away g) (CompletedAway K g)) =
      K.map (algebraMap R (CompletedAway K g)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R (Localization.Away g) (CompletedAway K g)]

/-- A completed principal localization of a Noetherian ring, with the adic topology of the
extended ideal, is a Noetherian adic ring. -/
theorem isNoetherianAdic_completedAway {C : Type u} [CommRing C] [IsNoetherianRing C]
    (I : Ideal C) (f : C) :
    letI : TopologicalSpace (CompletedAway I f) :=
      (I.map (algebraMap C (CompletedAway I f))).adicTopology
    letI : IsTopologicalRing (CompletedAway I f) :=
      (I.map (algebraMap C (CompletedAway I f))).nonarchimedean.toIsTopologicalRing
    IsNoetherianRing (CompletedAway I f) ∧ TopologicalRing.IsAdic (CompletedAway I f) := by
  let localized := Localization.Away f
  let localizedIdeal := I.map (algebraMap C localized)
  let target := CompletedAway I f
  have hmap : localizedIdeal.map (algebraMap localized target) =
      I.map (algebraMap C target) := map_map_algebraMap_completedAway I f
  have hadic := isAdic_adicCompletion localizedIdeal localizedIdeal.fg_of_isNoetherianRing
  exact ⟨inferInstance, Eq.mp (congrArg (fun J : Ideal target ↦
    let : TopologicalSpace target := J.adicTopology
    have : IsTopologicalRing target := J.nonarchimedean.toIsTopologicalRing
    TopologicalRing.IsAdic target) hmap) hadic⟩

/-- **The replacement of `C` by `C_{\{f\}}`.** If `A → C` is a continuous, adic homomorphism of
topological finite type between Noetherian adic rings, `I` is an ideal of definition of `C` and
`f : C`, then the composite `A → C → C_{\{f\}}` is again continuous, adic and topologically of
finite type. -/
theorem completedAway_adicFiniteType_comp {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C] (φ : A →+* C)
    (hφ : Continuous φ)
    (hP : _root_.RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ)
    (I : Ideal C) (hI : IsAdic I) (f : C) :
    letI : TopologicalSpace (CompletedAway I f) :=
      (I.map (algebraMap C (CompletedAway I f))).adicTopology
    letI : IsTopologicalRing (CompletedAway I f) :=
      (I.map (algebraMap C (CompletedAway I f))).nonarchimedean.toIsTopologicalRing
    Continuous ((algebraMap C (CompletedAway I f)).comp φ) ∧
      _root_.RingHom.IsAdic ((algebraMap C (CompletedAway I f)).comp φ) ∧
      TopologicalRing.IsTopologicallyOfFiniteType ((algebraMap C (CompletedAway I f)).comp φ) := by
  let target := CompletedAway I f
  let targetIdeal := I.map (algebraMap C target)
  let : TopologicalSpace target := targetIdeal.adicTopology
  let : IsTopologicalRing target := targetIdeal.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology target target := targetIdeal.isLinearTopology
  obtain ⟨hcont, hadic, hft, -, -⟩ := completedAway_canonical_properties I f hI
  exact ⟨hcont.comp hφ, _root_.RingHom.isAdic_comp φ (algebraMap C target) hφ hcont hP.1 hadic,
    TopologicalRing.isTopologicallyOfFiniteType_comp (algebraMap C target) φ hcont hft hP.2⟩

/-! ### The comparisons on the images of the uncompleted rings -/

/-- `Rig.adicCompletionCongr` on the image of the uncompleted ring. -/
theorem adicCompletionCongr_of {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map e.toRingHom = J) (x : R) :
    adicCompletionCongr e I J h (AdicCompletion.of I R x) = AdicCompletion.of J S (e x) :=
  DFunLike.congr_fun (adicCompletionMap_comp_algebraMap e.toRingHom I J h.le) x

/-- `adicCompletionMap`, read through `RingEquiv.ofBijective`, on the image of the uncompleted
ring. -/
theorem ofBijective_adicCompletionMap_of {R S : Type*} [CommRing R] [CommRing S]
    (F : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map F ≤ J)
    (hbij : Function.Bijective (adicCompletionMap F I J h)) (x : R) :
    RingEquiv.ofBijective (adicCompletionMap F I J h) hbij (AdicCompletion.of I R x) =
      AdicCompletion.of J S (F x) :=
  DFunLike.congr_fun (adicCompletionMap_comp_algebraMap F I J h) x

/-- `Rig.RingHom.completedAwayMap`, read through `RingEquiv.ofBijective`, on the image of the
principal localization. -/
theorem ofBijective_completedAwayMap_of {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (f : A)
    (hbij : Function.Bijective (RingHom.completedAwayMap φ I f)) (w : Localization.Away f) :
    RingEquiv.ofBijective (RingHom.completedAwayMap φ I f) hbij
        (AdicCompletion.of (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f) w) =
      AdicCompletion.of ((I.map φ).map (algebraMap B (Localization.Away (φ f))))
        (Localization.Away (φ f))
        (IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f w) :=
  DFunLike.congr_fun (RingHom.completedAwayMap_comp_algebraMap φ I f) w

/-- **Following a composite of four isomorphisms on a single element.** The second one is used
backwards, so its source is the third one's. -/
theorem ringEquiv_trans_symm_trans_apply {R₁ R₂ R₃ R₄ R₅ : Type*} [NonAssocSemiring R₁]
    [NonAssocSemiring R₂] [NonAssocSemiring R₃] [NonAssocSemiring R₄] [NonAssocSemiring R₅]
    (e₁ : R₁ ≃+* R₂) (e₂ : R₃ ≃+* R₂) (e₃ : R₃ ≃+* R₄) (e₄ : R₄ ≃+* R₅) {x₁ : R₁} {x₂ : R₂}
    {x₃ : R₃} {x₄ : R₄} {x₅ : R₅} (h₁ : e₁ x₁ = x₂) (h₂ : e₂ x₃ = x₂) (h₃ : e₃ x₃ = x₄)
    (h₄ : e₄ x₄ = x₅) :
    e₁.trans (e₂.symm.trans (e₃.trans e₄)) x₁ = x₅ := by
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply, h₁, ← h₂,
    RingEquiv.symm_apply_apply, h₃, h₄]

/-! ### The identification of `(B ⊗̂[A] C)_{\{f\}}` with `B ⊗̂[A] C_{\{f\}}` -/

/-- **`(B ⊗̂[A] C)_{\{f\}} = B ⊗̂[A] C_{\{f\}}`.** The completed principal localization of the
base change at `f ∈ C` is isomorphic to the base change of the completed principal
localization. -/
theorem nonempty_ringEquiv_completedTensorProduct_completedAway {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] (I : Ideal A) (hIadic : IsAdic I)
    (hB : IsAdic (I.map (algebraMap A B))) (hAC : _root_.RingHom.IsAdic (algebraMap A C))
    (hcontAC : Continuous (algebraMap A C))
    (hftAC : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C))
    (J : Ideal C) (hJ : IsAdic J) (f : C) :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
    letI : TopologicalSpace (CompletedAway J f) :=
      (J.map (algebraMap C (CompletedAway J f))).adicTopology
    letI : IsTopologicalRing (CompletedAway J f) :=
      (J.map (algebraMap C (CompletedAway J f))).nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (CompletedAway J f) (CompletedAway J f) :=
      (J.map (algebraMap C (CompletedAway J f))).isLinearTopology
    letI : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
    letI : UniformSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
    letI : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
    letI : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
    Nonempty (UniformSpace.Completion (B ⊗[A] CompletedAway J f) ≃+*
      CompletedAway
        ((J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).map
          (UniformSpace.Completion.coeRingHom : (B ⊗[A] C) →+* UniformSpace.Completion (B ⊗[A] C)))
        (UniformSpace.Completion.coeRingHom
          ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f))) := by
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : IsTopologicalRing (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := C)
  let : IsUniformAddGroup (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  let : TopologicalSpace (CompletedAway J f) :=
    (J.map (algebraMap C (CompletedAway J f))).adicTopology
  let : IsTopologicalRing (CompletedAway J f) :=
    (J.map (algebraMap C (CompletedAway J f))).nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (CompletedAway J f) (CompletedAway J f) :=
    (J.map (algebraMap C (CompletedAway J f))).isLinearTopology
  let : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
  let : UniformSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
  let : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
  let : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
  have hC : IsAdic (I.map (algebraMap A C)) :=
    _root_.RingHom.isAdic_map_of_isAdic (algebraMap A C) hAC hIadic
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  have hLJ : (J.map (algebraMap C (Localization.Away f))).map
      (algebraMap (Localization.Away f) (CompletedAway J f)) =
      J.map (algebraMap C (CompletedAway J f)) := map_map_algebraMap_completedAway J f
  have hAC' : _root_.RingHom.IsAdic (algebraMap A (CompletedAway J f)) :=
    ((completedAway_adicFiniteType_comp (algebraMap A C) hcontAC ⟨hAC, hftAC⟩ J hJ f).2.1)
  have hC'base : IsAdic (I.map (algebraMap A (CompletedAway J f))) :=
    _root_.RingHom.isAdic_map_of_isAdic _ hAC' hIadic
  have hJC' : IsAdic (J.map (algebraMap C (CompletedAway J f))) := rfl
  have hKadic : IsAdic (J.map
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) :=
    isAdic_map_includeRight_of_isAdic I hB hC J hJ
  have hstepA := bijective_completedAwayMap_coe_completion
    (J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)
    (hJfg.map _) hKadic ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f)
  have hstepC := bijective_adicCompletionMap_tensorProduct_map (B := B)
    (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f))
    (J.map (algebraMap C (Localization.Away f)))
    (fun n ↦ bijective_quotientMap_pow_algebraMap_adicCompletion
      (J.map (algebraMap C (Localization.Away f)))
      ((J.map (algebraMap C (Localization.Away f))).fg_of_isNoetherianRing) n)
  have hK'adic : IsAdic (((J.map (algebraMap C (Localization.Away f))).map
      (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f).toRingHom) := by
    rw [show ((J.map (algebraMap C (Localization.Away f))).map
        (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)).toRingHom) =
        J.map (algebraMap C (CompletedAway J f)) from hLJ]
    exact isAdic_map_includeRight_of_isAdic I hB hC'base _ hJC'
  refine ⟨((AdicCompletionBridge.adicCompletionRingEquiv _ hK'adic).trans
    ((RingEquiv.ofBijective _ hstepC).symm.trans
      ((adicCompletionCongr
        (IsLocalization.Away.tensorProductEquivTMulRight A B f
          (Localization.Away f)).toRingEquiv _ _
        (map_tensorProductEquivAway_ideal f J)).trans
        (RingEquiv.ofBijective _ hstepA))))⟩

/-- **`A → C_{\{f\}}` has the properties of `A → C`.** If `A → C` is a continuous, adic
homomorphism of topological finite type between Noetherian adic rings, `J` is an ideal of
definition of `C`, `f : C`, and `C_{\{f\}}` carries the `J`-adic topology, then `C_{\{f\}}` is a
Noetherian adic ring and `A → C_{\{f\}}` is again continuous, adic and topologically of finite
type. -/
theorem completedAway_baseChange_hypotheses {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C] (J : Ideal C)
    (hJ : IsAdic J) (f : C) [TopologicalSpace (CompletedAway J f)]
    [IsTopologicalRing (CompletedAway J f)]
    (hCf : IsAdic (J.map (algebraMap C (CompletedAway J f)))) (φ : A →+* C)
    (hφ : Continuous φ)
    (hP : _root_.RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :
    IsNoetherianRing (CompletedAway J f) ∧ TopologicalRing.IsAdic (CompletedAway J f) ∧
      Continuous ((algebraMap C (CompletedAway J f)).comp φ) ∧
      _root_.RingHom.IsAdic ((algebraMap C (CompletedAway J f)).comp φ) ∧
      TopologicalRing.IsTopologicallyOfFiniteType
        ((algebraMap C (CompletedAway J f)).comp φ) := by
  subst hCf
  exact ⟨(isNoetherianAdic_completedAway J f).1, (isNoetherianAdic_completedAway J f).2,
    completedAway_adicFiniteType_comp φ hφ hP J hJ f⟩

/-! ### The identification followed on the image of `C` -/

/-- **A composite of four comparisons of completions, followed on elements.** Four comparisons
of completions join five rings: the bridge from the uniform to the algebraic completion of `P`
along an ideal of definition `K₁`; the completion of a map `F : Q → P` carrying `K₂` into `K₁`
which is bijective on the completions; the completion of an isomorphism `ε : Q ≅ W[1/x]`
matching `K₂` with the extension of `K` to `W[1/x]`; and the completed principal localization of
a map `ψ : W → V` which is bijective.  Their composite identifies `P^∧` with `V_{\{ψ x\}}`, and
on five families of elements matched by `F`, `ε` and the localization of `ψ` it is the identity.
-/
theorem exists_ringEquiv_completion_adicCompletion_away {ι : Type*} {P Q W V : Type*}
    [CommRing P] [UniformSpace P] [IsTopologicalRing P] [IsUniformAddGroup P] [CommRing Q]
    [CommRing W] [CommRing V] (K₁ : Ideal P) (hK₁ : IsAdic K₁) (K₂ : Ideal Q) (F : Q →+* P)
    (hF : K₂.map F ≤ K₁) (hbijF : Function.Bijective (adicCompletionMap F K₂ K₁ hF))
    (K : Ideal W) (x : W) (ψ : W →+* V) (ε : Q ≃+* Localization.Away x)
    (hε : K₂.map ε.toRingHom = K.map (algebraMap W (Localization.Away x)))
    (hbijψ : Function.Bijective (RingHom.completedAwayMap ψ K x))
    (T : Ideal (Localization.Away (ψ x)))
    (hT : (K.map ψ).map (algebraMap V (Localization.Away (ψ x))) = T)
    (u : ι → P) (v : ι → Q) (w : ι → Localization.Away x)
    (z : ι → Localization.Away (ψ x)) (hu : ∀ i, F (v i) = u i) (hw : ∀ i, ε (v i) = w i)
    (hz : ∀ i, IsLocalization.Away.map (Localization.Away x) (Localization.Away (ψ x)) ψ x
      (w i) = z i) :
    ∃ e : UniformSpace.Completion P ≃+* AdicCompletion T (Localization.Away (ψ x)),
      ∀ i, e ↑(u i) = AdicCompletion.of T (Localization.Away (ψ x)) (z i) := by
  subst hT
  refine ⟨(AdicCompletionBridge.adicCompletionRingEquiv K₁ hK₁).trans
    ((RingEquiv.ofBijective _ hbijF).symm.trans
      ((adicCompletionCongr ε K₂ _ hε).trans (RingEquiv.ofBijective _ hbijψ))), fun i ↦ ?_⟩
  exact ringEquiv_trans_symm_trans_apply _ _ _ _
    (AdicCompletionBridge.adicCompletionRingEquiv_coe K₁ hK₁ (u i))
    ((ofBijective_adicCompletionMap_of F K₂ K₁ hF hbijF (v i)).trans
      (congrArg (AdicCompletion.of K₁ P) (hu i)))
    ((adicCompletionCongr_of ε K₂ _ hε (v i)).trans
      (congrArg (AdicCompletion.of (K.map (algebraMap W (Localization.Away x)))
        (Localization.Away x)) (hw i)))
    ((ofBijective_completedAwayMap_of ψ K x hbijψ (w i)).trans
      (congrArg (AdicCompletion.of ((K.map ψ).map (algebraMap V (Localization.Away (ψ x))))
        (Localization.Away (ψ x))) (hz i)))

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **`(B ⊗̂[A] C)_{\{f\}} = B ⊗̂[A] C_{\{f\}}`, compatibly with the maps from `C`.** For
`C_{\{f\}}` with the `J`-adic topology, there is an isomorphism
`B ⊗̂[A] C_{\{f\}} ≃+* (B ⊗̂[A] C)_{\{f\}}` carrying the image of `c : C` in `B ⊗̂[A] C_{\{f\}}`
to the image of `c` in `(B ⊗̂[A] C)_{\{f\}}`. -/
theorem exists_ringEquiv_completedTensorProduct_completedAway_apply {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] (J : Ideal C) (hJ : IsAdic J) (f : C)
    [TopologicalSpace (CompletedAway J f)]
    [IsTopologicalRing (CompletedAway J f)]
    [IsLinearTopology (CompletedAway J f) (CompletedAway J f)]
    (hCf : IsAdic (J.map (algebraMap C (CompletedAway J f)))) (I : Ideal A) (hIadic : IsAdic I)
    (hB : IsAdic (I.map (algebraMap A B))) (hAC : _root_.RingHom.IsAdic (algebraMap A C))
    (hcontAC : Continuous (algebraMap A C))
    (hftAC : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C))
    :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
    letI : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
    letI : UniformSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
    letI : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
    letI : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
    ∃ e : TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := CompletedAway J f) ≃+*
        CompletedAway
          (J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := C))))
          (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) f),
      ∀ c : C,
        e (algebraMap (CompletedAway J f) (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := CompletedAway J f)) (algebraMap C (CompletedAway J f) c)) =
          algebraMap (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))
            (CompletedAway
              (J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
                (R := A) (M := B) (N := C))))
              (algebraMap C (TopologicalRing.CompletedTensorProduct
                (R := A) (M := B) (N := C)) f))
            (algebraMap C (TopologicalRing.CompletedTensorProduct
              (R := A) (M := B) (N := C)) c) := by
  subst hCf
  let : TopologicalSpace (CompletedAway J f) :=
    (J.map (algebraMap C (CompletedAway J f))).adicTopology
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : IsTopologicalRing (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := C)
  let : IsUniformAddGroup (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  let : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
  let : UniformSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
  let : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
  let : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
  have hC : IsAdic (I.map (algebraMap A C)) :=
    _root_.RingHom.isAdic_map_of_isAdic (algebraMap A C) hAC hIadic
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  have hLJ : (J.map (algebraMap C (Localization.Away f))).map
      (algebraMap (Localization.Away f) (CompletedAway J f)) =
      J.map (algebraMap C (CompletedAway J f)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq C (Localization.Away f) (CompletedAway J f)]
  have hAC' : _root_.RingHom.IsAdic (algebraMap A (CompletedAway J f)) :=
    ((completedAway_adicFiniteType_comp (algebraMap A C) hcontAC ⟨hAC, hftAC⟩ J hJ f).2.1)
  have hC'base : IsAdic (I.map (algebraMap A (CompletedAway J f))) :=
    _root_.RingHom.isAdic_map_of_isAdic _ hAC' hIadic
  have hJC' : IsAdic (J.map (algebraMap C (CompletedAway J f))) := rfl
  have hKadic : IsAdic (J.map
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) :=
    isAdic_map_includeRight_of_isAdic I hB hC J hJ
  have hstepA := bijective_completedAwayMap_coe_completion
    (J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)
    (hJfg.map _) hKadic ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f)
  have hstepC := bijective_adicCompletionMap_tensorProduct_map (B := B)
    (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f))
    (J.map (algebraMap C (Localization.Away f)))
    (fun n ↦ bijective_quotientMap_pow_algebraMap_adicCompletion
      (J.map (algebraMap C (Localization.Away f)))
      ((J.map (algebraMap C (Localization.Away f))).fg_of_isNoetherianRing) n)
  have hK'adic : IsAdic (((J.map (algebraMap C (Localization.Away f))).map
      (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f).toRingHom) := by
    rw [show ((J.map (algebraMap C (Localization.Away f))).map
        (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)).toRingHom) =
        J.map (algebraMap C (CompletedAway J f)) from hLJ]
    exact isAdic_map_includeRight_of_isAdic I hB hC'base _ hJC'
  have hmapφ : (J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).map
      (UniformSpace.Completion.coeRingHom : (B ⊗[A] C) →+*
        TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) =
      J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
        (R := A) (M := B) (N := C))) := by
    rw [Ideal.map_map]
    exact congrArg J.map (RingHom.ext fun c ↦ rfl)
  have hu (c : C) :
      (Algebra.TensorProduct.map (AlgHom.id A B)
          (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f))).toRingHom
        ((Algebra.TensorProduct.includeRight :
          Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f)
          (algebraMap C (Localization.Away f) c)) =
      (Algebra.TensorProduct.includeRight :
        CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f)
        (algebraMap C (CompletedAway J f) c) := by
    have h := DFunLike.congr_fun (tensorProduct_map_comp_includeRight (B := B)
      (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)))
      (algebraMap C (Localization.Away f) c)
    refine h.trans (congrArg (Algebra.TensorProduct.includeRight :
      CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f) ?_)
    exact (IsScalarTower.algebraMap_apply C (Localization.Away f) (CompletedAway J f) c).symm
  have hw (c : C) :
      (IsLocalization.Away.tensorProductEquivTMulRight A B f
          (Localization.Away f)).toRingEquiv
        ((Algebra.TensorProduct.includeRight :
          Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f)
          (algebraMap C (Localization.Away f) c)) =
      algebraMap (B ⊗[A] C)
        (Localization.Away ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f))
        ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c) := by
    have h1 : (Algebra.TensorProduct.map (AlgHom.id A B)
          (IsScalarTower.toAlgHom A C (Localization.Away f)))
          ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c) =
        (Algebra.TensorProduct.includeRight :
          Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f)
          (algebraMap C (Localization.Away f) c) :=
      DFunLike.congr_fun (tensorProduct_map_comp_includeRight (B := B)
        (IsScalarTower.toAlgHom A C (Localization.Away f))) c
    exact (congrArg (IsLocalization.Away.tensorProductEquivTMulRight A B f
      (Localization.Away f)).toRingEquiv h1.symm).trans
      (DFunLike.congr_fun (tensorProductEquivAway_comp_map (A := A) (B := B) f)
        ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c))
  refine exists_ringEquiv_completion_adicCompletion_away (ι := C)
    (K₁ := ((J.map (algebraMap C (Localization.Away f))).map
      (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f)).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f).toRingHom)
    (hK₁ := hK'adic)
    (K₂ := (J.map (algebraMap C (Localization.Away f))).map
      (Algebra.TensorProduct.includeRight :
        Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f).toRingHom)
    (F := (Algebra.TensorProduct.map (AlgHom.id A B)
      (IsScalarTower.toAlgHom A (Localization.Away f) (CompletedAway J f))).toRingHom)
    (hF := le_of_eq (tensorProduct_map_map_ideal _ _)) (hbijF := hstepC)
    (K := J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)
    (x := (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f)
    (ψ := UniformSpace.Completion.coeRingHom)
    (ε := (IsLocalization.Away.tensorProductEquivTMulRight A B f
      (Localization.Away f)).toRingEquiv)
    (hε := map_tensorProductEquivAway_ideal f J) (hbijψ := hstepA)
    (hT := congrArg (Ideal.map (algebraMap
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))
      (Localization.Away (algebraMap C (TopologicalRing.CompletedTensorProduct
        (R := A) (M := B) (N := C)) f)))) hmapφ)
    (u := fun c ↦ (Algebra.TensorProduct.includeRight :
      CompletedAway J f →ₐ[A] B ⊗[A] CompletedAway J f)
      (algebraMap C (CompletedAway J f) c))
    (v := fun c ↦ (Algebra.TensorProduct.includeRight :
      Localization.Away f →ₐ[A] B ⊗[A] Localization.Away f)
      (algebraMap C (Localization.Away f) c))
    (w := fun c ↦ algebraMap (B ⊗[A] C)
      (Localization.Away ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) f))
      ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c))
    (z := fun c ↦ algebraMap (TopologicalRing.CompletedTensorProduct
      (R := A) (M := B) (N := C))
      (Localization.Away (algebraMap C (TopologicalRing.CompletedTensorProduct
        (R := A) (M := B) (N := C)) f))
      (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) c))
    (hu := hu) (hw := hw)
    (hz := fun _ ↦ IsLocalization.map_eq _ _)

/-! ### The compatibility over `C_{\{f\}}` -/

/-- **The identification is compatible with the two arrows out of `C_{\{f\}}`.** For
`C_{\{f\}}` with the `J`-adic topology, there is an isomorphism
`B ⊗̂[A] C_{\{f\}} ≃+* (B ⊗̂[A] C)_{\{f\}}` under which the base-change arrow
`C_{\{f\}} → B ⊗̂[A] C_{\{f\}}` is the map `C_{\{f\}} → (B ⊗̂[A] C)_{\{f\}}` induced by
`C → B ⊗̂[A] C`. -/
theorem exists_ringEquiv_comp_algebraMap_eq_completedAwayMap {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] (J : Ideal C) (hJ : IsAdic J) (f : C)
    [TopologicalSpace (CompletedAway J f)] [IsTopologicalRing (CompletedAway J f)]
    [IsLinearTopology (CompletedAway J f) (CompletedAway J f)]
    (hCf : IsAdic (J.map (algebraMap C (CompletedAway J f)))) (I : Ideal A) (hIadic : IsAdic I)
    (hB : IsAdic (I.map (algebraMap A B))) (hAC : _root_.RingHom.IsAdic (algebraMap A C))
    (hcontAC : Continuous (algebraMap A C))
    (hftAC : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C)) :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
    letI : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
    letI : UniformSpace (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
    letI : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
    letI : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
      TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
    ∃ e : TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := CompletedAway J f) ≃+*
        CompletedAway
          (J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := C))))
          (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) f),
      e.toRingHom.comp (algebraMap (CompletedAway J f)
          (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := CompletedAway J f))) =
        RingHom.completedAwayMap
          (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)))
          J f := by
  subst hCf
  let : TopologicalSpace (CompletedAway J f) :=
    (J.map (algebraMap C (CompletedAway J f))).adicTopology
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : TopologicalSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := CompletedAway J f)
  let : UniformSpace (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := CompletedAway J f)
  let : IsTopologicalRing (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isTopologicalRing (R := A) (A := B) (B := CompletedAway J f)
  let : IsUniformAddGroup (B ⊗[A] CompletedAway J f) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := CompletedAway J f)
  obtain ⟨e, he⟩ := exists_ringEquiv_completedTensorProduct_completedAway_apply J hJ f rfl I
    hIadic hB hAC hcontAC hftAC
  refine ⟨e, ?_⟩
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  let : TopologicalSpace (CompletedAway (J.map (algebraMap C
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))))
      (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) f)) :=
    (((J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
      (R := A) (M := B) (N := C)))).map
      (algebraMap (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))
        (Localization.Away (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C)) f)))).map
      (algebraMap (Localization.Away (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C)) f))
        (CompletedAway (J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C))))
          (algebraMap C (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := C)) f)))).adicTopology
  have hTadic := isAdic_adicCompletion
    ((J.map (algebraMap C (TopologicalRing.CompletedTensorProduct
      (R := A) (M := B) (N := C)))).map
      (algebraMap (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))
        (Localization.Away (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C)) f))))
    ((hJfg.map _).map _)
  let : T2Space (CompletedAway (J.map (algebraMap C
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))))
      (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) f)) :=
    hTadic.2.1
  have hbase : (e.toRingHom.comp (algebraMap (CompletedAway J f)
        (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := CompletedAway J f)))).comp
        (algebraMap C (CompletedAway J f)) =
      (RingHom.completedAwayMap (algebraMap C (TopologicalRing.CompletedTensorProduct
        (R := A) (M := B) (N := C))) J f).comp (algebraMap C (CompletedAway J f)) :=
    RingHom.ext fun c ↦ (he c).trans (DFunLike.congr_fun
      (RingHom.completedAwayMap_comp_base (algebraMap C
        (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) J f) c).symm
  have hcont : ∀ g : CompletedAway J f →+* CompletedAway (J.map (algebraMap C
        (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))))
        (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C)) f),
      g.comp (algebraMap C (CompletedAway J f)) =
        (RingHom.completedAwayMap (algebraMap C (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C))) J f).comp (algebraMap C (CompletedAway J f)) →
      Continuous g := by
    intro g hg
    refine continuous_adic_of_map_le (J.map (algebraMap C (CompletedAway J f))) _ g
      (le_of_eq ?_)
    calc (J.map (algebraMap C (CompletedAway J f))).map g
        = J.map (g.comp (algebraMap C (CompletedAway J f))) := Ideal.map_map _ _
      _ = J.map ((RingHom.completedAwayMap (algebraMap C
          (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) J f).comp
          (algebraMap C (CompletedAway J f))) := by rw [hg]
      _ = J.map ((algebraMap (TopologicalRing.CompletedTensorProduct
          (R := A) (M := B) (N := C)) _).comp (algebraMap C
          (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)))) := by
            rw [RingHom.completedAwayMap_comp_base]
      _ = _ := ((map_map_algebraMap_completedAway (J.map (algebraMap C
          (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))))
          (algebraMap C (TopologicalRing.CompletedTensorProduct
            (R := A) (M := B) (N := C)) f)).trans (Ideal.map_map _ _)).symm
  exact completedHom_ext f (completedAway_canonical_properties J f hJ).2.2.2.2 _ _
    (hcont _ hbase) (hcont _ rfl) hbase

end BaseChange

end Rig

end
