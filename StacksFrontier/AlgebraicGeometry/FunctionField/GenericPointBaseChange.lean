module

public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatAtPullbackMap
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.RingTheory.Localization.AtPrimeNilradical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The function field of a base change of a geometrically irreducible scheme

Let `K → Ω` be an extension of fields and let `W` be an integral scheme over `K` which is
geometrically irreducible, so that `W_Ω = W ×_K Spec Ω` is irreducible. The residue field of
`W_Ω` at its generic point — the function field of `(W_Ω)_red` — depends only on the function
field `K(W)` as a `K`-algebra: the local ring of `W_Ω` at its generic point is the localization of
`K(W) ⊗_K Ω` at a prime, that local ring has dimension zero, and `K(W) ⊗_K Ω` has a single
minimal prime because `K(W)` is geometrically irreducible over `K` ([Stacks, Tag 054Q]); so the
prime is the nilradical and the residue field is that of `K(W) ⊗_K Ω` at its nilradical.

Consequently two integral geometrically irreducible `K`-schemes with `K`-isomorphic function
fields have `Ω`-isomorphic residue fields at the generic points of their base changes to `Ω`.

## Main results

* `AlgebraicGeometry.krullDimLE_zero_stalk_genericPoint`: the local ring at the generic point of
  an irreducible scheme has dimension zero.
* `AlgebraicGeometry.stalkSpecFieldAlgEquiv`: the local ring of `Spec Ω` is `Ω`.
* `AlgebraicGeometry.exists_tensorProduct_presentation_stalk_genericPoint`: the local ring of
  `W_Ω` at its generic point is a localization of `K(W) ⊗_K 𝒪_{Spec Ω}` at a prime.
* `AlgebraicGeometry.isPrime_nilradical_stalk_tensorProduct`: that tensor product has prime
  nilradical.
* `AlgebraicGeometry.exists_residueField_genericPoint_ringEquiv`: a `K`-isomorphism of function
  fields induces an isomorphism, over `Ω`, of the residue fields at the generic points of the base
  changes to `Ω`.
* `AlgebraicGeometry.exists_residueField_ringEquiv_of_surjective_stalkMap`: a morphism over a
  base which is surjective on a local ring induces an isomorphism of residue fields compatible
  with the global functions of the base.

## Implementation notes

The `K`-algebra structures on local rings are `AlgebraicGeometry.stalkAlgebraOver`, the ones in
which `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct` is stated.
Compatibility with `Ω` is expressed through `Ω ⟶ Γ(W_Ω, ⊤)` followed by evaluation at the generic
point, so that it is the algebra structure on the residue field used by
`AlgebraicGeometry.geometricallyIrreducible_tfae_functionField`.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The local ring of an irreducible scheme at its generic point has Krull dimension zero: no
point generalizes the generic point strictly. -/
theorem krullDimLE_zero_stalk_genericPoint (T : Scheme.{u}) [IrreducibleSpace T] :
    Ring.KrullDimLE 0 (T.presheaf.stalk (genericPoint T)) := by
  refine krullDimLE_of_coheight_le (Order.coheight_eq_zero.mpr fun b _ => ?_).le
  exact (genericPoint_spec T).specializes trivial

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- The local ring of the spectrum of a field `Ω` at its point is `Ω` itself, as a `K`-algebra
for any field `K` below `Ω`. -/
def stalkSpecFieldAlgEquiv (y : Spec (.of Ω)) :
    letI := stalkAlgebraOver K (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y
    Ω ≃ₐ[K] (Spec (.of Ω)).presheaf.stalk y :=
  letI := stalkAlgebraOver K (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective
    ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (Spec (.of Ω)).presheaf.germ ⊤ y trivial).hom
    ⟨RingHom.injective _, fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)⟩)
    fun a => by
      have h : CommRingCat.ofHom (algebraMap K Ω) ≫ (Scheme.ΓSpecIso (.of Ω)).inv ≫
          (Spec (.of Ω)).presheaf.germ ⊤ y trivial = (Scheme.ΓSpecIso (.of K)).inv ≫
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω))).appTop ≫
              (Spec (.of Ω)).presheaf.germ ⊤ y trivial := by
        rw [← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
      exact congrArg (fun φ => φ.hom a) h

/-- Evaluating at `x` the pullback of a global function along `f` is evaluating its germ at
`f x`, carried along the map on local rings. -/
theorem Γevaluation_appTop_eq_residue_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (a : Γ(Y, ⊤)) :
    X.Γevaluation x (f.appTop a) =
      X.residue x (f.stalkMap x (Y.presheaf.germ ⊤ (f x) trivial a)) :=
  (congrArg (X.residue x).hom (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial a)).symm

/-- The base change of a geometrically irreducible scheme along a field extension is
irreducible. -/
instance irreducibleSpace_pullback_specMap_algebraMap {W : Scheme.{u}}
    (s : W ⟶ Spec (.of K)) [GeometricallyIrreducible s] :
    IrreducibleSpace (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}) :=
  pullback_of_geometrically ‹GeometricallyIrreducible s›.geometrically_irreducibleSpace Ω _

/-- The local ring of `W_Ω` at its generic point is the localization of `K(W) ⊗_K 𝒪_{Spec Ω, y}`
at the prime under its maximal ideal, `y` being the image of the generic point, through a map
restricting on the second factor to the map on local rings of the projection to `Spec Ω`. -/
@[ega "IV 4.2.4" "(ii), special case"]
theorem exists_tensorProduct_presentation_stalk_genericPoint {W : Scheme.{u}}
    (s : W ⟶ Spec (.of K)) [IsIntegral W] [GeometricallyIrreducible s] :
    letI := stalkAlgebraOver K s (genericPoint W)
    letI := stalkAlgebraOver K (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
        (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u})))
    ∃ ψ : W.presheaf.stalk (genericPoint W) ⊗[K] (Spec (.of Ω)).presheaf.stalk
        (pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
            Scheme.{u}))) →+*
        (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).presheaf.stalk
          (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
            Scheme.{u})),
      (∀ b, ψ (1 ⊗ₜ b) = ((pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).stalkMap
          (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
            Scheme.{u}))).hom b) ∧
      (letI := ψ.toAlgebra; IsLocalization.AtPrime
        ((pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).presheaf.stalk
          (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
            Scheme.{u}))) (Ideal.comap ψ (maximalIdeal _))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  set ξ := genericPoint (pullback s g : Scheme.{u})
  have hx : pullback.fst s g ξ = genericPoint W := map_genericPoint_of_isDominant _
  obtain ⟨ψ₀, -, h₂, hloc₀⟩ := exists_isLocalization_atPrime_stalk_pullback_tensorProduct K s g ξ
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensor_stalk_transport₂ K s g _ _ _ _ hx rfl ψ₀ hloc₀
  refine ⟨ψ, fun b => ?_, hloc⟩
  rw [hψ, map_one, map_one, one_mul, stalkCongr_hom_self, ← h₂]
  rfl

/-- For `W` integral and geometrically irreducible over `K`, the ring `K(W) ⊗_K 𝒪_{Spec Ω, y}` has
prime nilradical: by [Stacks, Tag 054Q] its function field is geometrically irreducible over
`K`, and `𝒪_{Spec Ω, y}` is the field `Ω`. -/
theorem isPrime_nilradical_stalk_tensorProduct {W : Scheme.{u}}
    (s : W ⟶ Spec (.of K)) [IsIntegral W] [GeometricallyIrreducible s] (y : Spec (.of Ω)) :
    letI := stalkAlgebraOver K s (genericPoint W)
    letI := stalkAlgebraOver K (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y
    (nilradical (W.presheaf.stalk (genericPoint W) ⊗[K]
      (Spec (.of Ω)).presheaf.stalk y)).IsPrime := by
  let := stalkAlgebraOver K s (genericPoint W)
  let := stalkAlgebraOver K (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y
  let : Algebra K (W.residueField (genericPoint W)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop ≫ W.Γevaluation (genericPoint W)).hom.toAlgebra
  have hgi : Algebra.IsGeometricallyIrreducible K (W.residueField (genericPoint W)) :=
    ((geometricallyIrreducible_tfae_functionField K W s (genericPoint W)
      (genericPoint_spec W)).out 1 2).mp ‹_›
  have hirr := (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
    K _).mp hgi Ω
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hirr
  let ε : W.presheaf.stalk (genericPoint W) ≃ₐ[K] W.residueField (genericPoint W) :=
    AlgEquiv.ofRingEquiv (f := genericResidueEquiv W) fun _ => rfl
  let ρ := (Algebra.TensorProduct.congr ε (stalkSpecFieldAlgEquiv K Ω y).symm).toRingEquiv
  have hcomap : Ideal.comap ρ.toRingHom (nilradical _) = nilradical _ := by
    ext x
    simp only [Ideal.mem_comap, mem_nilradical, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact ⟨fun h => by simpa using h.map ρ.symm.toRingHom, fun h => h.map ρ.toRingHom⟩
  exact hcomap ▸ Ideal.comap_isPrime ρ.toRingHom _

/-- **The function field of a base change depends only on the function field.** Let `W`, `W'` be
integral geometrically irreducible schemes over a field `K` and `Ω/K` a field extension. A
`K`-algebra isomorphism `K(W) ≃ K(W')` induces an isomorphism of the residue fields of `W_Ω` and
`W'_Ω` at their generic points which is compatible with the two maps from `Ω`. -/
theorem exists_residueField_genericPoint_ringEquiv {W W' : Scheme.{u}}
    (s : W ⟶ Spec (.of K)) (s' : W' ⟶ Spec (.of K)) [IsIntegral W] [IsIntegral W']
    [GeometricallyIrreducible s] [GeometricallyIrreducible s']
    (e : letI := stalkAlgebraOver K s (genericPoint W)
      letI := stalkAlgebraOver K s' (genericPoint W')
      W.presheaf.stalk (genericPoint W) ≃ₐ[K] W'.presheaf.stalk (genericPoint W')) :
    ∃ Φ : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).residueField
        (genericPoint (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u})) ≃+*
      (pullback s' (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}).residueField
        (genericPoint (pullback s' (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u})),
      ∀ ω : Ω, Φ (Scheme.Γevaluation _ _
          ((pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv ω))) =
        Scheme.Γevaluation _ _
          ((pullback.snd s' (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv ω)) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  set ξ := genericPoint (pullback s g : Scheme.{u})
  set ξ' := genericPoint (pullback s' g : Scheme.{u})
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensorProduct_presentation_stalk_genericPoint K Ω s
  obtain ⟨ψ', hψ', hloc'⟩ := exists_tensorProduct_presentation_stalk_genericPoint K Ω s'
  have := krullDimLE_zero_stalk_genericPoint (pullback s g : Scheme.{u})
  have := krullDimLE_zero_stalk_genericPoint (pullback s' g : Scheme.{u})
  let := stalkAlgebraOver K s (genericPoint W)
  let := stalkAlgebraOver K s' (genericPoint W')
  let := stalkAlgebraOver K g (pullback.snd s g ξ)
  let := stalkAlgebraOver K g (pullback.snd s' g ξ')
  let τ := (stalkSpecFieldAlgEquiv K Ω (pullback.snd s g ξ)).symm.trans
    (stalkSpecFieldAlgEquiv K Ω (pullback.snd s' g ξ'))
  let θ := (Algebra.TensorProduct.congr e τ).toRingEquiv
  obtain ⟨Φ, hΦ⟩ := IsLocalization.AtPrime.exists_residueField_ringEquiv_of_ringEquiv ψ ψ'
    hloc hloc' (isPrime_nilradical_stalk_tensorProduct K Ω s _) θ
  refine ⟨Φ, fun ω => ?_⟩
  rw [Γevaluation_appTop_eq_residue_stalkMap, Γevaluation_appTop_eq_residue_stalkMap]
  have h1 : ((pullback.snd s g).stalkMap ξ).hom ((Spec (.of Ω)).presheaf.germ ⊤
      (pullback.snd s g ξ) trivial ((Scheme.ΓSpecIso (.of Ω)).inv.hom ω)) =
      ψ (1 ⊗ₜ stalkSpecFieldAlgEquiv K Ω (pullback.snd s g ξ) ω) := by
    rw [hψ]
    rfl
  have h1' : ((pullback.snd s' g).stalkMap ξ').hom ((Spec (.of Ω)).presheaf.germ ⊤
      (pullback.snd s' g ξ') trivial ((Scheme.ΓSpecIso (.of Ω)).inv.hom ω)) =
      ψ' (1 ⊗ₜ stalkSpecFieldAlgEquiv K Ω (pullback.snd s' g ξ') ω) := by
    rw [hψ']
    rfl
  rw [h1, h1']
  refine (hΦ _).trans ?_
  simp [θ, τ]
  rfl

/-- A morphism `h : T ⟶ T'` over a scheme `S` which is surjective on the local ring at `x`
induces an isomorphism of residue fields `κ(h x) ≃ κ(x)` compatible with the global functions
of `S`. -/
theorem exists_residueField_ringEquiv_of_surjective_stalkMap {T T' S : Scheme.{u}}
    (t : T ⟶ S) (t' : T' ⟶ S) (h : T ⟶ T') (hh : h ≫ t' = t) (x : T) (x' : T')
    (hx : h x = x') (hsurj : Function.Surjective (h.stalkMap x).hom) :
    ∃ Φ : T'.residueField x' ≃+* T.residueField x,
      ∀ a : Γ(S, ⊤), Φ (T'.Γevaluation x' (t'.appTop a)) = T.Γevaluation x (t.appTop a) := by
  subst hx hh
  have hs : Function.Surjective (h.residueFieldMap x).hom := by
    intro y
    obtain ⟨z, rfl⟩ := T.residue_surjective x y
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨T'.residue (h x) w, by
      rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have hb : Function.Bijective (h.residueFieldMap x).hom := ⟨RingHom.injective _, hs⟩
  refine ⟨RingEquiv.ofBijective (h.residueFieldMap x).hom hb, fun a => ?_⟩
  rw [RingEquiv.ofBijective_apply, Scheme.Γevaluation_naturality_apply, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

end AlgebraicGeometry

end
