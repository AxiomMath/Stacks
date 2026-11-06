module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProduct
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# `X = X_{k'}/G` for a finite Galois extension `k'/k`

Let `k'/k` be an extension of fields, both contained in a big fppf site, and let `X` be a
presheaf on the big fppf site of `Spec k`. The base change `X_{k'} = X ×_{Spec k} Spec k'`,
viewed over `Spec k`, is the product `h_{Spec k'} ⨯ X`; the group `k' ≃ₐ[k] k'` of
`k`-automorphisms of `k'` acts on it through the first factor, and the projection to `X` is
invariant. The action is free, and when `k'/k` is finite Galois the induced map from the
quotient sheaf to `X` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.specExtension` is `Spec k'` as an object of the big fppf site of
  `Spec k`, and `AlgebraicGeometry.Space.specExtensionAut` is the automorphism it carries for
  each `k`-automorphism of `k'`.
* `AlgebraicGeometry.Space.extensionBaseChange` is `X_{k'}`, with
  `AlgebraicGeometry.Space.extensionBaseChangeAut` the induced action and
  `AlgebraicGeometry.Space.extensionBaseChangeProj` the projection to `X`.
* `AlgebraicGeometry.Space.extensionBaseChangeQuotient` is the quotient of `X_{k'}` by that
  action, and `AlgebraicGeometry.Space.extensionBaseChangeQuotientLift` the canonical map
  from it to `X`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_extensionBaseChange`: **Stacks 0B86**, `X_{k'}` is
  an algebraic space over `k` whenever `X` is.
* `AlgebraicGeometry.Space.isFreeOnNonemptyPoints_extensionBaseChange`: **Stacks 0B86**, the
  automorphism group of `k'` over `k` acts freely on `X_{k'}`.
* `AlgebraicGeometry.Space.isIso_extensionBaseChangeQuotientLift`: **Stacks 0B86**, for a
  finite Galois extension the comparison map `X_{k'}/G ⟶ X` is an isomorphism, that is
  `X = X_{k'}/G`.

## Implementation notes

`X_{k'}` is taken *over* `Spec k`, which is where the action and the quotient live: it is the
product `h_{Spec k'} ⨯ X` of presheaves on the big fppf site of `Spec k`. That it is an
algebraic space is `AlgebraicGeometry.isAlgebraicSpace_restrict_iff_product` (Stacks 04SH)
applied to the restriction of `X` to the site over `Spec k'`, which is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict` (Stacks 03I5, part (1)).

A `k`-automorphism `g` of `k'` acts through `Spec (g⁻¹)`: `Spec` is contravariant, so the
inverse is what turns the group law into a *left* action by post-composition on the functor of
points. The action on `X_{k'}` is this action on the first factor and the identity on `X`, so
the projection to `X` is invariant and the comparison map is
`AlgebraicGeometry.Space.orbitQuotientLift` applied to it.

Freeness is taken in the form `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`: the action is
cancellative on the points over the test objects whose underlying scheme is nonempty. This is
the only satisfiable form of the condition for a nontrivial group — over a test object with
empty underlying scheme a sheaf is terminal, so by
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton` asking cancellativity there
would force the group to be trivial. It is exactly what the geometry supplies: a point of
`X_{k'}` over a nonempty test object `T` has a first component `T ⟶ Spec k'`, which is a ring
map `k' → Γ(T, ⊤)` into a nonzero ring and hence injective, so two automorphisms acting alike
on it agree. Freeness therefore needs neither finiteness nor normality of `k'/k`, and is
stated for an arbitrary extension; the identification of `X` with the quotient is where the
extension must be finite Galois.

The quotient is identified with `X` by showing that the comparison map out of the presheaf of
pointwise orbits is locally bijective. Local surjectivity is the base change of a test object
along the fppf covering `Spec k' ⟶ Spec k`. Local injectivity is where the extension must be
Galois: two points of `X_{k'}` with the same image in `X` differ by a point of
`Spec k' ×_{Spec k} Spec k'`, which for a finite Galois extension is the disjoint union of one
copy of `Spec k'` for each element of the Galois group, by the normal basis theorem in the form
`k' ⊗[k] k' ≅ ∏_{g ∈ G} k'`.

## References

* [Stacks Project, Tag 0B86](https://stacks.math.columbia.edu/tag/0B86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry.Space

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))

/-! ### `Spec k'` over `Spec k` and its automorphisms -/

/-- The morphism `Spec k' ⟶ Spec k` of a big fppf site containing both. -/
def specExtensionHom : B.obj hk' ⟶ B.obj hk :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- `Spec k'`, viewed as an object of the big fppf site of `Spec k`. -/
def specExtension : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (specExtensionHom k k' B hk hk')

/-- The automorphism `Spec (g⁻¹)` of `Spec k'` over `Spec k` attached to a `k`-automorphism
`g` of `k'`.  The inverse appears because `Spec` is contravariant, so that `g ↦ Spec (g⁻¹)`
is a left action. -/
def specExtensionAut (g : k' ≃ₐ[k] k') :
    specExtension k k' B hk hk' ⟶ specExtension k k' B hk hk' :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (g⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom)))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (g⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k k')) =
        Spec.map (CommRingCat.ofHom (algebraMap k k'))
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x => (g⁻¹ : k' ≃ₐ[k] k').commutes x))

/-- The identity automorphism of `k'` acts as the identity of `Spec k'`. -/
@[simp]
theorem specExtensionAut_one : specExtensionAut k k' B hk hk' 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom ((1 : k' ≃ₐ[k] k')⁻¹).toAlgHom.toRingHom) = _
  rw [inv_one]
  change Spec.map (CommRingCat.ofHom (RingHom.id k')) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- The automorphisms of `Spec k'` attached to a product, in the order of a left action. -/
@[simp]
theorem specExtensionAut_mul (g h : k' ≃ₐ[k] k') :
    specExtensionAut k k' B hk hk' (g * h) =
      specExtensionAut k k' B hk hk' h ≫ specExtensionAut k k' B hk hk' g := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom ((g * h)⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (h⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (g⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom)
  rw [← Spec.map_comp]
  congr 1

/-- The automorphism of `Spec k'` attached to `g` is `Spec (g⁻¹)` on underlying schemes. -/
@[simp]
theorem specExtensionAut_left_hom (g : k' ≃ₐ[k] k') :
    (specExtensionAut k k' B hk hk' g).left.hom =
      Spec.map (CommRingCat.ofHom (g⁻¹ : k' ≃ₐ[k] k').toAlgHom.toRingHom) :=
  rfl

/-! ### The base change and its action -/

variable (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- `X_{k'} = X ×_{Spec k} Spec k'`, viewed as a presheaf on the big fppf site of `Spec k`. -/
abbrev extensionBaseChange : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u :=
  yoneda.obj (specExtension k k' B hk hk') ⨯ X

/-- **Stacks 0B86**, the algebraicity of the base change: the base change of an algebraic space
over `k` along a field extension `k'/k` is, viewed over `k`, an algebraic space. -/
@[stacks 0B86 "the base change is an algebraic space"]
theorem isAlgebraicSpace_extensionBaseChange
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsAlgebraicSpace B (Spec (.of k)) hk (extensionBaseChange k k' B hk hk' X) :=
  (isAlgebraicSpace_restrict_iff_product B (Spec (.of k')) (Spec (.of k)) hk' hk
      (specExtensionHom k k' B hk hk') X).1
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
      (specExtensionHom k k' B hk hk') X hX)

/-- The automorphism of `X_{k'}` given by a `k`-automorphism of `k'` acting on the factor
`Spec k'`. -/
def extensionBaseChangeAut (g : k' ≃ₐ[k] k') :
    extensionBaseChange k k' B hk hk' X ⟶ extensionBaseChange k k' B hk hk' X :=
  prod.map (yoneda.map (specExtensionAut k k' B hk hk' g)) (𝟙 X)

/-- The identity automorphism of `k'` acts as the identity of `X_{k'}`. -/
@[simp]
theorem extensionBaseChangeAut_one : extensionBaseChangeAut k k' B hk hk' X 1 = 𝟙 _ := by
  simp [extensionBaseChangeAut]

/-- The automorphisms of `X_{k'}` attached to a product, in the order of a left action. -/
@[simp]
theorem extensionBaseChangeAut_mul (g h : k' ≃ₐ[k] k') :
    extensionBaseChangeAut k k' B hk hk' X (g * h) =
      extensionBaseChangeAut k k' B hk hk' X h ≫ extensionBaseChangeAut k k' B hk hk' X g := by
  simp [extensionBaseChangeAut]

/-- The action of the `k`-automorphisms of `k'` on the points of `X_{k'}` over a test
object. -/
@[sga "7 XIII 1.1.1" "partial"]
instance mulAction_extensionBaseChange (T : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ) :
    MulAction (k' ≃ₐ[k] k') ((extensionBaseChange k k' B hk hk' X).obj T) where
  smul g x := (extensionBaseChangeAut k k' B hk hk' X g).app T x
  one_smul x := by
    change (extensionBaseChangeAut k k' B hk hk' X 1).app T x = x
    rw [extensionBaseChangeAut_one]
    rfl
  mul_smul g h x := by
    change (extensionBaseChangeAut k k' B hk hk' X (g * h)).app T x =
      (extensionBaseChangeAut k k' B hk hk' X g).app T
        ((extensionBaseChangeAut k k' B hk hk' X h).app T x)
    rw [extensionBaseChangeAut_mul]
    rfl

/-- The action on `X_{k'}` is natural in the test object. -/
theorem isNaturalAction_extensionBaseChange :
    IsNaturalAction B (Spec (.of k)) hk (k' ≃ₐ[k] k')
      (extensionBaseChange k k' B hk hk' X) := fun f g x =>
  (NatTrans.naturality_apply (extensionBaseChangeAut k k' B hk hk' X g) f x).symm

/-- The projection `X_{k'} ⟶ X`. -/
def extensionBaseChangeProj : extensionBaseChange k k' B hk hk' X ⟶ X := prod.snd

/-- The projection `X_{k'} ⟶ X` is invariant under the action. -/
theorem extensionBaseChangeProj_smul
    (T : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ) (g : k' ≃ₐ[k] k')
    (x : (extensionBaseChange k k' B hk hk' X).obj T) :
    (extensionBaseChangeProj k k' B hk hk' X).app T (g • x) =
      (extensionBaseChangeProj k k' B hk hk' X).app T x := by
  have h : extensionBaseChangeAut k k' B hk hk' X g ≫ extensionBaseChangeProj k k' B hk hk' X =
      extensionBaseChangeProj k k' B hk hk' X := by
    simp [extensionBaseChangeAut, extensionBaseChangeProj]
  exact congrArg (fun α : extensionBaseChange k k' B hk hk' X ⟶ X => α.app T x) h

private lemma extensionBaseChange_fst_smul
    (T : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ)
    (g : k' ≃ₐ[k] k') (x : (extensionBaseChange k k' B hk hk' X).obj T) :
    (prod.fst : extensionBaseChange k k' B hk hk' X ⟶
      yoneda.obj (specExtension k k' B hk hk')).app T (g • x) =
    (prod.fst : extensionBaseChange k k' B hk hk' X ⟶
      yoneda.obj (specExtension k k' B hk hk')).app T x ≫
      specExtensionAut k k' B hk hk' g :=
  congrArg (fun α : extensionBaseChange k k' B hk hk' X ⟶
      yoneda.obj (specExtension k k' B hk hk') => α.app T x)
    (prod.map_fst (yoneda.map (specExtensionAut k k' B hk hk' g)) (𝟙 X))

/-! ### Freeness of the action -/

/-- Two `k`-automorphisms of `k'` whose spectra agree after composition with a morphism from a
nonempty scheme to `Spec k'` are equal: such a morphism is a ring map from `k'` to a nonzero
ring, hence injective. -/
private lemma algEquiv_eq_of_spec_comp_eq {Y : Scheme.{u}} (hY : Nonempty Y)
    (f : Y ⟶ Spec (.of k')) (a b : k' ≃ₐ[k] k')
    (h : f ≫ Spec.map (CommRingCat.ofHom a.toAlgHom.toRingHom)
        = f ≫ Spec.map (CommRingCat.ofHom b.toAlgHom.toRingHom)) : a = b := by
  have hnt : Nontrivial Γ(Y, ⊤) := by
    obtain ⟨t⟩ := hY
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨Y.toSpecΓ.base t⟩
  set α : CommRingCat.of k' ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso (.of k')).inv ≫ f.appTop with hα
  have key (φ : k' →+* k') :
      (Scheme.ΓSpecIso (.of k')).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop
        = CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of k')).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have h2 : CommRingCat.ofHom a.toAlgHom.toRingHom ≫ α =
      CommRingCat.ofHom b.toAlgHom.toRingHom ≫ α := by
    have h1 := congrArg Scheme.Hom.appTop h
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
    have h3 := congrArg (fun z => (Scheme.ΓSpecIso (.of k')).inv ≫ z) h1
    simp only [← Category.assoc, key] at h3
    simpa [hα, Category.assoc] using h3
  exact AlgEquiv.ext fun x => α.hom.injective
    (by simpa using congrArg (fun z : k' →+* Γ(Y, ⊤) => z x) (congrArg CommRingCat.Hom.hom h2))

/-- **Stacks 0B86**, the freeness assertion: the group of `k`-automorphisms of `k'` acts freely
on `X_{k'}`.  For a finite Galois extension this is the first half of the tag; freeness in fact
needs no assumption on the extension. -/
@[stacks 0B86 "the Galois group acts freely on the base change"]
theorem isFreeOnNonemptyPoints_extensionBaseChange :
    IsFreeOnNonemptyPoints B (Spec (.of k)) hk (k' ≃ₐ[k] k')
      (extensionBaseChange k k' B hk hk' X) := by
  intro T hT
  refine ⟨fun a b x hab => ?_⟩
  set p : extensionBaseChange k k' B hk hk' X ⟶ yoneda.obj (specExtension k k' B hk hk') :=
    prod.fst
  have hfst : p.app T x ≫ specExtensionAut k k' B hk hk' a =
      p.app T x ≫ specExtensionAut k k' B hk hk' b := by
    rw [← extensionBaseChange_fst_smul, ← extensionBaseChange_fst_smul, hab]
  have hleft := congrArg (fun q => B.inclusion.map q.left) hfst
  simp only [Over.comp_left, Functor.map_comp] at hleft
  exact inv_injective
    (algEquiv_eq_of_spec_comp_eq k k' hT (B.inclusion.map (p.app T x).left) a⁻¹ b⁻¹ hleft)

/-! ### The Čech cover of a finite Galois extension

For a finite Galois extension the normal basis theorem makes `k' ⊗[k] k'` the algebra of
functions on the Galois group with values in `k'`, so `Spec k' ×_{Spec k} Spec k'` is the
disjoint union of one copy of `Spec k'` for each element of the group. -/

/-- For a finite Galois extension `k'/k` the `k'`-algebra map `k' ⊗[k] k' ⟶ (G → k')` given on
the `g`-th component by `a ⊗ b ↦ a * g b` is bijective: in the normal basis of `k'/k` its
matrix is the matrix of the group elements evaluated at the basis, whose rows are linearly
independent because distinct field embeddings are. -/
private theorem galoisTensorPi_bijective [FiniteDimensional k k'] [IsGalois k k'] :
    letI : Algebra k' (k' ⊗[k] k') := Algebra.TensorProduct.leftAlgebra
    letI : CommSemiring ((Gal(k'/k)) → k') := Pi.commSemiring
    letI : Algebra k' ((Gal(k'/k)) → k') := Pi.algebra (Gal(k'/k)) (fun _ => k')
    let φ : k' ⊗[k] k' →ₐ[k'] (Gal(k'/k) → k') := AlgHom.pi fun g =>
      Algebra.TensorProduct.lift (AlgHom.id k' k') g.toAlgHom (fun _ _ => Commute.all _ _)
    Function.Bijective φ := by
  classical
  let : Algebra k' (k' ⊗[k] k') := Algebra.TensorProduct.leftAlgebra
  let b := IsGalois.normalBasis k k'
  let φ : k' ⊗[k] k' →ₐ[k'] (Gal(k'/k) → k') := AlgHom.pi fun g =>
    Algebra.TensorProduct.lift (AlgHom.id k' k') g.toAlgHom (fun _ _ => Commute.all _ _)
  let e := Algebra.TensorProduct.equivPiOfFiniteBasis k' b
  let M : Matrix (Gal(k'/k)) (Gal(k'/k)) k' := Matrix.of fun g h => g (b h)
  have heval (z : k' ⊗[k] k') (g : Gal(k'/k)) : φ z g = M.mulVec (e z) g := by
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a y
      change a * g y = _
      conv_lhs => rw [← b.sum_repr y]
      simp only [map_sum, map_smul]
      have he : e (a ⊗ₜ[k] y) = fun h => (b.repr y) h • a := by
        ext h
        simp [e]
      rw [he]
      change a * (∑ h, (b.repr y) h • g (b h)) = ∑ h, g (b h) * ((b.repr y) h • a)
      simp only [Algebra.smul_def]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    · intro x y hx hy
      simp only [map_add, Pi.add_apply, Matrix.mulVec_add, hx, hy]
  have hEmb : LinearIndependent k'
      (fun g : Gal(k'/k) => (algEquivEquivAlgHom k k' g).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap k k' k').comp _ (algEquivEquivAlgHom k k').injective
  let ev : (Gal(k'/k) → k') ≃ₗ[k'] (k' →ₗ[k] k') := b.constr k'
  have hrows : LinearIndependent k' M.row := by
    have h' : LinearIndependent k'
        (fun g : Gal(k'/k) => ev.symm ((algEquivEquivAlgHom k k' g).toLinearMap)) :=
      hEmb.map' ev.symm.toLinearMap (LinearMap.ker_eq_bot.mpr ev.symm.injective)
    have heq : (fun g : Gal(k'/k) => ev.symm
        ((algEquivEquivAlgHom k k' g).toLinearMap)) = M.row := by
      funext g
      ext h
      simp [M, ev]
    rwa [heq] at h'
  have hMunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  refine ⟨fun x y hxy => e.injective
      (Matrix.mulVec_injective_iff_isUnit.mpr hMunit (funext fun g => ?_)), fun f => ?_⟩
  · rw [← heval x, ← heval y, hxy]
  · obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hMunit f
    exact ⟨e.symm v, funext fun g => by rw [heval, e.apply_symm_apply, hv]⟩

/-- The splitting `k' ⊗[k] k' ≅ (G → k')` of a finite Galois extension, as an isomorphism of
`k'`-algebras for the left factor. -/
private def galoisTensorPi [FiniteDimensional k k'] [IsGalois k k'] :
    letI : Algebra k' (k' ⊗[k] k') := Algebra.TensorProduct.leftAlgebra
    letI : CommSemiring (Gal(k'/k) → k') := Pi.commSemiring
    letI : Algebra k' (Gal(k'/k) → k') := Pi.algebra (Gal(k'/k)) (fun _ => k')
    AlgEquiv k' (k' ⊗[k] k') (Gal(k'/k) → k') := by
  classical
  letI : Algebra k' (k' ⊗[k] k') := Algebra.TensorProduct.leftAlgebra
  letI : CommSemiring (Gal(k'/k) → k') := Pi.commSemiring
  letI : Algebra k' (Gal(k'/k) → k') := Pi.algebra (Gal(k'/k)) (fun _ => k')
  let φ : k' ⊗[k] k' →ₐ[k'] (Gal(k'/k) → k') := AlgHom.pi fun g =>
    Algebra.TensorProduct.lift (AlgHom.id k' k') g.toAlgHom (fun _ _ => Commute.all _ _)
  exact AlgEquiv.ofBijective φ (galoisTensorPi_bijective k k')

private theorem galoisTensorPi_tmul [FiniteDimensional k k'] [IsGalois k k']
    (a b : k') (g : Gal(k'/k)) : galoisTensorPi k k' (a ⊗ₜ[k] b) g = a * g b := by
  classical
  simp [galoisTensorPi, Algebra.TensorProduct.lift_tmul]

/-- For a finite Galois extension `k'/k` the self-product `Spec k' ×_{Spec k} Spec k'` is the
disjoint union of one copy of `Spec k'` for each element of the Galois group. -/
private def specGaloisCechIso [FiniteDimensional k k'] [IsGalois k k'] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k k')))
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ≅
      ∐ fun _ : Gal(k'/k) => Spec (.of k') := by
  classical
  let e : CommRingCat.of (k' ⊗[k] k') ≅ CommRingCat.of (Gal(k'/k) → k') :=
    (galoisTensorPi k k').toRingEquiv.toCommRingCatIso
  exact AlgebraicGeometry.pullbackSpecIso k k' k' ≪≫ Scheme.Spec.mapIso e.symm.op ≪≫
    (asIso (AlgebraicGeometry.sigmaSpec (fun _ : Gal(k'/k) => CommRingCat.of k'))).symm

/-- The inclusion of the `g`-th copy of `Spec k'` into the Čech cover, followed by the inverse of
`specGaloisCechIso`, is `Spec` of the evaluation at `g` and of the splitting
`k' ⊗[k] k' ≅ (G → k')`, followed by the identification of the pullback with `Spec (k' ⊗[k] k')`. -/
private theorem ι_specGaloisCechIso_inv [FiniteDimensional k k'] [IsGalois k k']
    (g : Gal(k'/k)) :
    Sigma.ι (fun _ : Gal(k'/k) => Spec (.of k')) g ≫ (specGaloisCechIso k k').inv =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Gal(k'/k) => k') g)) ≫
        Spec.map (CommRingCat.ofHom (galoisTensorPi k k').toRingEquiv.toRingHom) ≫
        (AlgebraicGeometry.pullbackSpecIso k k' k').inv := by
  classical
  simp only [specGaloisCechIso, Iso.trans_inv, Iso.symm_inv, Iso.op_inv,
    Functor.mapIso_inv, CategoryTheory.asIso_hom]
  simp only [← Category.assoc]
  rw [AlgebraicGeometry.ι_sigmaSpec]
  rfl

private theorem specGaloisCechIso_inv_fst [FiniteDimensional k k'] [IsGalois k k']
    (g : Gal(k'/k)) :
    Sigma.ι (fun _ : Gal(k'/k) => Spec (.of k')) g ≫ (specGaloisCechIso k k').inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k k')))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) = 𝟙 _ := by
  classical
  have hcomp :
      ((Pi.evalRingHom (fun _ : Gal(k'/k) => k') g).comp
          (galoisTensorPi k k').toRingEquiv.toRingHom).comp
          (algebraMap k' (k' ⊗[k] k')) = RingHom.id k' := by
    ext a
    change (galoisTensorPi k k' (a ⊗ₜ[k] (1 : k')) g) = a
    rw [galoisTensorPi_tmul]
    simp
  rw [← Category.assoc, ι_specGaloisCechIso_inv]
  simp only [Category.assoc, AlgebraicGeometry.pullbackSpecIso_inv_fst', ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (by simpa [RingHom.comp_assoc] using hcomp)

private theorem specGaloisCechIso_inv_snd [FiniteDimensional k k'] [IsGalois k k']
    (g : Gal(k'/k)) :
    Sigma.ι (fun _ : Gal(k'/k) => Spec (.of k')) g ≫ (specGaloisCechIso k k').inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k k')))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) =
      Spec.map (CommRingCat.ofHom g.toAlgHom.toRingHom) := by
  classical
  have hcomp :
      ((Pi.evalRingHom (fun _ : Gal(k'/k) => k') g).comp
          (galoisTensorPi k k').toRingEquiv.toRingHom).comp
          (Algebra.TensorProduct.includeRight :
            k' →ₐ[k] k' ⊗[k] k').toRingHom = g.toAlgHom.toRingHom := by
    ext b
    change (galoisTensorPi k k' ((1 : k') ⊗ₜ[k] b) g) = g b
    rw [galoisTensorPi_tmul]
    simp
  rw [← Category.assoc, ι_specGaloisCechIso_inv]
  simp only [Category.assoc, AlgebraicGeometry.pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext hcomp

/-! ### `X` is the quotient of `X_{k'}` -/

/-- For a finite Galois extension, a sieve on a test object `T` containing every arrow along
which two morphisms `T ⟶ Spec k'` become related by some element of the Galois group is a
covering sieve: the two morphisms jointly define a morphism to
`Spec k' ×_{Spec k} Spec k'`, which is covered by the copies of `Spec k'` indexed by the
group. -/
private lemma orbitSieve_mem_of_galois [FiniteDimensional k k'] [IsGalois k k']
    (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : T ⟶ specExtension k k' B hk hk') (R : Sieve T)
    (hR : ∀ (U : BigFppfOver B (Spec (.of k)) hk) (f : U ⟶ T) (g : Gal(k'/k)),
      f ≫ a ≫ specExtensionAut k k' B hk hk' g = f ≫ b → R f) :
    R ∈ BigFppfOver.topology B (Spec (.of k)) hk T := by
  classical
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hab : a.left.hom ≫ s = b.left.hom ≫ s :=
    (congrArg (fun f => f.hom) a.w).trans (congrArg (fun f => f.hom) b.w).symm
  let l : T.left.obj ⟶ pullback s s := pullback.lift a.left.hom b.left.hom hab
  let C := (AlgebraicGeometry.sigmaOpenCover (fun _ : Gal(k'/k) => Spec (.of k'))).pushforwardIso
    (specGaloisCechIso k k').inv
  let D := C.pullback₁ l
  have hsize (i : D.I₀) : B.Contains (D.X i) :=
    Scheme.size_lt_of_isOpenImmersion (D.f i) T.left.property
  let U (i : D.I₀) : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (D.f i ≫ T.hom.hom) : B.obj (hsize i) ⟶ B.obj hk)
  let f (i : D.I₀) : U i ⟶ T := Over.homMk (ObjectProperty.homMk (D.f i))
  apply (BigFppfOver.topology B (Spec (.of k)) hk).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_)
    (BigFppfOver.sieve_generate_ofArrows_mem_topology U f ?_)
  · rintro _ _ ⟨i⟩
    let g₀ : Gal(k'/k) := i
    apply hR (U i) (f i) g₀⁻¹
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    have hcf : C.f i ≫ pullback.fst s s = 𝟙 _ := specGaloisCechIso_inv_fst k k' g₀
    have hcs : C.f i ≫ pullback.snd s s =
        Spec.map (CommRingCat.ofHom g₀.toAlgHom.toRingHom) :=
      specGaloisCechIso_inv_snd k k' g₀
    have hlf : l ≫ pullback.fst s s = a.left.hom := pullback.lift_fst _ _ _
    have hls : l ≫ pullback.snd s s = b.left.hom := pullback.lift_snd _ _ _
    have hproj {Z : Scheme.{u}} (π : pullback s s ⟶ Z) :
        D.f i ≫ l ≫ π = C.pullbackHom l i ≫ C.f i ≫ π := by
      simp only [← Category.assoc]
      exact congrArg (· ≫ π) (C.pullbackHom_map l i).symm
    have hfst := hproj (pullback.fst s s)
    rw [hlf, hcf] at hfst
    have hsnd := hproj (pullback.snd s s)
    rw [hls, hcs] at hsnd
    have key : D.f i ≫ a.left.hom ≫
        Spec.map (CommRingCat.ofHom g₀.toAlgHom.toRingHom) = D.f i ≫ b.left.hom :=
      (Category.assoc (D.f i) a.left.hom _).symm.trans
        ((congrArg (· ≫ Spec.map (CommRingCat.ofHom g₀.toAlgHom.toRingHom))
          (hfst.trans (Category.comp_id _))).trans hsnd.symm)
    exact (congrArg (fun g : Gal(k'/k) => D.f i ≫ a.left.hom ≫
      Spec.map (CommRingCat.ofHom g.toAlgHom.toRingHom)) (inv_inv g₀)).trans key
  · exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ D.mem₀

/-- Two sections of a binary product of presheaves of types over the same test object agree as
soon as their two projections agree. -/
private lemma prod_presheaf_section_ext {C : Type*} [Category.{u} C]
    {F H : Cᵒᵖ ⥤ Type u} {T : C} {x y : (F ⨯ H).obj (Opposite.op T)}
    (hf : (prod.fst : F ⨯ H ⟶ F).app _ x = (prod.fst : F ⨯ H ⟶ F).app _ y)
    (hh : (prod.snd : F ⨯ H ⟶ H).app _ x = (prod.snd : F ⨯ H ⟶ H).app _ y) : x = y := by
  apply yonedaEquiv.symm.injective
  apply prod.hom_ext <;> apply yonedaEquiv.injective
  · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hf
  · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hh

private lemma isLocallyInjective_orbitLift [FiniteDimensional k k'] [IsGalois k k'] :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (orbitLift B (Spec (.of k)) hk (Gal(k'/k)) (extensionBaseChange k k' B hk hk' X)
        (isNaturalAction_extensionBaseChange k k' B hk hk' X)
        (extensionBaseChangeProj k k' B hk hk' X)
        (extensionBaseChangeProj_smul k k' B hk hk' X)) := by
  constructor
  intro T x y hxy
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      let p : extensionBaseChange k k' B hk hk' X ⟶
          yoneda.obj (specExtension k k' B hk hk') := prod.fst
      apply orbitSieve_mem_of_galois k k' B hk hk' T.unop (p.app T x) (p.app T y)
      intro U f g hg
      change Quotient.mk (MulAction.orbitRel (Gal(k'/k)) _)
          ((extensionBaseChange k k' B hk hk' X).map f.op x) =
        Quotient.mk (MulAction.orbitRel (Gal(k'/k)) _)
          ((extensionBaseChange k k' B hk hk' X).map f.op y)
      symm
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      apply prod_presheaf_section_ext
      · rw [extensionBaseChange_fst_smul]
        have hn (z : (extensionBaseChange k k' B hk hk' X).obj T) :
            p.app _ ((extensionBaseChange k k' B hk hk' X).map f.op z) = f ≫ p.app T z :=
          NatTrans.naturality_apply p f.op z
        exact (congrArg (fun α => α ≫ specExtensionAut k k' B hk hk' g) (hn x)).trans
          (hg.trans (hn y).symm)
      · change (extensionBaseChangeProj k k' B hk hk' X).app _
            (g • (extensionBaseChange k k' B hk hk' X).map f.op x) =
          (extensionBaseChangeProj k k' B hk hk' X).app _
            ((extensionBaseChange k k' B hk hk' X).map f.op y)
        rw [extensionBaseChangeProj_smul, NatTrans.naturality_apply, NatTrans.naturality_apply]
        exact congrArg (X.map f.op) hxy

private lemma isLocallySurjective_orbitLift [FiniteDimensional k k'] :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (orbitLift B (Spec (.of k)) hk (Gal(k'/k)) (extensionBaseChange k k' B hk hk' X)
        (isNaturalAction_extensionBaseChange k k' B hk hk' X)
        (extensionBaseChangeProj k k' B hk hk' X)
        (extensionBaseChangeProj_smul k k' B hk hk' X)) := by
  let J := BigFppfOver.topology B (Spec (.of k)) hk
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hflat : Flat s := Flat.SpecMap_iff.mpr ((RingHom.flat_algebraMap_iff).mpr inferInstance)
  have hsurj : Surjective s := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have hs : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      ((RingHom.finitePresentation_algebraMap).mpr
        (Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType k k')))
  constructor
  intro T x
  let P := pullback T.hom.hom s
  have hP : B.Contains P := Scheme.size_pullback_lt _ _ T.left.property hk'
  let U : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (pullback.fst T.hom.hom s ≫ T.hom.hom) :
      B.obj hP ⟶ B.obj hk)
  let f : U ⟶ T := Over.homMk (ObjectProperty.homMk (pullback.fst T.hom.hom s))
  let a : U ⟶ specExtension k k' B hk hk' :=
    Over.homMk (ObjectProperty.homMk (pullback.snd T.hom.hom s))
      (by apply ObjectProperty.hom_ext; exact pullback.condition.symm)
  have : Flat ((BigFppfOver.toScheme B (Spec (.of k)) hk).map f) :=
    inferInstanceAs (Flat (pullback.fst T.hom.hom s))
  have : Surjective ((BigFppfOver.toScheme B (Spec (.of k)) hk).map f) :=
    inferInstanceAs (Surjective (pullback.fst T.hom.hom s))
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B (Spec (.of k)) hk).map f) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst T.hom.hom s))
  have hf : Sieve.generate
      (Presieve.ofArrows (fun _ : PUnit.{u + 1} => U) (fun _ => f)) ∈ J T := by
    refine BigFppfOver.sieve_generate_ofArrows_mem_topology _ _ ?_
    rw [Presieve.ofArrows_pUnit]
    exact ((BigFppfOver.toScheme B (Spec (.of k)) hk).map f).singleton_mem_fppfPrecoverage
  apply J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hf
  rintro _ _ ⟨⟩
  let z : (extensionBaseChange k k' B hk hk' X).obj (Opposite.op U) :=
    yonedaEquiv (prod.lift (yoneda.map a) (yonedaEquiv.symm (X.map f.op x)))
  refine ⟨Quotient.mk (MulAction.orbitRel (Gal(k'/k)) _) z, ?_⟩
  change (extensionBaseChangeProj k k' B hk hk' X).app _ z = X.map f.op x
  dsimp only [z, extensionBaseChangeProj]
  rw [← yonedaEquiv_comp, prod.lift_snd, Equiv.apply_symm_apply]

/-- The lift of a locally bijective map of presheaves to the sheafification of its source is an
isomorphism onto a sheaf target. -/
private lemma isIso_sheafifyLift_of_isLocallyBijective {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type u)]
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] :
    IsIso (sheafifyLift J φ hQ) := by
  obtain ⟨i, hi, -⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J φ
    (toSheafify J P) ((presheafToSheaf J (Type u)).obj P).property
  refine ⟨⟨i, ?_, ?_⟩⟩
  · apply sheafify_hom_ext J _ _ ((presheafToSheaf J (Type u)).obj P).property
    rw [← Category.assoc, toSheafify_sheafifyLift, hi, Category.comp_id]
  · obtain ⟨_, -, huniq⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J φ φ hQ
    exact (huniq _ (by
      dsimp only
      rw [← Category.assoc, hi, toSheafify_sheafifyLift])).trans
      (huniq _ (Category.comp_id φ)).symm

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The quotient of `X_{k'}` by the `k`-automorphisms of `k'`. -/
def extensionBaseChangeQuotient :
    Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u) :=
  orbitQuotientSheaf B (Spec (.of k)) hk (k' ≃ₐ[k] k')
    (extensionBaseChange k k' B hk hk' X)
    (isNaturalAction_extensionBaseChange k k' B hk hk' X)

/-- The canonical map `X_{k'}/G ⟶ X` induced by the projection. -/
def extensionBaseChangeQuotientLift
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk) X) :
    (extensionBaseChangeQuotient k k' B hk hk' X).obj ⟶ X :=
  orbitQuotientLift B (Spec (.of k)) hk (k' ≃ₐ[k] k')
    (extensionBaseChange k k' B hk hk' X)
    (isNaturalAction_extensionBaseChange k k' B hk hk' X)
    (extensionBaseChangeProj k k' B hk hk' X)
    (extensionBaseChangeProj_smul k k' B hk hk' X) hX

/-- For a finite Galois extension `k'/k` with group `G`, every fppf sheaf `X` on the big fppf
site of `Spec k` is the quotient `X_{k'}/G`. -/
theorem isIso_extensionBaseChangeQuotientLift_of_isSheaf
    [FiniteDimensional k k'] [IsGalois k k']
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk) X) :
    IsIso (extensionBaseChangeQuotientLift k k' B hk hk' X hX) := by
  have := isLocallyInjective_orbitLift k k' B hk hk' X
  have := isLocallySurjective_orbitLift k k' B hk hk' X
  exact isIso_sheafifyLift_of_isLocallyBijective _ _ hX

/-- **Stacks 0B86**, the quotient assertion: for a finite Galois extension `k'/k` with Galois
group `G`, an algebraic space `X` over `k` is the quotient `X_{k'}/G`. -/
@[stacks 0B86 "X = X_{k'}/G"]
theorem isIso_extensionBaseChangeQuotientLift [FiniteDimensional k k'] [IsGalois k k']
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsIso (extensionBaseChangeQuotientLift k k' B hk hk' X hX.isSheaf) :=
  isIso_extensionBaseChangeQuotientLift_of_isSheaf k k' B hk hk' X hX.isSheaf

end AlgebraicGeometry.Space

end
