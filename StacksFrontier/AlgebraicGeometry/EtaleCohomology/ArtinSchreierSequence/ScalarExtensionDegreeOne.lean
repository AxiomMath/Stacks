module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ComparisonScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.MayerVietorisDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# `H¹(X_{k'}, 𝐆_a)` is spanned by the restrictions of `H¹(X, 𝐆_a)`

Let `X` be a scheme over a field `k` covered by two open subschemes `U`, `V` whose base changes to
an extension `k'/k` are affine and whose intersection is affine, and let `g : X_{k'} ⟶ X` be the
projection. Restricting étale cohomology along `g` and pulling functions back gives an additive
map `H¹(X, 𝐆_a) ⟶ H¹(X_{k'}, 𝐆_a)` (`Stacks.ArtinSchreier.additiveRestriction`). This file
proves that its image spans the target over `k'`, the action of `k'` on the target being
multiplication by scalars on `𝐆_a`.

Both groups are computed by the Mayer–Vietoris sequence of the cover: every class of
`H¹(X_{k'}, 𝐆_a)` is a coboundary of a morphism `g^{-1} j_{U ∩ V!} ℤ ⟶ 𝐆_a`, because `H¹` of `𝐆_a`
vanishes on the affine schemes `U_{k'}`, `V_{k'}`; such a morphism is a function on `(U ∩ V)_{k'}`;
and since `U ∩ V` is affine, the functions on `(U ∩ V)_{k'}` are `k'`-linear combinations of
functions pulled back from `U ∩ V`, the ring of functions of the base change being the tensor
product (`AlgebraicGeometry.isPushout_appTop_of_isPullback`).

## Main definitions

* `Stacks.ArtinSchreier.additiveRestriction`: the restriction map on the cohomology of `𝐆_a`.

## Main results

* `Stacks.ArtinSchreier.exists_sum_of_isPushout`: in a pushout of commutative rings every element
  is a sum of products of elements of the two corners.
* `Stacks.ArtinSchreier.exists_sum_additiveRestriction_one`: the spanning statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

/-! ### Rings -/

/-- **Every element of a pushout of commutative rings is a sum of products** `inr c * inl b`:
the pushout is the tensor product, which is spanned by pure tensors. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (x : P) :
    ∃ (n : ℕ) (b : Fin n → B) (c : Fin n → C), x = ∑ i, inr.hom (c i) * inl.hom (b i) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have h' := CommRingCat.isPushout_tensorProduct A B C
  let e := h'.isoIsPushout _ _ h
  have hl : ∀ b : B, e.hom.hom (Algebra.TensorProduct.includeLeftRingHom b) = inl.hom b :=
    fun b => congrArg (fun φ : B ⟶ P => φ.hom b) (h'.inl_isoIsPushout_hom _ _ h)
  have hr : ∀ c : C, e.hom.hom (Algebra.TensorProduct.includeRight.toRingHom c) = inr.hom c :=
    fun c => congrArg (fun φ : C ⟶ P => φ.hom c) (h'.inr_isoIsPushout_hom _ _ h)
  suffices H : ∀ t : TensorProduct A B C,
      ∃ (n : ℕ) (b : Fin n → B) (c : Fin n → C), e.hom.hom t = ∑ i, inr.hom (c i) * inl.hom (b i) by
    obtain ⟨n, b, c, hbc⟩ := H (e.inv.hom x)
    exact ⟨n, b, c, (Iso.inv_hom_id_apply e x).symm.trans hbc⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul b c =>
    refine ⟨1, fun _ => b, fun _ => c, ?_⟩
    rw [show (b ⊗ₜ[A] c : TensorProduct A B C) = Algebra.TensorProduct.includeLeftRingHom b *
        Algebra.TensorProduct.includeRight.toRingHom c by simp,
      map_mul, hl, hr, Fin.sum_univ_one, mul_comm]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, b₁, c₁, e₁⟩ := h₁
    obtain ⟨n₂, b₂, c₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append b₁ b₂, Fin.append c₁ c₂, ?_⟩
    rw [map_add, e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-! ### Functions on the base change of an affine scheme -/

section ScalarExtension

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The structure morphism of the scalar extension `X_{k'}` to `Spec k'`. -/
abbrev scalarExtensionStructure : scalarExtension k k' f ⟶ Spec (.of k') :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- The pullback along `ψ ≫ φ` of a function on `Spec R` is the pullback along `ψ` of its image
in the global functions of the source of `φ`, read through `Γ(Spec R) ≅ R`. -/
theorem appTop_comp_eq_appTop_baseScalar {R : CommRingCat.{u}} {P Q : Scheme.{u}}
    (ψ : Q ⟶ P) (φ : P ⟶ Spec R) (γ : Γ(Spec R, ⊤)) :
    (ψ ≫ φ).appTop.hom γ = ψ.appTop.hom
      (((Scheme.ΓSpecIso R).inv ≫ φ.appLE ⊤ ⊤ (by simp)).hom ((Scheme.ΓSpecIso R).hom.hom γ)) := by
  rw [Stacks.Descent.appLE_top_top, CommRingCat.comp_apply, Iso.hom_inv_id_apply,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]

/-- **Functions on the base change of an affine étale `X`-scheme are `k'`-linear combinations of
pulled-back functions.** For an étale `X`-scheme `W` with affine underlying scheme, every global
function on `W ×_X X_{k'}` is a sum `∑ cᵢ • fᵢ` with `cᵢ ∈ k'` and `fᵢ` pulled back from `W`:
the square `W ×_X X_{k'} ⟶ W ⟶ Spec k`, `W ×_X X_{k'} ⟶ Spec k' ⟶ Spec k` is cartesian, so the
global functions form the pushout of rings, that is the tensor product. -/
theorem exists_sum_appTop_fst (W : X.Etale) [IsAffine W.left]
    (b : Γ(pullback W.hom (scalarExtensionFst k k' f), ⊤)) :
    ∃ (n : ℕ) (a : Fin n → Γ(W.left, ⊤)) (c : Fin n → k'),
      b = ∑ i, (pullback.snd W.hom (scalarExtensionFst k k' f)).appTop.hom
          (baseScalarSection k' (scalarExtensionStructure f) (c i)) *
        (pullback.fst W.hom (scalarExtensionFst k k' f)).appTop.hom (a i) := by
  have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := ‹IsAffine W.left›
  obtain ⟨n, a, γ, hb⟩ := exists_sum_of_isPushout (isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback W.hom (scalarExtensionFst k k' f)).paste_vert
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))))) b
  refine ⟨n, a, fun i => (Scheme.ΓSpecIso (.of k')).hom.hom (γ i), ?_⟩
  rw [hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact appTop_comp_eq_appTop_baseScalar _ _ _

end ScalarExtension

/-! ### `Ext` out of an object with a splitting -/

/-- `Ext` out of an object split by idempotents `p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙` vanishes when `Ext` out of
both summands vanishes. -/
theorem subsingleton_ext_of_decomposition {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {P A B Z : C} (i₁ : A ⟶ P) (i₂ : B ⟶ P) (p₁ : P ⟶ A) (p₂ : P ⟶ B)
    (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 P) (n : ℕ) (hA : Subsingleton (Ext.{w} A Z n))
    (hB : Subsingleton (Ext.{w} B Z n)) : Subsingleton (Ext.{w} P Z n) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  rw [← Ext.mk₀_id_comp z, ← h, Ext.mk₀_add, Ext.add_comp, ← Ext.mk₀_comp_mk₀,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n),
    Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n), hA.elim ((Ext.mk₀ i₁).comp z _) 0,
    hB.elim ((Ext.mk₀ i₂).comp z _) 0, Ext.comp_zero, Ext.comp_zero, add_zero]

/-! ### The restriction map on the cohomology of `𝐆_a` -/

section Restriction

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The restriction map on the étale cohomology of `𝐆_a`** along a morphism `g : Y ⟶ X`:
restriction of étale cohomology followed by pulling functions back. -/
def additiveRestriction (n : ℕ) :
    Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) n →+ Sheaf.H.{w} (additiveSheaf.{u, u + 1} Y) n :=
  (Sheaf.H.map (additiveInverseImageComparison.{u, u + 1} g) n).comp
    (etaleCohomologyRestrictionMap.{u, 0, w} g (additiveSheaf.{u, u + 1} X) n)

/-- `Stacks.ArtinSchreier.additiveRestriction`, unfolded. -/
theorem additiveRestriction_apply (n : ℕ) (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) n) :
    additiveRestriction g n x = Sheaf.H.map (additiveInverseImageComparison.{u, u + 1} g) n
      (etaleCohomologyRestrictionMap.{u, 0, w} g (additiveSheaf.{u, u + 1} X) n x) :=
  rfl

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- A map on `Y` applied to a coboundary of the inverse image of the Mayer–Vietoris sequence is
the coboundary of the composite. -/
theorem sheafH_map_coverDeltaInverseImage
    {F' F'' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (m : F' ⟶ F'')
    (t : (etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₁ ⟶ F') :
    Sheaf.H.map m 1 (coverDeltaInverseImage U V hUV g F' t) =
      coverDeltaInverseImage U V hUV g F'' (t ≫ m) := by
  rw [coverDeltaInverseImage_apply, coverDeltaInverseImage_apply, Sheaf.H.map_apply,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end Restriction

/-! ### The spanning statement -/

section Spanning

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The section of `𝐆_a` attached to a finite sum of functions is the sum of the sections. -/
theorem ofSection_sum {Z : Scheme.{u}} {T : Z.Etale} {n : ℕ} (x : Fin n → Γ(T.left, ⊤)) :
    ofSection.{u, u + 1} (∑ i, x i) = ∑ i, ofSection.{u, u + 1} (x i) :=
  map_sum (AddEquiv.ulift.{u, u + 1} (α := Γ(T.left, ⊤))).symm x Finset.univ

/-- **Morphisms `g^{-1} j_! j^{-1} ℤ ⟶ 𝐆_{a,X_{k'}}` are `k'`-linear combinations of pulled-back
morphisms `j_! j^{-1} ℤ ⟶ 𝐆_{a,X}`**, for an affine open `W` of `X`. Transposing along
`g^{-1} ⊣ g_*` and evaluating over `W`, this is the statement that functions on `W_{k'}` are
`k'`-linear combinations of functions pulled back from `W`
(`Stacks.ArtinSchreier.exists_sum_appTop_fst`). -/
theorem exists_sum_inverseImage_comp (W : X.Opens) [IsAffine (W : Scheme.{u})]
    (t : (etaleAbelianInverseImage.{u, 0} (scalarExtensionFst k k' f)).obj
      ((extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X)) ⟶
        additiveSheaf.{u, u + 1} (scalarExtension k k' f)) :
    ∃ (n : ℕ) (s : Fin n → ((extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶
        additiveSheaf.{u, u + 1} X)) (c : Fin n → k'),
      t = ∑ i, ((etaleAbelianInverseImage.{u, 0} (scalarExtensionFst k k' f)).map (s i) ≫
        additiveInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' f)) ≫
          additiveSmul.{u, u + 1} (scalarExtension k k' f)
            (baseScalarSection k' (scalarExtensionStructure f) (c i)) := by
  let g := scalarExtensionFst k k' f
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} g
  let Ψ := extensionByZeroOfRestrictionHomAddEquiv W
  have : IsAffine (opensEtaleObject W).left := ‹IsAffine (W : Scheme.{u})›
  obtain ⟨b, hb⟩ := ofSection_surjective.{u, u + 1}
    (U := (smallEtaleBaseChange g).obj (opensEtaleObject W))
    (Ψ ((etaleAbelianDirectImage.{u, 0} g).obj (additiveSheaf.{u, u + 1} (scalarExtension k k' f)))
      (adj.homEquiv _ _ t))
  obtain ⟨n, a, c, hbac⟩ := exists_sum_appTop_fst f (opensEtaleObject W) b
  refine ⟨n, fun i => (Ψ (additiveSheaf.{u, u + 1} X)).symm (ofSection (a i)), c, ?_⟩
  have htr : ∀ (σ : (extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶
      additiveSheaf.{u, u + 1} X) (m : additiveSheaf.{u, u + 1} (scalarExtension k k' f) ⟶
        additiveSheaf.{u, u + 1} (scalarExtension k k' f)),
      adj.homEquiv _ _ (((etaleAbelianInverseImage.{u, 0} g).map σ ≫
        additiveInverseImageComparison.{u, u + 1} g) ≫ m) =
      σ ≫ additiveDirectImageComparison.{u, u + 1} g ≫
        (etaleAbelianDirectImage.{u, 0} g).map m := fun σ m => by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Category.assoc]
    exact congrArg (fun φ => σ ≫ φ ≫ (etaleAbelianDirectImage.{u, 0} g).map m)
      (additiveInverseImageComparison_transpose.{u, u + 1} g)
  apply (adj.homEquiv _ _).injective
  apply (Ψ _).injective
  rw [← hb, ← adj.homAddEquiv_apply, map_sum, map_sum, hbac]
  refine (ofSection_sum (T := (smallEtaleBaseChange g).obj (opensEtaleObject W)) _).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [adj.homAddEquiv_apply, htr, extensionByZeroOfRestrictionHomAddEquiv_comp]
  simp only [Ψ, AddEquiv.apply_symm_apply]
  rfl

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`H¹(X_{k'}, 𝐆_a)` is spanned over `k'` by the restrictions of `H¹(X, 𝐆_a)`**, for `X`
covered by two opens `U`, `V` with `U ∩ V` affine and `U_{k'}`, `V_{k'}` affine. Every class of
`H¹(X_{k'}, 𝐆_a)` is a Mayer–Vietoris coboundary, `H¹(U_{k'}, 𝐆_a)` and `H¹(V_{k'}, 𝐆_a)` being
zero; coboundaries of pulled-back morphisms are restrictions of coboundaries; and every morphism
is a `k'`-linear combination of pulled-back ones. -/
theorem exists_sum_additiveRestriction_one (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [IsAffine ((U ⊓ V : X.Opens) : Scheme.{u})]
    [IsAffine (pullback U.ι (scalarExtensionFst k k' f))]
    [IsAffine (pullback V.ι (scalarExtensionFst k k' f))]
    (y : Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} (scalarExtension k k' f)) 1) :
    ∃ (n : ℕ) (x : Fin n → Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) 1) (c : Fin n → k'),
      y = ∑ i, Sheaf.H.map (additiveSmul.{u, u + 1} (scalarExtension k k' f)
        (baseScalarSection k' (scalarExtensionStructure f) (c i))) 1
          (additiveRestriction (scalarExtensionFst k k' f) 1 (x i)) := by
  let g := scalarExtensionFst k k' f
  let F := etaleAbelianInverseImage.{u, 0} g
  have : ∀ (T : Scheme.{u}), IsGrothendieckAbelian.{u + 1}
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := fun T =>
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse T
  let : ∀ (T : Scheme.{u}), HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun T => CategoryTheory.IsGrothendieckAbelian.hasExt _
  have hvan : Subsingleton (Ext.{u + 1} (F.obj (coverSequence U V).X₂)
      (additiveSheaf.{u, u + 1} (scalarExtension k k' f)) 1) := by
    refine subsingleton_ext_of_decomposition (F.map biprod.inl) (F.map biprod.inr)
      (F.map biprod.fst) (F.map biprod.snd) ?_ 1
      (subsingleton_ext_one_inverseImage_extensionByZeroOfRestriction g U)
      (subsingleton_ext_one_inverseImage_extensionByZeroOfRestriction g V)
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  obtain ⟨t, rfl⟩ := exists_coverDeltaInverseImage_eq U V hUV g _ hvan y
  obtain ⟨n, s, c, rfl⟩ := exists_sum_inverseImage_comp f (U ⊓ V) t
  refine ⟨n, fun i => coverDelta U V hUV (additiveSheaf.{u, u + 1} X) (s i), c, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [additiveRestriction_apply, sheafH_map_etaleCohomologyRestrictionMap_coverDelta,
    sheafH_map_coverDeltaInverseImage]

end Spanning

end Stacks.ArtinSchreier

end
