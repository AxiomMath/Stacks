module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheafIdeal
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# The structure sheaf of `X₀ ×_{Spec k} Spec k[V]` on the small étale site of `X₀`

Let `k` be a commutative ring, `V` a `k`-module whose trivial square-zero extension `k[V]` lies in
the site, `τ : Spec k[V] ⟶ Spec k` a morphism over `S` restricting to the identity along the
closed immersion `Spec k ⟶ Spec k[V]` (`τ` is `Spec` of a section `c ↦ (c, D c)` of the
projection, `D` a derivation), and let `X₀ ⟶ X_V ⟶ X₀` be the base change of
`Spec k ⟶ Spec k[V] ⟶ Spec k` along `p : X₀ ⟶ Spec k`. Then the structure sheaf of `X_V`,
carried to the small étale site of `X₀`, is the trivial square-zero extension
`𝒪_{X₀}[𝒪_{X₀} ⊗_k V]`, compatibly with restriction to `X₀`
(`AlgebraicGeometry.Space.squareZeroRetractionRingIso`,
`AlgebraicGeometry.Space.squareZeroRetractionRingIso_hom_comp`), `𝒪_{X₀}` being a `k`-algebra
through `p` (`AlgebraicGeometry.Space.squareZeroCoefficientMap`). Transposed under the Comparison
Lemma equivalence of the thickening, this is an isomorphism `𝒪_{X'} ≅ i^* (𝒪_{X₀}[𝒪_{X₀} ⊗_k V])`
on the site of `X'` compatible with the structure map of chart base change along `i`
(`AlgebraicGeometry.Space.squareZeroStructureSheafIso`,
`AlgebraicGeometry.Space.squareZeroStructureSheafIso_hom_comp`), hence an equivalence of
`𝒪_{X₀}[𝒪_{X₀} ⊗_k V]`-modules with `𝒪_{X'}`-modules
(`AlgebraicGeometry.Space.squareZeroModuleEquivalence`). The identification does not
depend on `τ` beyond the restriction maps.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [CommRing k] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k))) (V : SiteModule k B)

/-- The scheme underlying `Spec k` as an object over `S` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (algebraOver k B S hS toS hk)) :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- The scheme underlying `Spec k[V]` as an object over `S` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (squareZeroOver k B S hS toS V)) :=
  inferInstanceAs (IsAffine (Spec (squareZeroRing k V.obj)))

/-- The functions on `Spec k[V]` are `k[V]`. -/
def squareZeroSectionsEquiv : TrivSqZeroExt k V.obj ≃+*
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (squareZeroOver k B S hS toS V))) :=
  (Scheme.ΓSpecIso (squareZeroRing k V.obj)).commRingCatIsoToRingEquiv.symm

/-- The functions on `Spec k` are `k`. -/
def squareZeroBaseSectionsEquiv : k ≃+*
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (algebraOver k B S hS toS hk))) :=
  (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm

/-- The isomorphism `k ≅ Γ(Spec k)` of commutative rings. -/
abbrev squareZeroBaseIso :
    CommRingCat.of k ≅
      Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (algebraOver k B S hS toS hk))) :=
  (Scheme.ΓSpecIso (.of k)).symm

/-- The isomorphism `k ≅ Γ(Spec k)` agrees with
`AlgebraicGeometry.Space.squareZeroBaseSectionsEquiv`. -/
theorem squareZeroBaseIso_hom_apply (c : k) :
    (squareZeroBaseIso k B S hS toS hk).hom c = squareZeroBaseSectionsEquiv k B S hS toS hk c := rfl

/-- The inclusion `V ⟶ Γ(Spec k[V])`, `v ↦ (0, v)`. -/
def dualNumbersIdealInclusion :
    V.obj →+
      Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (squareZeroOver k B S hS toS V))) :=
  (squareZeroSectionsEquiv k B S hS toS V).toAddMonoidHom.comp
    (TrivSqZeroExt.inrHom k V.obj).toAddMonoidHom

/-- The inclusion `V ⟶ Γ(Spec k[V])` sends `v` to the function `(0, v)`. -/
theorem dualNumbersIdealInclusion_apply (v : V.obj) :
    dualNumbersIdealInclusion k B S hS toS V v =
      squareZeroSectionsEquiv k B S hS toS V (TrivSqZeroExt.inr v) := rfl

/-- Functions on `Spec k[V]` restricted to `Spec k`: the projection `k[V] ⟶ k`. -/
theorem Γ_map_squareZeroArrow_apply (x : TrivSqZeroExt k V.obj) :
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (squareZeroArrow k B S hS toS hk V)).op
        (squareZeroSectionsEquiv k B S hS toS V x) =
      squareZeroBaseSectionsEquiv k B S hS toS hk x.fst := by
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k V.obj).toRingHom))).symm

/-- Functions on `Spec k[V]` restricted to `Spec k` are the first component. -/
private theorem Γ_map_squareZeroArrow_eq_fst
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (squareZeroOver k B S hS toS V)))) :
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (squareZeroArrow k B S hS toS hk V)).op t =
      squareZeroBaseSectionsEquiv k B S hS toS hk
        ((squareZeroSectionsEquiv k B S hS toS V).symm t).fst := by
  rw [← Γ_map_squareZeroArrow_apply, RingEquiv.apply_symm_apply]

variable {k B S hS toS hk V} in
/-- **A retraction `Spec k[V] ⟶ Spec k` of `Spec k ⟶ Spec k[V]` is `Spec` of a section of the
projection** `k[V] ⟶ k`: the function `c` on `Spec k` pulls back to a function on `Spec k[V]`
with first component `c`. -/
theorem fst_Γ_map_retraction {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) (c : k) :
    ((squareZeroSectionsEquiv k B S hS toS V).symm
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op
        (squareZeroBaseSectionsEquiv k B S hS toS hk c))).fst = c := by
  exact (squareZeroBaseSectionsEquiv k B S hS toS hk).injective
    ((Γ_map_squareZeroArrow_eq_fst k B S hS toS hk V _).symm.trans
      (Γ_map_section_retraction hβτ (squareZeroBaseSectionsEquiv k B S hS toS hk c)))

/-- The image of `V` in `Γ(Spec k[V])` restricts to zero on `Spec k`. -/
theorem dualNumbersIdealInclusion_retraction (v : V.obj) :
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (squareZeroArrow k B S hS toS hk V)).op
      (dualNumbersIdealInclusion k B S hS toS V v) = 0 := by
  rw [dualNumbersIdealInclusion_apply, Γ_map_squareZeroArrow_apply, TrivSqZeroExt.fst_inr,
    map_zero]

variable {k B S hS toS hk V} in
/-- For a retraction `τ : Spec k[V] ⟶ Spec k` of `Spec k ⟶ Spec k[V]`, the inclusion of `V` is
`k`-linear when `Γ(Spec k[V])` is a `k`-algebra through `τ`. -/
theorem dualNumbersIdealInclusion_smul
    {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) (c : k) (v : V.obj) :
    dualNumbersIdealInclusion k B S hS toS V (c • v) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op
        ((squareZeroBaseIso k B S hS toS hk).hom c) *
          dualNumbersIdealInclusion k B S hS toS V v := by
  rw [squareZeroBaseIso_hom_apply, dualNumbersIdealInclusion_apply, dualNumbersIdealInclusion_apply,
    ← RingEquiv.apply_symm_apply (squareZeroSectionsEquiv k B S hS toS V)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op
        (squareZeroBaseSectionsEquiv k B S hS toS hk c)),
    ← map_mul]
  congr 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp
  · rw [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inr,
      TrivSqZeroExt.fst_inr, MulOpposite.op_zero, zero_smul, add_zero, fst_Γ_map_retraction hβτ c]

/-- The inclusion `V ⟶ Γ(Spec k[V])` is injective. -/
theorem dualNumbersIdealInclusion_injective :
    Function.Injective (dualNumbersIdealInclusion k B S hS toS V) := fun _ _ hvw =>
  TrivSqZeroExt.inr_injective ((squareZeroSectionsEquiv k B S hS toS V).injective hvw)

/-- Every function on `Spec k[V]` restricting to zero on `Spec k` lies in the image of `V`. -/
theorem dualNumbersIdealInclusion_surjective_ker
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (squareZeroOver k B S hS toS V))))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (squareZeroArrow k B S hS toS hk V)).op
      t = 0) :
    ∃ v, dualNumbersIdealInclusion k B S hS toS V v = t := by
  have h2 := Γ_map_squareZeroArrow_eq_fst k B S hS toS hk V t
  rw [ht] at h2
  refine ⟨((squareZeroSectionsEquiv k B S hS toS V).symm t).snd, ?_⟩
  apply (squareZeroSectionsEquiv k B S hS toS V).symm.injective
  rw [dualNumbersIdealInclusion_apply, RingEquiv.symm_apply_apply]
  exact TrivSqZeroExt.ext
    ((squareZeroBaseSectionsEquiv k B S hS toS hk).injective (h2.symm.trans (map_zero _).symm)).symm
    rfl

/-- The image of `V` in `Γ(Spec k[V])` has square zero. -/
theorem dualNumbersIdealInclusion_mul (v w : V.obj) :
    dualNumbersIdealInclusion k B S hS toS V v *
      dualNumbersIdealInclusion k B S hS toS V w = 0 := by
  rw [dualNumbersIdealInclusion_apply, dualNumbersIdealInclusion_apply, ← map_mul,
    TrivSqZeroExt.inr_mul_inr, map_zero]

section Retraction

variable {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) (hq : yoneda.relativelyRepresentable q.hom)
  (p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk))
  {p' : X'.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}

/-- **The `k`-algebra structure of `𝒪_X` through `p : X ⟶ Spec k`**: over a chart `W` a scalar
`c` is the pullback of `c ∈ Γ(Spec k)` along `W ⟶ X ⟶ Spec k`. -/
abbrev squareZeroCoefficientMap :
    Stacks.TensorByBaseModule.constantRingPresheaf (C := SmallEtale B S hS X.1) k ⟶
      (structureSheaf B S hS X.1 X.2).obj :=
  retractionCoefficientMap B S hS (p := p) k (squareZeroBaseIso k B S hS toS hk).hom

variable {k B S hS toS hk V hq p} in
/-- **The ideal of `X` in the base change `X'` of `Spec k ⟶ Spec k[V]` is `𝒪_X ⊗_k V`.** -/
def squareZeroRetractionIdealIso
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    (tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj ≅
      splitIdeal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq) :=
  retractionIdealIso (φ₀ := squareZeroBaseIso k B S hS toS hk) hi h hip hpb hβτ
    (dualNumbersIdealInclusion k B S hS toS V)
    (dualNumbersIdealInclusion_retraction k B S hS toS hk V)
    (dualNumbersIdealInclusion_smul hβτ) (dualNumbersIdealInclusion_injective k B S hS toS V)
    (dualNumbersIdealInclusion_surjective_ker k B S hS toS hk V)

variable {k B S hS toS hk V hq p} in
/-- **The structure sheaf of `X'` on the site of `X` is `𝒪_X[𝒪_X ⊗_k V]`**, for `X ⟶ X' ⟶ X` the
base change of `Spec k ⟶ Spec k[V] ⟶ Spec k` along `p : X ⟶ Spec k`. -/
def squareZeroRetractionRingIso
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    thickeningRetractionRing B S hS hq ≅ sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj) :=
  thickeningRetractionRingIso (φ₀ := squareZeroBaseIso k B S hS toS hk) hi h hip hpb hβτ
    (dualNumbersIdealInclusion k B S hS toS V)
    (dualNumbersIdealInclusion_retraction k B S hS toS hk V)
    (dualNumbersIdealInclusion_smul hβτ) (dualNumbersIdealInclusion_injective k B S hS toS V)
    (dualNumbersIdealInclusion_surjective_ker k B S hS toS hk V)
    (dualNumbersIdealInclusion_mul k B S hS toS V)

variable {k B S hS toS hk V hq p} in
/-- The isomorphism `q_*𝒪_{X'} ≅ 𝒪_X[𝒪_X ⊗_k V]` carries restriction to `X` to the projection. -/
theorem squareZeroRetractionRingIso_hom_comp
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    (squareZeroRetractionRingIso hi h hip hpb hβτ).hom ≫ sqZeroExtSheafAnySiteProj _ =
      thickeningRetractionRestriction B S hS hi h hq :=
  thickeningRetractionRingIso_hom_comp hi h hip hpb hβτ _ _ _ _ _ _

variable {k B S hS toS hk V hq p} in
/-- **The structure sheaf of `X'` on its own site is `i^* (𝒪_X[𝒪_X ⊗_k V])`**, for `X ⟶ X' ⟶ X` the
base change of `Spec k ⟶ Spec k[V] ⟶ Spec k`: the transpose of
`AlgebraicGeometry.Space.squareZeroRetractionRingIso` under the Comparison Lemma equivalence. -/
def squareZeroStructureSheafIso
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    structureSheaf B S hS X'.1 X'.2 ≅
      (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).functor.obj
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) :=
  thickeningRetractionTranspose B S hS hi h hq (squareZeroRetractionRingIso hi h hip hpb hβτ)

variable {k B S hS toS hk V hq p} in
/-- The isomorphism `𝒪_{X'} ≅ i^* (𝒪_X[𝒪_X ⊗_k V])` followed by the projection is the structure
map of chart base change along `i`. -/
theorem squareZeroStructureSheafIso_hom_comp
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    (squareZeroStructureSheafIso hi h hip hpb hβτ).hom ≫
        (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).functor.map
          (sqZeroExtSheafAnySiteProj _) =
      smallBaseChangeSharpCommRingCat B S hS i hi.isClosedImmersion.rep :=
  thickeningRetractionTranspose_hom_comp B S hS hi h hq _ _
    (squareZeroRetractionRingIso_hom_comp hi h hip hpb hβτ)

variable {k B S hS toS hk V hq p} in
/-- **Sheaves of modules over `𝒪_X[𝒪_X ⊗_k V]` on the site of `X` are the `𝒪_{X'}`-modules**:
restriction along chart base change along `i` (the Comparison Lemma,
`AlgebraicGeometry.Space.thickeningHomModuleEquivalence`) followed by restriction of scalars along
`AlgebraicGeometry.Space.squareZeroStructureSheafIso`. -/
def squareZeroModuleEquivalence
    (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) ≌
      SheafOfModules.{u} (smallEtaleRingSheaf B S hS X'.1 X'.2) :=
  thickeningHomModuleEquivalence B S hS hi _ |>.trans
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
        (squareZeroStructureSheafIso (hq := hq) hi h hip hpb hβτ)).symm)

end Retraction

end AlgebraicGeometry.Space

end
