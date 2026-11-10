module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# Fibre products of normal schemes over a field

The fibre product over a field of a geometrically normal scheme with a normal scheme is normal.

## Main results

* `AlgebraicGeometry.algebra_isGeometricallyNormal_sections`: the sections of a geometrically
  normal scheme over an affine open form a geometrically normal algebra over the base field.
* `AlgebraicGeometry.isNormal_pullback_of_isGeometricallyNormal`: normality of a fibre product
  over a field when one factor is geometrically normal and the other is normal.

## Implementation notes

The fibre product over the field is the categorical pullback of the two structure morphisms to
its spectrum. Both results are affine-local: the opens `fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V`, for `U` and `V`
affine opens of the two factors, are affine and cover the pullback, and their rings of sections
are the tensor products `Γ(X, U) ⊗[k] Γ(Y, V)` — this identification is
`affineProduct_sections_equiv`, obtained by comparing the pullback of the two restricted
structure morphisms with the spectrum of the tensor product. Normality of the fibre product then
follows from Tag 06DF, the ring-theoretic statement that a geometrically normal algebra stays
normal after tensoring with a normal ring.

Geometric normality of the scheme over `k` is the definition of Tag 038M: after every field
extension `K / k` the stalks of the base change are normal rings. To convert that into geometric
normality of the sections over an affine open `U` — the condition of Tag 0380, which is what Tag
06DF consumes — one has to know that the base change of `U` is `Spec (Γ(X, U) ⊗[k] K)`, which is
`affineBaseChangeIso`. This is the implication (1) ⇒ (5) of Tag 038O; only that implication is
proved here, and no characterization of geometric normality is needed for it.

## References

* [Stacks Project, Tag 038O](https://stacks.math.columbia.edu/tag/038O)
* [Stacks Project, Tag 06DG](https://stacks.math.columbia.edu/tag/06DG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-
`AlgebraicGeometry.isNormal_spec_iff` lived here and was a duplicate of the lemma of the same
full name in `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/NormalTFAE.lean:86`, a file
this one imports; that one is now public and is the survivor.
-/

/-! ### Base change of an affine open -/

/-- The canonical algebra structure on the sections of `X` over an open `U`, induced by a
structure morphism `f : X ⟶ Spec k`. -/
public noncomputable abbrev sectionsAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra

/-- On an affine open `U`, the structure morphism of `Spec Γ(X, U)` over `k` is the restriction
of `f` along `hU.fromSpec`. -/
private lemma specMap_algebraMap_sections_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Spec.map (ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f := by
  let := sectionsAlgebra f U
  change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)) = hU.fromSpec ≫ f
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU (by simp),
    Spec.map_comp, IsAffineOpen.fromSpec_top]
  congr 1
  rw [← cancel_mono (Spec (.of k)).toSpecΓ]
  simp

/-- On an affine open `U`, the isomorphism `U ≅ Spec Γ(X, U)` is over `Spec k`. -/
private lemma isoSpec_hom_specMap_algebraMap_sections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    hU.isoSpec.hom ≫ Spec.map (ofHom (algebraMap k Γ(X, U))) = U.ι ≫ f := by
  let := sectionsAlgebra f U
  rw [specMap_algebraMap_sections_eq f hU, ← Category.assoc, hU.isoSpec_hom_fromSpec]

/-- Over an affine open `U` of a scheme `X` over a field `k`, the base change of `U` along a
field extension `K / k` is the spectrum of `Γ(X, U) ⊗[k] K`. -/
private noncomputable def affineBaseChangeIso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    (pullback U.ι (pullback.fst f (Spec.map (ofHom (algebraMap k K)))) : Scheme.{u}) ≅
      Spec (.of (Γ(X, U) ⊗[k] K)) := by
  letI := sectionsAlgebra f U
  let g := Spec.map (ofHom (algebraMap k K))
  have eU : pullback U.ι (pullback.fst f g) ≅ pullback hU.fromSpec (pullback.fst f g) := by
    let m := pullback.map U.ι (pullback.fst f g) hU.fromSpec (pullback.fst f g)
      hU.isoSpec.hom (𝟙 _) (𝟙 _) hU.isoSpec_hom_fromSpec.symm (by simp)
    let n := pullback.map hU.fromSpec (pullback.fst f g) U.ι (pullback.fst f g)
      hU.isoSpec.inv (𝟙 _) (𝟙 _) hU.isoSpec_inv_ι.symm (by simp)
    refine ⟨m, n, ?_, ?_⟩ <;> refine pullback.hom_ext ?_ ?_ <;> dsimp [m, n, pullback.map] <;>
      simp [Category.assoc]
  exact eU.trans <| (pullbackRightPullbackFstIso f g hU.fromSpec).trans <|
    (pullback.congrHom (specMap_algebraMap_sections_eq f hU).symm rfl).trans
      (pullbackSpecIso k Γ(X, U) K)

/-! ### Geometric normality on affine opens -/

/-- **Stacks Project, Tag 038O**, the implication (1) ⇒ (5): the sections of a geometrically
normal scheme over a field `k` on an affine open form a geometrically normal `k`-algebra. -/
public theorem algebra_isGeometricallyNormal_sections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : IsGeometricallyNormal f) (U : X.affineOpens) :
    letI := sectionsAlgebra f U.1
    Algebra.IsGeometricallyNormal k Γ(X, U.1) := by
  let : Algebra k Γ(X, U.1) := sectionsAlgebra f U.1
  refine ⟨fun K _ _ ↦ ?_⟩
  let fst := pullback.fst f (Spec.map (ofHom (algebraMap k K)))
  have : IsNormal (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme.{u}) :=
    (AlgebraicGeometry.isNormal_iff_stalk_isNormalRing _).2 fun y ↦ hf (fst y) K y rfl
  have : IsNormal (fst ⁻¹ᵁ (U.1 : X.Opens)).toScheme := isNormal_open _
  have : IsNormal (Spec (.of (Γ(X, U.1) ⊗[k] K))) :=
    AlgebraicGeometry.isNormal_of_iso (((isPullback_morphismRestrict fst U.1).isoPullback.trans
      (affineBaseChangeIso k f K U.1 U.2)).symm)
  exact IsNormalRing.congr (Algebra.TensorProduct.comm k Γ(X, U.1) K).toRingEquiv
    (isNormal_spec_iff.mp inferInstance)

/-! ### The fibre product -/

/-- On an affine open of the form `fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V` the sections of a fibre product over a
field `k` are the tensor product over `k` of the sections of the two factors. -/
private noncomputable def affineProduct_sections_equiv {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (U : X.affineOpens) (V : Y.affineOpens) :
    letI := sectionsAlgebra f U.1
    letI := sectionsAlgebra g V.1
    Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) ≃+*
      Γ(X, U.1) ⊗[k] Γ(Y, V.1) := by
  letI := sectionsAlgebra f U.1
  letI := sectionsAlgebra g V.1
  let W := pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1
  let i := pullback.map (U.1.ι ≫ f) (V.1.ι ≫ g) f g U.1.ι V.1.ι (𝟙 _) (by simp) (by simp)
  have hW' : Set.range i = Set.range W.ι := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange,
      Scheme.Pullback.range_map (U.1.ι ≫ f) (V.1.ι ≫ g) f g U.1.ι V.1.ι (𝟙 _) (by simp) (by simp),
      Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  let eOpen : pullback (U.1.ι ≫ f) (V.1.ι ≫ g) ≅ W.toScheme :=
    IsOpenImmersion.isoOfRangeEq i W.ι hW'
  let mPull := pullback.map (U.1.ι ≫ f) (V.1.ι ≫ g)
    (Spec.map (ofHom (algebraMap k Γ(X, U.1)))) (Spec.map (ofHom (algebraMap k Γ(Y, V.1))))
    U.2.isoSpec.hom V.2.isoSpec.hom (𝟙 _)
    (isoSpec_hom_specMap_algebraMap_sections f U.2).symm
    (isoSpec_hom_specMap_algebraMap_sections g V.2).symm
  have : IsIso mPull := pullback.map_isIso ..
  have hWι : W.ι ''ᵁ ⊤ = W := by
    ext x
    simp
  exact ((((pullback f g).presheaf.mapIso (eqToIso hWι).op) ≪≫
      Scheme.Hom.appIso W.ι ⊤).commRingCatIsoToRingEquiv).trans
    ((Scheme.Γ.mapIso (eOpen.symm ≪≫ asIso mPull ≪≫
        pullbackSpecIso k Γ(X, U.1) Γ(Y, V.1)).op).symm.commRingCatIsoToRingEquiv.trans
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⊗[k] Γ(Y, V.1)))).commRingCatIsoToRingEquiv)

/-- **Stacks Project, Tag 06DG.** The fibre product over a field of a geometrically normal
scheme and a normal scheme is normal. -/
@[stacks 06DG,
  ega "IV 6.14.1" "base = Spec of a field",
  ega "IV 21.14.4" "more general",
  ega "IV 7.3.9" "more general"]
public theorem isNormal_pullback_of_isGeometricallyNormal {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (hX : IsGeometricallyNormal f) [IsNormal Y] :
    IsNormal (pullback f g : Scheme.{u}) := by
  let W : X.affineOpens × Y.affineOpens → (pullback f g : Scheme.{u}).Opens := fun q =>
    pullback.fst f g ⁻¹ᵁ q.1.1 ⊓ pullback.snd f g ⁻¹ᵁ q.2.1
  have hcover : IsOpenCover W := by
    refine IsOpenCover.mk (eq_top_iff.2 fun z _ ↦ ?_)
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp
      (show (pullback.fst f g).base z ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) by
        rw [iSup_affineOpens_eq_top]; simp)
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp
      (show (pullback.snd f g).base z ∈ (⨆ V : Y.affineOpens, (V.1 : Y.Opens)) by
        rw [iSup_affineOpens_eq_top]; simp)
    exact Opens.mem_iSup.mpr ⟨(U, V), hU, hV⟩
  have hAffine : ∀ q : X.affineOpens × Y.affineOpens, IsAffineOpen (W q) := fun q ↦ by
    have : IsAffine q.1.1.toScheme := q.1.2
    have : IsAffine q.2.1.toScheme := q.2.2
    have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top _
    exact isAffineOpen_inf_preimage f g (S₀ := ⊤) le_top le_top
  have hYsections : ∀ V : Y.affineOpens, IsNormalRing Γ(Y, V.1) :=
    ((isNormal_tfae Y).out 1 2).mp ‹IsNormal Y›
  have key : ∃ (I : Type u) (V : I → (pullback f g : Scheme.{u}).affineOpens),
      IsOpenCover (fun i ↦ ((V i : (pullback f g : Scheme.{u}).Opens))) ∧
        ∀ i, IsNormalRing Γ(pullback f g, V i) := by
    refine ⟨X.affineOpens × Y.affineOpens, fun q ↦ ⟨W q, hAffine q⟩, hcover, fun q ↦ ?_⟩
    let : Algebra k Γ(X, q.1.1) := sectionsAlgebra f q.1.1
    let : Algebra k Γ(Y, q.2.1) := sectionsAlgebra g q.2.1
    have : Algebra.IsGeometricallyNormal k Γ(X, q.1.1) :=
      algebra_isGeometricallyNormal_sections f hX q.1
    exact IsNormalRing.congr (affineProduct_sections_equiv f g q.1 q.2).symm
      (Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_isNormalRing
        k Γ(X, q.1.1) Γ(Y, q.2.1) (hYsections q.2))
  exact ((isNormal_tfae (pullback f g : Scheme.{u})).out 3 1).mp key

end AlgebraicGeometry

end
