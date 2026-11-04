module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothReduction
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalizationPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationDimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothNormalizationPurelyInseparable

/-!
# Lemma 0A3Q: extension by zero of `Z/ℓ` on a reduced scheme of dimension at most one

Lemma 0A3Q of the source: in Situation 0A52 with `X` reduced, for an open immersion `j : U ⟶ X`
and a prime `ℓ`, statements (1) -- (8) hold for `j_! Z/ℓ`. The proof passes to the normalization
`ν : X^ν ⟶ X`, which is finite with smooth source and an isomorphism over a dense open, and uses
Lemmas 03SG, 0A5D and 0GJA.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_isReduced`: Lemma
  0A3Q, granted Lemma 0A5B for the constant sheaf on smooth curves
  (`Stacks.EtaleCohomology.CurveStatementsConstantOnSmoothCurves`).
* `Stacks.EtaleCohomology.directImageConstantSheafIsoOfIsIso`: the direct image of a constant
  sheaf along an isomorphism of schemes is constant.
* `Stacks.EtaleCohomology.extensionByZeroCompIso`: extension by zero along a composite of open
  immersions.

## Implementation notes

**No `@[stacks 0A3Q]` attribute**: Lemma 0A5B enters as an explicit hypothesis.

The source applies Lemma 0GJA twice, once on each side of the agreement over the dense open
`X'`. Here the second application is replaced by Tag 0GJ1
(`Stacks.EtaleCohomology.directImageExtensionByZeroIso`) for the cartesian square
`ν^{-1}(U ∩ X') ⟶ X^ν` over `U ∩ X' ⟶ X`, which says that `ν_*` of the extension by zero from
`ν^{-1}(U ∩ X')` is the extension by zero from `U ∩ X'`. This avoids the constructibility of
`ν_* j^ν_! Z/ℓ` (Tag 095R), which the forward direction of Lemma 0GJA would need.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Isos

/-- The direct image of a constant sheaf along an isomorphism of schemes is constant: the unit
`G ⟶ φ_* φ^{-1} G` is invertible, as it is after `φ^{-1}` (an isomorphism is a closed
immersion) and `φ` is surjective. -/
def directImageConstantSheafIsoOfIsIso {A B : Scheme.{u}} (φ : A ⟶ B) [IsIso φ]
    (E : AddCommGrpCat.{u + 1}) :
    (etaleAbelianDirectImage.{u, 0} φ).obj ((constantSheaf A.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj E) ≅
      (constantSheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E :=
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} φ).unit.app
      ((constantSheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) :=
    isIso_of_isIso_etaleAbelianInverseImage_family.{u, 0} (fun _ : PUnit.{u + 1} ↦ φ)
      (by
        refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨PUnit.unit, ?_⟩
        exact ⟨(inv φ).base x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩)
      _ fun _ ↦ isIso_etaleAbelianInverseImage_map_unit.{u, 0} φ _
  (etaleAbelianDirectImage.{u, 0} φ).mapIso
      ((etaleAbelianInverseImageConstantIso.{u, 0} φ).app E).symm ≪≫
    (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} φ).unit.app _)).symm

/-- **Extension by zero along a composite of open immersions** is the composite of the
extensions by zero: both are left adjoint to restriction along the composite. -/
def extensionByZeroCompIso {P W X : Scheme.{u}} (q : P ⟶ W) (b : W ⟶ X) [IsOpenImmersion q]
    [IsOpenImmersion b] :
    extensionByZero.{u, 0} q ⋙ extensionByZero.{u, 0} b ≅ extensionByZero.{u, 0} (q ≫ b) :=
  Adjunction.leftAdjointUniq ((extensionByZeroAdj.{u, 0} q).comp (extensionByZeroAdj.{u, 0} b))
    ((extensionByZeroAdj.{u, 0} (q ≫ b)).ofNatIsoRight
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} (q ≫ b)).symm ≪≫
        etaleAbelianInverseImageCompIso'.{u, 0} q b (q ≫ b) rfl ≪≫
        Functor.isoWhiskerRight (etaleAbelianInverseImageRestrictionIso.{u, 0} b) _ ≪≫
        Functor.isoWhiskerLeft _ (etaleAbelianInverseImageRestrictionIso.{u, 0} q)))

/-- A scheme of finite type over a field is noetherian. -/
private theorem isNoetherian_of_quasiCompact_locallyOfFiniteType {k : Type u} [Field k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  exact ⟨⟩

end Isos

attribute [local instance] hasExt_sheaf_smallEtale_succ

section Reduced

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} (hℓ : ℓ.Prime) (E : AddCommGrpCat.{u + 1})
  (hE : Nonempty (E ≃+ ZMod ℓ))

include hℓ hE in
/-- **Stacks Project, Lemma 0A3Q, granted Lemma 0A5B for the constant sheaf.** Let `X` be a
reduced separated scheme of finite type and dimension at most one over an algebraically closed
field `k`, let `j : V ⟶ X` be an open immersion and `E` cyclic of prime order `ℓ`. If statements
(1) -- (8) of Situation 0A52 hold for the constant sheaf `E` on every smooth curve over `k`, they
hold for `j_! E`.

The normalization `ν : X^ν ⟶ X` is finite (Tag 0BXR), `X^ν` is normal of dimension at most one,
hence smooth over the perfect field `k`, and `ν` is an isomorphism over a dense open `W ⊆ X`
(`X` being reduced). With `Q = V ∩ W` and `Q^ν = ν^{-1} Q`, Tag 0GJ1 identifies `ν_*` of the
extension by zero of `E` from `Q^ν` with the extension by zero of `E` from `Q`; the former
satisfies the statements by Lemmas 03SG and 0A5D, and the latter is `j_W! j_W^{-1} (j_! E)`, so
Lemma 0GJA (the direction from `j_W! j_W^{-1}`) concludes. -/
theorem curveStatements_extensionByZero_constantSheaf_of_isReduced {X V : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (j : V ⟶ X) [IsOpenImmersion j]
    (hbase : CurveStatementsConstantOnSmoothCurves k E) :
    CurveStatements.{u, 0, u + 1} π
      ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) := by
  have := isNoetherian_of_quasiCompact_locallyOfFiniteType π
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Finite E := by obtain ⟨e⟩ := hE; exact Finite.of_equiv _ e.toEquiv.symm
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k π
  set ν := normalizationOverField k π
  have : IsFinite ν := isFinite_normalizationOverField k π
  have : IsNormal (normalizationSchemeOverField k π) := Scheme.isNormal_normalizationScheme X hX
  have hdimn : topologicalKrullDim (normalizationSchemeOverField k π) ≤ 1 :=
    topologicalKrullDim_normalizationScheme_le_one hdim hX
  have : Smooth (ν ≫ π) := smooth_of_isGeometricallyRegular k _
    (isGeometricallyRegular_of_isGeometricallyNormal_of_topologicalKrullDim_le_one k _ hdimn
      (isGeometricallyNormal_of_isNormal_of_perfectField k _))
  have := isNoetherian_of_quasiCompact_locallyOfFiniteType (ν ≫ π)
  have : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have : Finite (irreducibleComponents (normalizationSchemeOverField k π)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨W, hWd, hWiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom ν
    (Scheme.isBirational_normalization X hX) (Or.inl ⟨inferInstance, inferInstance⟩)
  set q := pullback.snd j W.ι
  set ν' := ν ∣_ W
  have hsq : IsPullback (pullback.snd q ν' ≫ (ν ⁻¹ᵁ W).ι) (pullback.fst q ν') ν (q ≫ W.ι) :=
    (IsPullback.of_hasPullback q ν').flip.paste_horiz (isPullback_morphismRestrict ν W).flip
  have : IsIso (pullback.fst q ν') := inferInstance
  -- the normalization side: `ν_*` of an extension by zero from `Q^ν`
  have hA : CurveStatements.{u, 0, u + 1} π ((etaleAbelianDirectImage.{u, 0} ν).obj
      ((extensionByZero.{u, 0} (pullback.snd q ν' ≫ (ν ⁻¹ᵁ W).ι)).obj
        ((constantSheaf (pullback q ν').smallEtaleTopology AddCommGrpCat.{u + 1}).obj E))) :=
    CurveStatements.directImage_of_nsmul_eq_zero π ν hℓ
      (nsmul_id_eq_zero_map _ (nsmul_id_constantSheaf_eq_zero _ E hE))
      (isConstructibleOnEveryBigSite_extensionByZero_constantSheaf _ E)
      (curveStatements_extensionByZero_constantSheaf_of_smooth hℓ E hE (ν ≫ π) hdimn _ hbase)
  have eA := (directImageExtensionByZeroIso (pullback.snd q ν' ≫ (ν ⁻¹ᵁ W).ι)
      (pullback.fst q ν') ν (q ≫ W.ι) hsq).app
      ((constantSheaf (pullback q ν').smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) ≪≫
    (extensionByZero.{u, 0} (q ≫ W.ι)).mapIso
      (directImageConstantSheafIsoOfIsIso (pullback.fst q ν') E)
  -- the side of `X`: `j_W! j_W^{-1} (j_! E)` is the extension by zero from `Q`
  have eB : (extensionByZero.{u, 0} W.ι).obj ((etaleRestriction.{u, 0} W.ι).obj
      ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E))) ≅
      (extensionByZero.{u, 0} (q ≫ W.ι)).obj
        ((constantSheaf (pullback j W.ι).smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) :=
    (extensionByZero.{u, 0} W.ι).mapIso
        (((etaleAbelianInverseImageRestrictionIso.{u, 0} W.ι).app _).symm ≪≫
          inverseImageExtensionByZeroConstantSheafIso j E W.ι) ≪≫
      (extensionByZeroCompIso q W.ι).app _
  exact curveStatements_of_curveStatements_extensionByZero_of_dense.{u, 0, u + 1} π hdim W.ι
    (by rwa [Scheme.Opens.range_ι]) _ ((hA.of_iso eA).of_iso eB.symm)

/-- **A finite filtration with constant graded pieces.** `HasConstantFiltration E n K` says that
the abelian sheaf `K` is built from the constant sheaf `E` by `n` successive extensions: it is
zero for `n = 0`, and for `n + 1` it is the middle term of a short exact sequence whose first
term has such a filtration of length `n` and whose last term is the constant sheaf `E`. This is
the shape of the conclusion of Tag 0A3R. -/
def HasConstantFiltration {S : Scheme.{u}} (E : AddCommGrpCat.{u + 1}) :
    ℕ → Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop
  | 0, K => IsZero K
  | n + 1, K => ∃ T : ShortComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}),
      T.ShortExact ∧ Nonempty (T.X₂ ≅ K) ∧ HasConstantFiltration E n T.X₁ ∧
        Nonempty (T.X₃ ≅ (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)

include hℓ hE in
/-- **The last step of Lemma 03SD.** On a reduced `X` as in Lemma 0A3Q, for an open immersion
`j : V ⟶ X` and a sheaf `K` on `V` with a finite filtration whose graded pieces are the constant
sheaf `E`, statements (1) -- (8) hold for `j_! K`: extension by zero is exact (Tag 03S5), so
Lemma 0A5C reduces to the graded pieces, which are Lemma 0A3Q. -/
theorem curveStatements_extensionByZero_of_hasConstantFiltration {X V : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (j : V ⟶ X) [IsOpenImmersion j]
    (hbase : CurveStatementsConstantOnSmoothCurves k E) :
    ∀ (n : ℕ) (K : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}),
      HasConstantFiltration E n K →
        CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj K) := by
  have := isNoetherian_of_quasiCompact_locallyOfFiniteType π
  intro n
  induction n with
  | zero => exact fun K hK ↦ CurveStatements.of_isZero π ((extensionByZero.{u, 0} j).map_isZero hK)
  | succ n ih =>
    rintro K ⟨T, hT, ⟨e₂⟩, h₁, ⟨e₃⟩⟩
    have := (extensionByZero_exact.{u, 0} j)
    have hT' := hT.map_of_exact (extensionByZero.{u, 0} j)
    exact (CurveStatements.of_shortExact hT' (ih _ h₁)
      ((curveStatements_extensionByZero_constantSheaf_of_isReduced hℓ E hE π hdim j hbase).of_iso
        ((extensionByZero.{u, 0} j).mapIso e₃).symm)).of_iso ((extensionByZero.{u, 0} j).mapIso e₂)

end Reduced

end Stacks.EtaleCohomology

end
