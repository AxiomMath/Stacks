module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveTopSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeGeometricPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections

/-!
# `R² f_* μ_n ≅ ℤ/n` for a smooth proper family of curves

Let `f : X ⟶ S` be proper, smooth of relative dimension one, with geometrically irreducible
fibres, and `n` invertible on `X`. Then the sheaf `R² f_* μ_n = H⁰(Rf_*(μ_n[2]))` of abelian groups
on `S_étale` is isomorphic to the constant sheaf `ℤ/n`
(`Stacks.EtaleCohomology.nonempty_constantSheaf_zmod_iso_relativeTopSheaf`).

The generating section `τ : ℤ_S ⟶ R² f_* μ_n` of `Stacks.EtaleCohomology.exists_relativeTopSection`
factors through `ℤ/n_S`, and the factorization is an isomorphism, as it is at every geometric point
of `S` over a point of `X`: over the spectrum `Spec Ω` of a separably closed field, morphisms out
of `ℤ_Ω` are global sections, global sections are an equivalence, the morphisms `ℤ_Ω ⟶ ℤ/n` form a
group of order `n`, and the restriction of `τ` is a generator of order `n`
(`Stacks.EtaleCohomology.isIso_of_isZModGenerator`).

## Main results

* `Stacks.EtaleCohomology.isIso_of_bijective_comp_intSheaf`: over a separably closed field, a
  morphism of sheaves is an isomorphism when postcomposition with it is bijective on morphisms
  out of `ℤ`.
* `Stacks.EtaleCohomology.natCard_hom_intSheaf_constantSheaf`.
* `Stacks.EtaleCohomology.isIso_of_isZModGenerator`.
* `Stacks.EtaleCohomology.nonempty_constantSheaf_zmod_iso_relativeTopSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

section SepClosed

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- The final object of the small étale site of `Spec Ω`. -/
theorem isTerminal_etale_mk_id : Nonempty (IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) := by
  have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))).hom :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of Ω))))
  exact ⟨isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))⟩

/-- Morphisms out of `ℤ` over `Spec Ω` are the sections over the final object. -/
def homIntSheafEquivSections (P : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (intSheaf (Spec (.of Ω)) ⟶ P) ≃
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).obj P :=
  ((constantSheafAdj (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminal_etale_mk_id Ω).some).homEquiv _ _).trans
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom _).symm)

omit [IsSepClosed Ω] in
/-- `homIntSheafEquivSections` is natural in the target sheaf. -/
theorem homIntSheafEquivSections_comp {P Q : Sheaf (Spec (.of Ω)).smallEtaleTopology
    AddCommGrpCat.{u + 1}} (g : intSheaf (Spec (.of Ω)) ⟶ P) (w : P ⟶ Q) :
    homIntSheafEquivSections Ω Q (g ≫ w) =
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).map w (homIntSheafEquivSections Ω P g) := by
  simp only [homIntSheafEquivSections, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- **Over a separably closed field, a morphism of sheaves which is bijective on morphisms out of
`ℤ` is an isomorphism**: morphisms out of `ℤ` are sections over the final object, and taking those
is an equivalence. -/
theorem isIso_of_bijective_comp_intSheaf
    {M N : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}} (w : M ⟶ N)
    (h : Function.Bijective (fun g : intSheaf (Spec (.of Ω)) ⟶ M => g ≫ w)) : IsIso w := by
  have := isEquivalence_sheafSections_final_of_isSepClosed Ω AddCommGrpCat.{u + 1}
  let E := (sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  have key : (E.map w : E.obj M → E.obj N) =
      homIntSheafEquivSections Ω N ∘ (fun g => g ≫ w) ∘ (homIntSheafEquivSections Ω M).symm := by
    funext a
    simp only [Function.comp_apply, homIntSheafEquivSections_comp, Equiv.apply_symm_apply]
    rfl
  have : IsIso (E.map w) := (ConcreteCategory.isIso_iff_bijective _).2 <| by
    rw [key]
    exact (homIntSheafEquivSections Ω N).bijective.comp
      (h.comp (homIntSheafEquivSections Ω M).symm.bijective)
  exact isIso_of_reflects_iso w E

omit [IsSepClosed Ω] in
/-- **The morphisms `ℤ ⟶ A` of constant sheaves over `Spec Ω` are the elements of `A`.** -/
theorem natCard_hom_intSheaf_constantSheaf (A : Type (u + 1)) [AddCommGroup A] :
    Nat.card (intSheaf (Spec (.of Ω)) ⟶
      (constantSheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)) = Nat.card A := by
  rw [Nat.card_congr (homIntSheafEquivSections Ω _)]
  let e := ((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, 0} (Spec (.of Ω)) A).app
    (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).addCommGroupIsoToAddEquiv
  refine (Nat.card_congr (e.toEquiv.trans
    (Equiv.refl (LocallyConstant (Spec (.of Ω)) A)))).trans ?_
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine Nat.card_congr
    { toFun := fun g => g p
      invFun := fun a => LocallyConstant.const _ a
      left_inv := fun g => LocallyConstant.ext fun q => by
        rw [Subsingleton.elim q p]
        rfl
      right_inv := fun a => rfl }

end SepClosed

section Criterion

variable {S X : Scheme.{u}} (p : X ⟶ S) [Surjective p] {n : ℕ} [NeZero n]

/-- The inverse image of the constant sheaf `ℤ`, identified with `ℤ`. -/
abbrev intSheafInverseImageIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (etaleAbelianInverseImage.{u, 0} g).obj (intSheaf Z) ≅ intSheaf Y :=
  (etaleAbelianInverseImageConstantIso.{u, 0} g).app (AddCommGrpCat.of (ULift ℤ))

/-- **A criterion for a morphism out of a constant sheaf to be an isomorphism.** Let
`p : X ⟶ S` be surjective and `v : A ⟶ G` a morphism of abelian sheaves on `S` with
`ε ≫ v = τ` for `ε : ℤ_S ⟶ A`, `τ : ℤ_S ⟶ G`. Suppose that at the geometric point `x̄` of every
point `x` of `X` (algebraic closure of the residue field), the morphisms `ℤ ⟶ x̄⁻¹p⁻¹A` form a
group of order `n`, and the restriction of `τ` generates the group of morphisms
`ℤ ⟶ x̄⁻¹p⁻¹G` as a cyclic group of order `n`. Then `v` is an isomorphism. -/
theorem isIso_of_isZModGenerator {A G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (v : A ⟶ G) (ε : intSheaf S ⟶ A) (τ : intSheaf S ⟶ G) (hv : ε ≫ v = τ)
    (hA : ∀ x : X, Nat.card (intSheaf (Spec (.of (GeometricPoint.ofPoint X x).residueField)) ⟶
      (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint X x).hom).obj
        ((etaleAbelianInverseImage.{u, 0} p).obj A)) = n)
    (hG : ∀ x : X, IsZModGenerator n
      ((intSheafInverseImageIso (GeometricPoint.ofPoint X x).hom).inv ≫
        (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint X x).hom).map
          ((intSheafInverseImageIso p).inv ≫ (etaleAbelianInverseImage.{u, 0} p).map τ))) :
    IsIso v := by
  refine isIso_of_geometricStalkAb_family
    (Ω := fun x : X => (GeometricPoint.ofPoint X x).residueField)
    (fun x : X => (GeometricPoint.ofPoint X x).hom ≫ p) ?_ v (fun x => ?_)
  · refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨x, rfl⟩ := p.surjective s
    exact Set.mem_iUnion.2 ⟨x, ⟨default, by
      rw [Scheme.Hom.comp_apply, GeometricPoint.ofPoint_liesOver]⟩⟩
  refine isIso_stalk_of_isIso_etaleAbelianInverseImage_map
    (GeometricPoint.mk (GeometricPoint.ofPoint X x).residueField
      ((GeometricPoint.ofPoint X x).hom ≫ p)) v ?_
  refine (NatIso.isIso_map_iff (etaleAbelianInverseImageCompIso.{u, 0}
    (GeometricPoint.ofPoint X x).hom p) v).2 ?_
  set y := (GeometricPoint.ofPoint X x).hom
  change IsIso ((etaleAbelianInverseImage.{u, 0} y).map ((etaleAbelianInverseImage.{u, 0} p).map v))
  refine isIso_of_bijective_comp_intSheaf _ _ ?_
  obtain ⟨e, he⟩ := hG x
  let D := fun {B : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (t : intSheaf S ⟶ B) => (intSheafInverseImageIso y).inv ≫
    (etaleAbelianInverseImage.{u, 0} y).map
      ((intSheafInverseImageIso p).inv ≫ (etaleAbelianInverseImage.{u, 0} p).map t)
  set g := D τ
  set d := D ε
  have hd : d ≫ (etaleAbelianInverseImage.{u, 0} y).map
      ((etaleAbelianInverseImage.{u, 0} p).map v) = g := by
    simp only [D, d, g, Category.assoc, ← Functor.map_comp, hv]
  have hsurj : Function.Surjective
      (fun z : intSheaf (Spec (.of (GeometricPoint.ofPoint X x).residueField)) ⟶
        (etaleAbelianInverseImage.{u, 0} y).obj ((etaleAbelianInverseImage.{u, 0} p).obj A) =>
          z ≫ (etaleAbelianInverseImage.{u, 0} y).map
            ((etaleAbelianInverseImage.{u, 0} p).map v)) := by
    intro c
    refine ⟨(e c).val • d, ?_⟩
    have hc : c = (e c).val • g := e.injective (by
      rw [map_nsmul, he, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
    simp only [Preadditive.nsmul_comp, hd]
    exact hc.symm
  have : Finite (intSheaf (Spec (.of (GeometricPoint.ofPoint X x).residueField)) ⟶
      (etaleAbelianInverseImage.{u, 0} y).obj ((etaleAbelianInverseImage.{u, 0} p).obj A)) :=
    Nat.finite_of_card_ne_zero (by rw [hA x]; exact NeZero.ne n)
  refine hsurj.bijective_of_nat_card_le ?_
  rw [hA x, Nat.card_congr e.toEquiv, Nat.card_zmod]

end Criterion

section Family

attribute [local instance] HasDerivedCategory.standard

variable {S X : Scheme.{u}} (f : X ⟶ S) {n : ℕ}

include f in
/-- `R² f_* μ_n` is killed by `n`. -/
theorem nsmul_id_relativeTopSheaf : n • 𝟙 (relativeTopSheaf f n) = 0 := by
  have : (etaleAbelianDerivedDirectImage.{u, 0} f).Additive :=
    (etaleAbelianDerivedAdjunction.{u, 0} f).right_adjoint_additive
  have h := Stacks.Kummer.nsmul_id_rootsOfUnitySheaf_univ.{u, u + 1} X n
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id,
    ← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
    ← Functor.map_nsmul, ← Functor.map_nsmul, ← Functor.map_nsmul, h]
  simp

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]

/-- **`R² f_* μ_n ≅ ℤ/n`** for `f : X ⟶ S` proper, smooth of relative dimension one, with
geometrically irreducible fibres, and `n ≥ 1` invertible on `X`, as sheaves of abelian groups on
`S_étale`. -/
theorem nonempty_constantSheaf_zmod_iso_relativeTopSheaf [NeZero n]
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤))) :
    Nonempty ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≅ relativeTopSheaf f n) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨τ, hτ⟩ := exists_relativeTopSection f hn0 hX hY
  let adj := constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u + 1}
    (etaleSiteTerminalIsTerminal S)
  let E := (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (etaleSiteTerminal S))
  let sec := adj.homEquiv _ _ τ (ULift.up 1)
  have hs : (zmultiplesHom (E.obj (relativeTopSheaf f n)) sec) (n : ℤ) = 0 := by
    rw [zmultiplesHom_apply, natCast_zsmul]
    have h1 : E.map (n • 𝟙 (relativeTopSheaf f n)) sec = n • sec := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl
    rw [← h1, nsmul_id_relativeTopSheaf f]
    simp
  let q₀ : ULift.{u + 1} ℤ →+ ULift.{u + 1} (ZMod n) :=
    AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom)
  let ψ₀ : ULift.{u + 1} (ZMod n) →+ E.obj (relativeTopSheaf f n) :=
    (ZMod.lift n ⟨zmultiplesHom _ sec, hs⟩).comp AddEquiv.ulift.toAddMonoidHom
  let ε : intSheaf S ⟶ (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :=
    (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom q₀)
  let v := (adj.homEquiv _ _).symm (AddCommGrpCat.ofHom ψ₀)
  have hv : ε ≫ v = τ := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    apply AddCommGrpCat.hom_ext
    apply (uliftZMultiplesHom _).symm.injective
    change ψ₀ (q₀ (ULift.up 1)) = sec
    suffices h : ψ₀ (q₀ (ULift.up 1)) = AddEquiv.ulift (ULift.up.{u + 1} (1 : ℤ)) • sec from
      h.trans (one_zsmul _)
    simp [ψ₀, q₀]
  refine ⟨@asIso _ _ _ _ v
    (isIso_of_isZModGenerator (n := n) f v ε τ hv (fun x => ?_) (fun x => ?_))⟩
  · let B := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
    let i := (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint X x).hom).mapIso
        ((etaleAbelianInverseImageConstantIso.{u, 0} f).app B) ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} (GeometricPoint.ofPoint X x).hom).app B
    refine (Nat.card_congr (Iso.homCongr (Iso.refl _) i)).trans ?_
    rw [natCard_hom_intSheaf_constantSheaf, Nat.card_ulift, Nat.card_zmod]
  · have hx : IsUnit (n : (GeometricPoint.ofPoint X x).residueField) := by
      have := (hX.map ((X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom)).map
        (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))
      rwa [map_natCast, map_natCast] at this
    rw [hτ]
    exact isZModGenerator_relativeTopEdge f hn0 hX hY _ hx

end Family

end Stacks.EtaleCohomology

end
