module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.DominatedCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleStabilizerHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenusZeroSimplyConnected
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.GroupTheory.CyclicKernelRelIndex
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence

/-!
# Killing `H²` with constant coefficients on a finite étale cover of a curve

Let `Z` be a smooth proper connected curve over an algebraically closed field `K`, `n` invertible
in `K`, and suppose `π₁(Z, z)` has a continuous surjection onto `ℤ/n^(e+1)` for every `e` (this
holds as soon as the genus of `Z` is at least one). Let `T ⟶ Z` be a surjective finite étale
cover and `A` a finite abelian group killed by `n`. Then every class `θ ∈ H²(T, A)` dies on some
`V ⟶ T` with `V ⟶ Z` surjective finite étale.

Proof (the trace step of Tag 03VM): pick a point `t` of the geometric fibre of `T`, a connected
cover `A'` with a point `a'` over `t` (Tag 0BND), `H = Stab(a')` of index `e`, and
`χ : π₁(Z) ↠ ℤ/n^(e+1)`. The connected cover `V` attached to `H ∩ ker χ` maps to `A'`, and the
degree of `V ⟶ A'` is the index of `Stab(v)` in `H`, which `n` divides
(`Subgroup.dvd_relIndex_inf_ker_of_surjective`). Both `A'` and `V` are smooth proper curves, so
pulling back `H²(A', A)` to `V` is zero
(`Stacks.EtaleCohomology.etaleConstantCohomologyPullback_two_eq_zero_of_dvd`).

## Main results

* `Stacks.EtaleCohomology.exists_finiteEtale_mapExactFunctor_eq_zero_of_two` — the statement.
* `Stacks.EtaleCohomology.exists_finite_etale_surjective_restriction_eq_zero_of_trivialization_two`
  — for `i : Z ⟶ Y` dominating finite étale covers and coefficients `i⁻¹G` with `G` constant on a
  finite étale cover of `Y`, a class of `H²(Z, i⁻¹G)` dies on the base change of a finite étale
  cover of `Y` (the degree-two analogue of
  `Stacks.EtaleCohomology.exists_finite_etale_surjective_restriction_eq_zero_of_trivialization`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.FundamentalGroup

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (qZ : Z ⟶ Spec (.of K))
  [IsCurve K qZ] [Smooth qZ] [IsProper qZ] [ConnectedSpace Z] (z : GeometricPoint Z)

/-- A class of `H^q` whose image under an isomorphism of coefficients is zero is zero. -/
lemma sheafH_eq_zero_of_map_isIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [IsIso φ] {q : ℕ} (y : Sheaf.H.{u + 1} F q)
    (h : Sheaf.H.map φ q y = 0) : y = 0 := by
  have h2 := congrArg (Sheaf.H.map (inv φ) q) h
  rwa [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply, map_zero] at h2

/-- A class of `H²(T, A)`, `A` finite and killed by `n`, dies on pulling back along `b ≫ a`, where
`a : X ⟶ T` and `b : Y ⟶ X` is a nonconstant morphism of smooth proper curves with
`n ∣ deg(Y/X)`. -/
theorem mapExactFunctor_comp_eq_zero_of_dvd_degreeOver {X Y T : Scheme.{u}}
    (qX : X ⟶ Spec (.of K)) (qY : Y ⟶ Spec (.of K)) [IsCurve K qX] [Smooth qX] [IsProper qX]
    [IsCurve K qY] [Smooth qY] [IsProper qY] (b : Y ⟶ X) (w : b ≫ qX = qY)
    (hnc : ¬ ∃ x : X, ∀ y : Y, b.base y = x) {n : ℕ} (hn : IsUnit (n : K))
    (hd : n ∣ @degreeOver Y X b inferInstance inferInstance
      (locallyOfFiniteType_of_isCurve_comp K qY qX b w) (isDominant_of_not_constant K qY qX b hnc))
    (a : X ⟶ T) (A : AddCommGrpCat.{u + 1}) [Finite A] (hA : ∀ a : A, n • a = 0)
    (θ : Sheaf.H.{u + 1} ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) 2) :
    θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ a)) = 0 := by
  let eA : A ≅ AddCommGrpCat.of (ULift.{u + 1} (Shrink.{0} A)) :=
    (Shrink.addEquiv.symm.trans
      (AddEquiv.ulift.{0, u + 1} (α := Shrink.{0} A)).symm).toAddCommGrpIso
  let isoA : (etaleAbelianInverseImage.{u, 0} a).obj
      ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) ≅
      etaleConstantSheaf.{u, 0} X (Shrink.{0} A) :=
    (etaleAbelianInverseImageConstantIso.{u, 0} a).app A ≪≫
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso eA
  let θ' := etaleCohomologyRestrictionMap.{u, 0, u + 1} a _ 2 θ
  have hE₀ : ∀ e : Shrink.{0} A, n • e = 0 := fun e => Shrink.addEquiv.injective (by
    rw [map_nsmul, hA, map_zero])
  have hz := etaleConstantCohomologyPullback_two_eq_zero_of_dvd qX qY b w hnc hn hE₀ hd
    (Sheaf.H.map isoA.hom 2 θ')
  simp only [etaleConstantCohomologyPullback, etaleCohomologyMapTo, AddMonoidHom.comp_apply] at hz
  rw [Stacks.Kummer.etaleCohomologyRestrictionMap_sheafHMap, ← Sheaf.H.map_comp_apply] at hz
  exact mapExactFunctor_comp_eq_zero_of_etaleCohomologyRestrictionMap a b _ θ
    ((etaleCohomologyRestrictionMap_eq_zero_iff b _ θ').1 (sheafH_eq_zero_of_map_isIso _ _ hz))

/-- The stabilizer of a point in a transitive finite étale fibre has nonzero index. -/
private theorem index_stabilizer_ne_zero_of_transitive (A' : FiniteEtaleOver Z)
    (a' : (finiteEtaleFiberFunctor z).obj A')
    (hA'tr : ∀ y, ∃ σ : EtaleFundamentalGroup Z z, σ • a' = y) :
    (MulAction.stabilizer (EtaleFundamentalGroup Z z) a').index ≠ 0 := by
  have : Finite ((finiteEtaleFiberFunctor z).obj A') := finite_finiteEtaleFiber z A'
  rw [← natCard_finiteEtaleFiber_eq_index_stabilizer z A' a' hA'tr]
  exact Nat.card_ne_zero.2 ⟨⟨a'⟩, inferInstance⟩

omit [IsAlgClosed K] [Smooth qZ] in
/-- For connected covers `V ⟶ A'` of the curve `Z` with transitive fibres, the degree of
`V ⟶ A'` is the relative index of the stabilizers. -/
theorem degreeOver_left_eq_relIndex_stabilizer {A' V : FiniteEtaleOver Z}
    [ConnectedSpace A'.left] [ConnectedSpace V.left] [IsProper (A'.hom ≫ qZ)]
    [Smooth (A'.hom ≫ qZ)] [IsCurve K (A'.hom ≫ qZ)] [IsProper (V.hom ≫ qZ)]
    [Smooth (V.hom ≫ qZ)] [IsCurve K (V.hom ≫ qZ)]
    (a' : (finiteEtaleFiberFunctor z).obj A') (v₀ : (finiteEtaleFiberFunctor z).obj V)
    (hA'tr : ∀ y, ∃ σ : EtaleFundamentalGroup Z z, σ • a' = y)
    (hVtr : ∀ y, ∃ σ : EtaleFundamentalGroup Z z, σ • v₀ = y) (f : V ⟶ A')
    (hst : MulAction.stabilizer (EtaleFundamentalGroup Z z) v₀ ≤
      MulAction.stabilizer (EtaleFundamentalGroup Z z) a')
    [LocallyOfFiniteType f.left] [IsDominant f.left] :
    degreeOver f.left = (MulAction.stabilizer (EtaleFundamentalGroup Z z) v₀).relIndex
      (MulAction.stabilizer (EtaleFundamentalGroup Z z) a') := by
  have : Finite ((finiteEtaleFiberFunctor z).obj A') := finite_finiteEtaleFiber z A'
  have : Finite ((finiteEtaleFiberFunctor z).obj V) := finite_finiteEtaleFiber z V
  have hcardA := natCard_finiteEtaleFiber_eq_index_stabilizer z A' a' hA'tr
  have hHAi := index_stabilizer_ne_zero_of_transitive z A' a' hA'tr
  have hb : f.left ≫ A'.hom = V.hom := MorphismProperty.Over.w f
  have w : f.left ≫ (A'.hom ≫ qZ) = V.hom ≫ qZ := by rw [← Category.assoc, hb]
  have := locallyOfFiniteType_of_isCurve_comp K (A'.hom ≫ qZ) qZ A'.hom rfl
  have := isDominant_of_not_constant K (A'.hom ≫ qZ) qZ A'.hom (not_constant_finiteEtaleOver qZ A')
  have := locallyOfFiniteType_of_isCurve_comp K (V.hom ≫ qZ) qZ V.hom rfl
  have := isDominant_of_not_constant K (V.hom ≫ qZ) qZ V.hom (not_constant_finiteEtaleOver qZ V)
  have : LocallyOfFiniteType (f.left ≫ A'.hom) := hb ▸ inferInstance
  have hdA : degreeOver A'.hom = (MulAction.stabilizer (EtaleFundamentalGroup Z z) a').index :=
    (degreeOver_eq_natCard_finiteEtaleFiber z qZ A').trans hcardA
  have hdV : degreeOver V.hom = (MulAction.stabilizer (EtaleFundamentalGroup Z z) v₀).index :=
    (degreeOver_eq_natCard_finiteEtaleFiber z qZ V).trans
      (natCard_finiteEtaleFiber_eq_index_stabilizer z V v₀ hVtr)
  have hfe := finiteEtale_left f
  have : IsFinite f.left := hfe.1
  have : Etale f.left := hfe.2
  let Vb : FiniteEtaleOver A'.left :=
    MorphismProperty.Over.mk ⊤ f.left ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace Vb.left := (inferInstance : ConnectedSpace V.left)
  have : IsProper (Vb.hom ≫ (A'.hom ≫ qZ)) := by
    show IsProper (f.left ≫ (A'.hom ≫ qZ))
    rw [w]
    infer_instance
  have : IsCurve K (Vb.hom ≫ (A'.hom ≫ qZ)) := by
    show IsCurve K (f.left ≫ (A'.hom ≫ qZ))
    rw [w]
    infer_instance
  obtain ⟨a₀⟩ : Nonempty A'.left := ConnectedSpace.toNonempty
  let ā := GeometricPoint.ofPoint A'.left a₀
  have : Finite ((finiteEtaleFiberFunctor ā).obj Vb) := finite_finiteEtaleFiber ā Vb
  have := nonempty_finiteEtaleFiber_of_nonempty_left ā Vb
  have hbpos : 0 < degreeOver f.left := by
    rw [show degreeOver f.left = _ from
      degreeOver_eq_natCard_finiteEtaleFiber ā (A'.hom ≫ qZ) Vb]
    exact Nat.card_pos
  have hcomp := degreeOver_comp_of_pos f.left A'.hom hbpos (hdA ▸ Nat.pos_of_ne_zero hHAi)
  rw [degreeOver_congr hb, hdV, hdA] at hcomp
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hHAi)
    (hcomp.symm.trans (Subgroup.relIndex_mul_index hst).symm)

include qZ in
/-- **`H²` with constant finite coefficients on a finite étale cover of a curve dies on a further
finite étale cover**, provided `π₁(Z, z)` surjects continuously onto `ℤ/n^(e+1)` for every `e`. -/
theorem exists_finiteEtale_mapExactFunctor_eq_zero_of_two {n : ℕ} (hn : IsUnit (n : K))
    (hχ : ∀ e : ℕ, ∃ χ : EtaleFundamentalGroup Z z →* Multiplicative (ZMod (n ^ (e + 1))),
      IsOpen (χ.ker : Set (EtaleFundamentalGroup Z z)) ∧ Function.Surjective χ)
    {T : Scheme.{u}} (s : T ⟶ Z) [IsFinite s] [Etale s] [Surjective s]
    (A : AddCommGrpCat.{u + 1}) [Finite A] (hA : ∀ a : A, n • a = 0)
    (θ : Sheaf.H.{u + 1} ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) 2) :
    ∃ (V : Scheme.{u}) (v : V ⟶ T), IsFinite (v ≫ s) ∧ Etale (v ≫ s) ∧ Surjective (v ≫ s) ∧
      θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} v) = 0 := by
  classical
  have : NeZero n := ⟨Stacks.Kummer.neZero_of_isUnit hn⟩
  let G := EtaleFundamentalGroup Z z
  let T' : FiniteEtaleOver Z := MorphismProperty.Over.mk ⊤ s ⟨inferInstance, inferInstance⟩
  obtain ⟨z₀⟩ : Nonempty Z := ConnectedSpace.toNonempty
  have : Nonempty T'.left := ⟨(s.surjective z₀).choose⟩
  obtain ⟨t⟩ := nonempty_finiteEtaleFiber_of_nonempty_left z T'
  let Ht : OpenSubgroup G := ⟨MulAction.stabilizer G t,
    EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨T', t, rfl⟩⟩
  obtain ⟨A', a', hA'tr, hA'st⟩ := exists_finiteEtaleOver_transitive_stabilizer_le z Ht
  obtain ⟨fA, -⟩ := exists_hom_finiteEtaleOver_of_stabilizer_le z A' T' a' t hA'tr
    (fun σ hσ => hA'st σ hσ)
  let HA : Subgroup G := MulAction.stabilizer G a'
  have hHAo : IsOpen (HA : Set G) :=
    EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨A', a', rfl⟩
  have : HA.FiniteIndex := ⟨index_stabilizer_ne_zero_of_transitive z A' a' hA'tr⟩
  obtain ⟨χ, hχo, hχs⟩ := hχ HA.index
  let HB : OpenSubgroup G := ⟨HA ⊓ χ.ker, hHAo.inter hχo⟩
  obtain ⟨V, v₀, hVtr, hVst⟩ := exists_finiteEtaleOver_transitive_stabilizer_le z HB
  obtain ⟨fV, -⟩ := exists_hom_finiteEtaleOver_of_stabilizer_le z V A' v₀ a' hVtr
    (fun σ hσ => (hVst σ hσ).1)
  have : ConnectedSpace A'.left := connectedSpace_left_of_exists_smul_eq hA'tr
  have : ConnectedSpace V.left := connectedSpace_left_of_exists_smul_eq hVtr
  obtain ⟨_, _, -, _⟩ := isCurve_comp_of_isAlgClosed K qZ A'
  obtain ⟨_, _, -, _⟩ := isCurve_comp_of_isAlgClosed K qZ V
  have hb : fV.left ≫ A'.hom = V.hom := MorphismProperty.Over.w fV
  have w : fV.left ≫ (A'.hom ≫ qZ) = V.hom ≫ qZ := by rw [← Category.assoc, hb]
  have hnc : ¬ ∃ a : A'.left, ∀ x : V.left, fV.left.base x = a := by
    rintro ⟨a, ha⟩
    exact not_constant_finiteEtaleOver qZ V ⟨A'.hom.base a, fun x => by
      rw [← hb, Scheme.Hom.comp_apply, ha]⟩
  have := locallyOfFiniteType_of_isCurve_comp K (V.hom ≫ qZ) (A'.hom ≫ qZ) fV.left w
  have := isDominant_of_not_constant K (V.hom ≫ qZ) (A'.hom ≫ qZ) fV.left hnc
  have hVB : MulAction.stabilizer G v₀ ≤ HB.toSubgroup := fun σ hσ => hVst σ hσ
  have hBA : HB.toSubgroup ≤ HA := inf_le_left
  have hdvd : n ∣ degreeOver fV.left := by
    rw [degreeOver_left_eq_relIndex_stabilizer qZ z a' v₀ hA'tr hVtr fV (hVB.trans hBA),
      ← Subgroup.relIndex_mul_relIndex _ _ _ hVB hBA]
    exact Dvd.dvd.mul_left (Subgroup.dvd_relIndex_inf_ker_of_surjective HA n χ hχs) _
  let a : A'.left ⟶ T := fA.left
  have hv : (fV.left ≫ a) ≫ s = V.hom := by
    rw [Category.assoc, show a ≫ s = A'.hom from MorphismProperty.Over.w fA, hb]
  refine ⟨V.left, fV.left ≫ a, ?_, ?_, ?_,
    mapExactFunctor_comp_eq_zero_of_dvd_degreeOver (A'.hom ≫ qZ) (V.hom ≫ qZ) fV.left w hnc hn
      hdvd a A hA θ⟩ <;> rw [hv]
  exacts [V.prop.1, V.prop.2, ⟨surjective_of_finiteEtale V⟩]

include qZ in
/-- **The degree-two effacement on a curve.** Let `i : Z ⟶ Y` dominate finite étale covers, with
`Z` a smooth proper connected curve over an algebraically closed field whose fundamental group
surjects continuously onto `ℤ/n^(e+1)` for every `e`, and `G` an abelian sheaf on `Y` whose
inverse image to a surjective finite étale `p : T ⟶ Y` is constant with finite value killed by
`n`. Then every class of `H²(Z, i⁻¹G)` dies on the base change `W ×_Y Z` of some surjective
finite étale `W ⟶ Y`. -/
theorem exists_finite_etale_surjective_restriction_eq_zero_of_trivialization_two
    {Y : Scheme.{u}} [ConnectedSpace Y] (i : Z ⟶ Y) (hi : DominatesFiniteEtale i) {n : ℕ}
    (hn : IsUnit (n : K))
    (hχ : ∀ e : ℕ, ∃ χ : EtaleFundamentalGroup Z z →* Multiplicative (ZMod (n ^ (e + 1))),
      IsOpen (χ.ker : Set (EtaleFundamentalGroup Z z)) ∧ Function.Surjective χ)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) {T : Scheme.{u}} (p : T ⟶ Y)
    [IsFinite p] [Etale p] [Surjective p] (A : AddCommGrpCat.{u + 1}) [Finite A]
    (hA : ∀ a : A, n • a = 0)
    (e : (etaleAbelianInverseImage.{u, 0} p).obj G ≅
      (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) 2) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Y), IsFinite π ∧ Etale π ∧ Surjective π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) _ 2 ξ = 0 := by
  let s := pullback.snd p i
  let e' : (etaleAbelianInverseImage.{u, 0} s).obj ((etaleAbelianInverseImage.{u, 0} i).obj G) ≅
      (constantSheaf (pullback p i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    ((etaleAbelianInverseImageCompIso'.{u, 0} s i (s ≫ i) rfl).app G).symm ≪≫
      (etaleAbelianInverseImageCompIso'.{u, 0} (pullback.fst p i) p (s ≫ i)
        pullback.condition.symm).app G ≪≫
      (etaleAbelianInverseImage.{u, 0} (pullback.fst p i)).mapIso e ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst p i)).app A
  let r := etaleCohomologyRestrictionMap.{u, 0, u + 1} s _ 2 ξ
  obtain ⟨V, v, _, _, _, hk⟩ :=
    exists_finiteEtale_mapExactFunctor_eq_zero_of_two qZ z hn hχ s A hA (Sheaf.H.map e'.hom 2 r)
  have hr : r.mapExactFunctor (etaleAbelianInverseImage.{u, 0} v) = 0 := by
    rw [Sheaf.H.map_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at hk
    have h' := congrArg (fun y => y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} v).map
      e'.inv)) (add_zero 2)) hk
    simp only [Ext.zero_comp] at h'
    rwa [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id] at h'
  exact exists_finite_etale_surjective_restriction_eq_zero_of_dominatesFiniteEtale i hi _ ξ
    (v ≫ s) (mapExactFunctor_comp_eq_zero_of_etaleCohomologyRestrictionMap s v _ ξ hr)

end Stacks.EtaleCohomology

end
