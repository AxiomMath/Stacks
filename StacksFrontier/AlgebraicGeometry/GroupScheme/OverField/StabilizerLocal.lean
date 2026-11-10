module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerRepresentable
public import StacksFrontier.RingTheory.TensorProduct.CoordinateIdeal
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.PullbackNormal

/-!
# Right stabilisers of a function: the local computation

Let `G` be a group scheme over a field `k`, `U` an affine open of `G` and `f ∈ Γ(U)`.  For a
`T`-point `h` of `G`, `AlgebraicGeometry.RightStabilises h U f` says that `f` and its right
translate by `h` agree where both are defined.  This file computes this condition on product
charts `U ×_k V` (`V` an affine open of `T`), following Perrin (thesis I §2, IV §1):

* `Γ(U ×_k V) ≅ Γ(U) ⊗[k] Γ(V)` (`AlgebraicGeometry.prodOpenTensorIso`), naturally in `T`;
* the condition is local on `T` (`AlgebraicGeometry.rightStabilises_iff_forall_rightStabilisesOn`,
  `AlgebraicGeometry.rightStabilises_of_forall_exists`);
* given a non-zero-divisor `b` of `Γ(U ×_k V)` with `D(b)` inside the stabiliser locus, and
  `num = b^N (ρ^* f − pr^* f)` on `D(b)`, the condition on the chart is `num = 0`
  (`AlgebraicGeometry.rightStabilisesOn_iff_eq_zero`), and this data base changes
  (`AlgebraicGeometry.rightStabilisesOn_comp_iff`);
* for universal data (`AlgebraicGeometry.StabilizerChartData`, on charts of `G ×_k G`) whose `b`
  is nonzero in every fibre, and `Γ(U)` geometrically integral, the content lemma makes `b` a
  non-zero-divisor after every base change, so a point `φ` stabilises on `U ×_k V'` iff `φ^*`
  kills the finitely generated coordinate ideal of `num`
  (`AlgebraicGeometry.StabilizerChartData.rightStabilisesOn_iff`);
* such data exist near every point when `G` is geometrically irreducible and `U` nonempty
  (`AlgebraicGeometry.exists_stabilizerChartData`).

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, I §2 and IV §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {G T T' : Over (Spec (.of k))} [GrpObj G]

/-- The open `U ×_k V` of `G ×_k T` for opens `U` of `G` and `V` of `T`. -/
noncomputable def prodOpen (U : G.left.Opens) (V : T.left.Opens) : (G ⊗ T).left.Opens :=
  (fst G T).left ⁻¹ᵁ U ⊓ (snd G T).left ⁻¹ᵁ V

omit [GrpObj G] in
/-- The open `U ×_k V` lies in the preimage of `U` under the first projection. -/
theorem prodOpen_le_fst (U : G.left.Opens) (V : T.left.Opens) :
    prodOpen U V ≤ (fst G T).left ⁻¹ᵁ U :=
  inf_le_left

omit [GrpObj G] in
/-- The open `U ×_k V` lies in the preimage of `V` under the second projection. -/
theorem prodOpen_le_snd (U : G.left.Opens) (V : T.left.Opens) :
    prodOpen U V ≤ (snd G T).left ⁻¹ᵁ V :=
  inf_le_right

/-- The structure map `k ⟶ Γ(X, U)` of a scheme over `Spec k`, on an open `U`. -/
noncomputable def sectionsStructureMap (X : Over (Spec (.of k))) (U : X.left.Opens) :
    CommRingCat.of k ⟶ Γ(X.left, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U (by simp)

omit [GrpObj G] in
/-- **The sections over `U ×_k V` are the pushout of the sections over `U` and over `V`**, for
affine opens `U` of `G` and `V` of `T` over a field `k`. -/
theorem isPushout_prodOpen {U : G.left.Opens} {V : T.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    IsPushout (sectionsStructureMap G U) (sectionsStructureMap T V)
      ((fst G T).left.appLE U (prodOpen U V) (prodOpen_le_fst U V))
      ((snd G T).left.appLE V (prodOpen U V) (prodOpen_le_snd U V)) := by
  have hfield : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k))
  have H := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
    (IsPullback.of_hasPullback G.hom T.hom) (US := ⊤) (UT := V) (UX := U)
    (UY := prodOpen U V) le_top le_top rfl (isAffineOpen_top _) hV.isCompact
    hV.isQuasiSeparated hU.isCompact hU.isQuasiSeparated (RingHom.Flat.of_isField hfield _)
  have H' := (isIso_pushoutSection_iff _ _ _ _).mp H
  exact H'.of_iso (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [sectionsStructureMap]) (by simp [sectionsStructureMap]) (by simp) (by simp)

/-- **Restriction to a basic open of a non-zero-divisor is injective.**  Let `Y` be an affine open
of a scheme, `b` a non-zero-divisor of `Γ(Y)` and `W ⊆ Y` an open containing `D(b)`.  Then a
section over `W` vanishing on `D(b)` vanishes: locally on a basic open `D(c) ⊆ W` the restriction
`Γ(D(c)) ⟶ Γ(D(cb))` is the localization at the image of `b`, still a non-zero-divisor. -/
theorem Scheme.injective_res_basicOpen_of_mem_nonZeroDivisors {X : Scheme.{u}} {Y : X.Opens}
    (hY : IsAffineOpen Y) {b : Γ(X, Y)} (hb : b ∈ nonZeroDivisors Γ(X, Y)) {W : X.Opens}
    (hWY : W ≤ Y) (hbW : X.basicOpen b ≤ W) :
    Function.Injective (X.presheaf.map (homOfLE hbW).op).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext X.sheaf W s 0 fun x hx ↦ ?_
  obtain ⟨c, hcW, hxc⟩ := hY.exists_basicOpen_le ⟨x, hx⟩ (hWY hx)
  have hcY : X.basicOpen c ≤ Y := X.basicOpen_le c
  let s' := X.presheaf.map (homOfLE hcW).op s
  have hc := hY.basicOpen c
  let b' := X.presheaf.map (homOfLE hcY).op b
  have hb' : b' ∈ nonZeroDivisors Γ(X, X.basicOpen c) := by
    let := hY.isLocalization_basicOpen c
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers c) _ hb
  have hbb' : X.basicOpen b' = X.basicOpen c ⊓ X.basicOpen b := Scheme.basicOpen_res _ _ _
  have hle : X.basicOpen b' ≤ X.basicOpen c := X.basicOpen_le b'
  have hinj : Function.Injective (X.presheaf.map (homOfLE hle).op).hom := by
    let := hc.isLocalization_basicOpen b'
    exact IsLocalization.injective (M := Submonoid.powers b') _
      (Submonoid.powers_le.mpr hb')
  have hzero : X.presheaf.map (homOfLE hle).op s' = 0 := by
    have hle' : X.basicOpen b' ≤ X.basicOpen b := hbb' ▸ inf_le_right
    have e1 : X.presheaf.map (homOfLE hle).op s' =
        X.presheaf.map (homOfLE hle').op (X.presheaf.map (homOfLE hbW).op s) := by
      simp only [s', ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [e1, hs, map_zero]
  have hs' : s' = 0 := hinj (hzero.trans (map_zero _).symm)
  have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hcW) x hxc s
  rw [map_zero]
  refine this.symm.trans ?_
  change X.presheaf.germ _ x hxc s' = 0
  rw [hs', map_zero]

omit [GrpObj G] in
/-- `U ×_k V` is affine for affine opens `U` and `V`. -/
theorem isAffineOpen_prodOpen {U : G.left.Opens} {V : T.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (prodOpen U V) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsAffine (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  exact .of_isIso (Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback G.hom T.hom)
    (US := ⊤) (UT := V) (UX := U) (UY := prodOpen U V) le_top le_top rfl).isoPullback.hom

/-- **`Γ(U) ⊗[k] Γ(V) ≅ Γ(U ×_k V)`** for affine opens `U` of `G` and `V` of `T`. -/
noncomputable def prodOpenTensorIso {U : G.left.Opens} {V : T.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    letI := sectionsAlgebra G.hom U
    letI := sectionsAlgebra T.hom V
    CommRingCat.of (Γ(G.left, U) ⊗[k] Γ(T.left, V)) ≅ Γ((G ⊗ T).left, prodOpen U V) :=
  letI := sectionsAlgebra G.hom U
  letI := sectionsAlgebra T.hom V
  (CommRingCat.isPushout_tensorProduct k Γ(G.left, U) Γ(T.left, V)).isoIsPushout _ _
    (isPushout_prodOpen hU hV)

omit [GrpObj G] in
/-- The isomorphism `Γ(U) ⊗[k] Γ(V) ≅ Γ(U ×_k V)` sends `c ⊗ₜ a` to the product of the pullbacks
of `c` and `a` along the two projections. -/
theorem prodOpenTensorIso_tmul {U : G.left.Opens} {V : T.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (c : Γ(G.left, U)) (a : Γ(T.left, V)) :
    letI := sectionsAlgebra G.hom U
    letI := sectionsAlgebra T.hom V
    (prodOpenTensorIso hU hV).hom (c ⊗ₜ a) =
      (fst G T).left.appLE U (prodOpen U V) (prodOpen_le_fst U V) c *
        (snd G T).left.appLE V (prodOpen U V) (prodOpen_le_snd U V) a := by
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra T.hom V
  have h1 := congr($((CommRingCat.isPushout_tensorProduct k Γ(G.left, U)
    Γ(T.left, V)).inl_isoIsPushout_hom
    _ _ (isPushout_prodOpen hU hV)).hom c)
  have h2 := congr($((CommRingCat.isPushout_tensorProduct k Γ(G.left, U)
    Γ(T.left, V)).inr_isoIsPushout_hom
    _ _ (isPushout_prodOpen hU hV)).hom a)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  have hca : c ⊗ₜ[k] a = (c ⊗ₜ[k] (1 : Γ(T.left, V))) * ((1 : Γ(G.left, U)) ⊗ₜ[k] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hca, map_mul]
  exact congrArg₂ (· * ·) h1 h2

/-- The structure maps `k ⟶ Γ(V)` are compatible with restriction along a morphism over
`Spec k`. -/
theorem sectionsStructureMap_comp (φ : T' ⟶ T) (V : T.left.Opens) (V' : T'.left.Opens)
    (h : V' ≤ φ.left ⁻¹ᵁ V) :
    sectionsStructureMap T V ≫ φ.left.appLE V V' h = sectionsStructureMap T' V' := by
  rw [sectionsStructureMap, sectionsStructureMap, Category.assoc, Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact Scheme.Hom.appLE_congr_hom (Over.w φ) _ _ _ _

/-- The map of sections along a morphism over `Spec k`, as a `k`-algebra map. -/
noncomputable def sectionsAlgHom (φ : T' ⟶ T) (V : T.left.Opens) (V' : T'.left.Opens)
    (h : V' ≤ φ.left ⁻¹ᵁ V) :
    letI := sectionsAlgebra T.hom V
    letI := sectionsAlgebra T'.hom V'
    Γ(T.left, V) →ₐ[k] Γ(T'.left, V') :=
  letI := sectionsAlgebra T.hom V
  letI := sectionsAlgebra T'.hom V'
  { (φ.left.appLE V V' h).hom with
    commutes' := fun r ↦ congrArg (fun m ↦ m.hom r) (sectionsStructureMap_comp φ V V' h) }

/-- `sectionsAlgHom φ V V' h` acts on sections as `φ.left.appLE V V' h`. -/
theorem sectionsAlgHom_apply (φ : T' ⟶ T) (V : T.left.Opens) (V' : T'.left.Opens)
    (h : V' ≤ φ.left ⁻¹ᵁ V) (a : Γ(T.left, V)) :
    sectionsAlgHom φ V V' h a = φ.left.appLE V V' h a :=
  rfl

omit [GrpObj G] in
/-- If `V' ≤ φ⁻¹ V`, then `U ×_k V'` lies in the preimage of `U ×_k V` under the base change
`G ×_k T' ⟶ G ×_k T`. -/
theorem prodOpen_le_preimage (φ : T' ⟶ T) (U : G.left.Opens) (V : T.left.Opens)
    (V' : T'.left.Opens) (h : V' ≤ φ.left ⁻¹ᵁ V) :
    prodOpen U V' ≤ (stabilizerBaseChange (G := G) φ).left ⁻¹ᵁ prodOpen U V := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change ((stabilizerBaseChange φ ≫ fst G T).left) x ∈ U
    rw [stabilizerBaseChange_fst]
    exact hx.1
  · change ((stabilizerBaseChange φ ≫ snd G T).left) x ∈ V
    rw [show stabilizerBaseChange (G := G) φ ≫ snd G T = snd G T' ≫ φ from lift_snd _ _]
    exact h hx.2

omit [GrpObj G] in
/-- **The tensor identification is natural in the parameter.**  Along `φ : T' ⟶ T` with
`V' ⊆ φ⁻¹ V`, pulling sections of `U ×_k V` back to `U ×_k V'` is `id ⊗ φ^*`. -/
theorem prodOpenTensorIso_naturality (φ : T' ⟶ T) {U : G.left.Opens} {V : T.left.Opens}
    {V' : T'.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ φ.left ⁻¹ᵁ V)
    (x : letI := sectionsAlgebra G.hom U; letI := sectionsAlgebra T.hom V
      Γ(G.left, U) ⊗[k] Γ(T.left, V)) :
    letI := sectionsAlgebra G.hom U
    letI := sectionsAlgebra T.hom V
    letI := sectionsAlgebra T'.hom V'
    (stabilizerBaseChange φ).left.appLE (prodOpen U V) (prodOpen U V')
        (prodOpen_le_preimage φ U V V' h) ((prodOpenTensorIso hU hV).hom x) =
      (prodOpenTensorIso hU hV').hom
        (Algebra.TensorProduct.map (AlgHom.id k _) (sectionsAlgHom φ V V' h) x) := by
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra T.hom V
  let := sectionsAlgebra T'.hom V'
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [prodOpenTensorIso_tmul, Algebra.TensorProduct.map_tmul, prodOpenTensorIso_tmul, map_mul]
    congr 1
    · rw [AlgHom.id_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_congr_hom
        ((Over.comp_left _ _ _ _ _).symm.trans
          (congrArg Over.Hom.left (stabilizerBaseChange_fst φ))) _ _ _ _) c
    · rw [sectionsAlgHom_apply, ← CommRingCat.comp_apply,
        Scheme.Hom.appLE_comp_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_congr_hom
        ((Over.comp_left _ _ _ _ _).symm.trans
          ((congrArg Over.Hom.left (lift_snd (fst G T') (snd G T' ≫ φ))).trans
            (Over.comp_left _ _ _ _ _))) _ _ _ _) a
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The stabiliser condition on a product chart, through a non-zero-divisor -/

/-- The part of the stabiliser locus over the product chart `U ×_k V`. -/
noncomputable def stabilizerChart (h : T ⟶ G) (U : G.left.Opens) (V : T.left.Opens) :
    (G ⊗ T).left.Opens :=
  rightStabilizerLocus h U ⊓ prodOpen U V

/-- The stabiliser chart lies in the preimage of `U` under the first projection. -/
theorem stabilizerChart_le_fst (h : T ⟶ G) (U : G.left.Opens) (V : T.left.Opens) :
    stabilizerChart h U V ≤ (fst G T).left ⁻¹ᵁ U :=
  inf_le_left.trans (rightStabilizerLocus_le_fst h U)

/-- The stabiliser chart lies in the preimage of `U` under right translation by `h`. -/
theorem stabilizerChart_le_rightTranslate (h : T ⟶ G) (U : G.left.Opens) (V : T.left.Opens) :
    stabilizerChart h U V ≤ (rightTranslate h).left ⁻¹ᵁ U :=
  inf_le_left.trans (rightStabilizerLocus_le_rightTranslate h U)

/-- `h` right-stabilises `f` on the part of the locus over the product chart `U ×_k V`. -/
def RightStabilisesOn (h : T ⟶ G) (U : G.left.Opens) (V : T.left.Opens) (f : Γ(G.left, U)) :
    Prop :=
  (fst G T).left.appLE U (stabilizerChart h U V) (stabilizerChart_le_fst h U V) f =
    (rightTranslate h).left.appLE U (stabilizerChart h U V)
      (stabilizerChart_le_rightTranslate h U V) f

/-- Right stabilisation holds if every point of `G ×_k T` lies over a point of `V` such that `h`
right-stabilises `f` on the chart `U ×_k V`. -/
private theorem rightStabilises_of_forall_rightStabilisesOn (h : T ⟶ G) (U : G.left.Opens)
    (f : Γ(G.left, U))
    (H : ∀ x : (G ⊗ T).left, ∃ V : T.left.Opens, (snd G T).left x ∈ V ∧ RightStabilisesOn h U V f) :
    RightStabilises h U f := by
  refine TopCat.Presheaf.section_ext (G ⊗ T).left.sheaf _ _ _ fun x hx ↦ ?_
  obtain ⟨V, hxV', hst⟩ := H x
  have hxV : x ∈ stabilizerChart h U V := ⟨hx, rightStabilizerLocus_le_fst h U hx, hxV'⟩
  have hle : stabilizerChart h U V ≤ rightStabilizerLocus h U := inf_le_left
  have e := congrArg ((G ⊗ T).left.presheaf.germ _ x hxV).hom hst
  have h1 := TopCat.Presheaf.germ_res_apply (G ⊗ T).left.presheaf (homOfLE hle) x hxV
    ((fst G T).left.appLE U (rightStabilizerLocus h U) (rightStabilizerLocus_le_fst h U) f)
  have h2 := TopCat.Presheaf.germ_res_apply (G ⊗ T).left.presheaf (homOfLE hle) x hxV
    ((rightTranslate h).left.appLE U (rightStabilizerLocus h U)
      (rightStabilizerLocus_le_rightTranslate h U) f)
  have m1 : (G ⊗ T).left.presheaf.map (homOfLE hle).op
      ((fst G T).left.appLE U (rightStabilizerLocus h U) (rightStabilizerLocus_le_fst h U) f) =
      (fst G T).left.appLE U (stabilizerChart h U V) (stabilizerChart_le_fst h U V) f := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have m2 : (G ⊗ T).left.presheaf.map (homOfLE hle).op
      ((rightTranslate h).left.appLE U (rightStabilizerLocus h U)
        (rightStabilizerLocus_le_rightTranslate h U) f) =
      (rightTranslate h).left.appLE U (stabilizerChart h U V)
        (stabilizerChart_le_rightTranslate h U V) f := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rw [m1] at h1
  rw [m2] at h2
  exact h1.symm.trans (e.trans h2)

/-- **Right stabilisation is checked on the product charts.** -/
theorem rightStabilises_iff_forall_rightStabilisesOn (h : T ⟶ G) (U : G.left.Opens)
    (f : Γ(G.left, U)) :
    RightStabilises h U f ↔ ∀ V : T.left.affineOpens, RightStabilisesOn h U V f := by
  constructor
  · intro hst V
    have e := congrArg ((G ⊗ T).left.presheaf.map
      (homOfLE (inf_le_left : stabilizerChart h U V ≤ _)).op).hom hst
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at e
    exact e
  · intro hst
    refine rightStabilises_of_forall_rightStabilisesOn h U f fun x ↦ ?_
    obtain ⟨V, hVa, hxV', -⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top ((snd G T).left x))
    exact ⟨V, hxV', hst ⟨V, hVa⟩⟩

/-- **Right stabilisation is local on the parameter scheme**: it suffices that every point of `T`
has an affine neighbourhood `V` on whose chart `U ×_k V` the condition holds. -/
theorem rightStabilises_of_forall_exists (h : T ⟶ G) (U : G.left.Opens) (f : Γ(G.left, U))
    (H : ∀ t : T.left, ∃ V : T.left.Opens, IsAffineOpen V ∧ t ∈ V ∧ RightStabilisesOn h U V f) :
    RightStabilises h U f :=
  rightStabilises_of_forall_rightStabilisesOn h U f fun x ↦ by
    obtain ⟨V, -, hxV', hst⟩ := H ((snd G T).left x)
    exact ⟨V, hxV', hst⟩

/-- **The stabiliser condition on a chart is the vanishing of one element.**  Let `b` be a
non-zero-divisor of `Γ(U ×_k V)` with `D(b)` inside the stabiliser locus, and `num` a section of
`U ×_k V` whose restriction to `D(b)` is `b^N (ρ^* f − pr^* f)`.  Then `h` right-stabilises `f` on
the chart if and only if `num = 0`. -/
theorem rightStabilisesOn_iff_eq_zero (h : T ⟶ G) {U : G.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (f : Γ(G.left, U))
    (b : Γ((G ⊗ T).left, prodOpen U V)) (hb : b ∈ nonZeroDivisors Γ((G ⊗ T).left, prodOpen U V))
    (hbW : (G ⊗ T).left.basicOpen b ≤ rightStabilizerLocus h U)
    (num : Γ((G ⊗ T).left, prodOpen U V)) (N : ℕ)
    (hnum : (G ⊗ T).left.presheaf.map (homOfLE ((G ⊗ T).left.basicOpen_le b)).op num =
      (G ⊗ T).left.presheaf.map (homOfLE ((G ⊗ T).left.basicOpen_le b)).op b ^ N *
        ((rightTranslate h).left.appLE U ((G ⊗ T).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_rightTranslate h U))) f -
          (fst G T).left.appLE U ((G ⊗ T).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_fst h U))) f)) :
    RightStabilisesOn h U V f ↔ num = 0 := by
  let X := (G ⊗ T).left
  have hY := isAffineOpen_prodOpen hU hV
  have hbC : X.basicOpen b ≤ stabilizerChart h U V := le_inf hbW (X.basicOpen_le b)
  have hinjnum : Function.Injective
      (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom := by
    let := hY.isLocalization_basicOpen b
    exact IsLocalization.injective (M := Submonoid.powers b) _ (Submonoid.powers_le.mpr hb)
  have hinjC := Scheme.injective_res_basicOpen_of_mem_nonZeroDivisors hY hb
    (inf_le_right : stabilizerChart h U V ≤ prodOpen U V) hbC
  have hunit := RingedSpace.isUnit_res_basicOpen X.toRingedSpace b
  have resF : X.presheaf.map (homOfLE hbC).op
      ((fst G T).left.appLE U (stabilizerChart h U V) (stabilizerChart_le_fst h U V) f) =
      (fst G T).left.appLE U (X.basicOpen b) (hbW.trans (rightStabilizerLocus_le_fst h U)) f := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have resR : X.presheaf.map (homOfLE hbC).op
      ((rightTranslate h).left.appLE U (stabilizerChart h U V)
        (stabilizerChart_le_rightTranslate h U V) f) =
      (rightTranslate h).left.appLE U (X.basicOpen b)
        (hbW.trans (rightStabilizerLocus_le_rightTranslate h U)) f := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  unfold RightStabilisesOn
  refine ⟨fun hst ↦ hinjnum ?_, fun h0 ↦ hinjC ?_⟩
  · rw [hnum, map_zero, ← resF, ← resR, hst, sub_self, mul_zero]
  · rw [h0, map_zero] at hnum
    have hdiff := (hunit.pow N).mul_right_eq_zero.mp hnum.symm
    exact resF.trans ((sub_eq_zero.mp hdiff).symm.trans resR.symm)

/-! ### Base change of the chart data -/

/-- If `a ≫ g = g'`, then restricting along `g` and then along `a` is restricting along `g'`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_appLE_of_comp_eq {X Y Z : Scheme.{u}}
    {a : X ⟶ Y} {g : Y ⟶ Z} {g' : X ⟶ Z} (hg : a ≫ g = g') {U : Z.Opens} {V : Y.Opens}
    {V' : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e : V' ≤ a ⁻¹ᵁ V) (e₂ : V' ≤ g' ⁻¹ᵁ U) (x : Γ(Z, U)) :
    a.appLE V V' e (g.appLE U V e₁ x) = g'.appLE U V' e₂ x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_congr_hom hg _ _ _ _) x

/-- The right stabiliser locus of `φ ≫ h` is the preimage of that of `h` under the base change
`G ×_k T' ⟶ G ×_k T`. -/
theorem rightStabilizerLocus_comp (φ : T' ⟶ T) (h : T ⟶ G) (U : G.left.Opens) :
    rightStabilizerLocus (φ ≫ h) U =
      (stabilizerBaseChange φ).left ⁻¹ᵁ rightStabilizerLocus h U := by
  ext x
  change (fst G T').left x ∈ U ∧ (rightTranslate (φ ≫ h)).left x ∈ U ↔
    ((stabilizerBaseChange φ ≫ fst G T).left) x ∈ U ∧
      ((stabilizerBaseChange φ ≫ rightTranslate h).left) x ∈ U
  rw [stabilizerBaseChange_fst, stabilizerBaseChange_rightTranslate]

/-- The basic open of the restriction of `r` along `a` lies in the preimage of `D(r)`. -/
theorem basicOpen_appLE_le {X Y : Scheme.{u}} (a : X ⟶ Y) {V : Y.Opens} {V' : X.Opens}
    (e : V' ≤ a ⁻¹ᵁ V) (r : Γ(Y, V)) :
    X.basicOpen (a.appLE V V' e r) ≤ a ⁻¹ᵁ Y.basicOpen r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res,
    ← Scheme.preimage_basicOpen]
  exact inf_le_right

/-- **The chart data base change.**  If `(b, num, N)` satisfies the hypotheses of
`AlgebraicGeometry.rightStabilisesOn_iff_eq_zero` for `h` on the chart `U ×_k V`, then for
`φ : T' ⟶ T` with `V' ⊆ φ⁻¹ V` and the pulled-back `b` a non-zero-divisor on `U ×_k V'`, the
composite `φ ≫ h` right-stabilises `f` on `U ×_k V'` iff the pull-back of `num` vanishes. -/
theorem rightStabilisesOn_comp_iff (h : T ⟶ G) (φ : T' ⟶ T) {U : G.left.Opens}
    {V : T.left.Opens} {V' : T'.left.Opens} (hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (hφ : V' ≤ φ.left ⁻¹ᵁ V) (f : Γ(G.left, U))
    (b : Γ((G ⊗ T).left, prodOpen U V))
    (hbW : (G ⊗ T).left.basicOpen b ≤ rightStabilizerLocus h U)
    (num : Γ((G ⊗ T).left, prodOpen U V)) (N : ℕ)
    (hnum : (G ⊗ T).left.presheaf.map (homOfLE ((G ⊗ T).left.basicOpen_le b)).op num =
      (G ⊗ T).left.presheaf.map (homOfLE ((G ⊗ T).left.basicOpen_le b)).op b ^ N *
        ((rightTranslate h).left.appLE U ((G ⊗ T).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_rightTranslate h U))) f -
          (fst G T).left.appLE U ((G ⊗ T).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_fst h U))) f))
    (hb' : (stabilizerBaseChange φ).left.appLE (prodOpen U V) (prodOpen U V')
      (prodOpen_le_preimage φ U V V' hφ) b ∈ nonZeroDivisors Γ((G ⊗ T').left, prodOpen U V')) :
    RightStabilisesOn (φ ≫ h) U V' f ↔
      (stabilizerBaseChange φ).left.appLE (prodOpen U V) (prodOpen U V')
        (prodOpen_le_preimage φ U V V' hφ) num = 0 := by
  let m := (stabilizerBaseChange (G := G) φ).left
  let e := prodOpen_le_preimage (G := G) φ U V V' hφ
  let b' := m.appLE (prodOpen U V) (prodOpen U V') e b
  let X := (G ⊗ T).left
  let X' := (G ⊗ T').left
  have hb'le : X'.basicOpen b' ≤ m ⁻¹ᵁ X.basicOpen b := basicOpen_appLE_le m e b
  have hbW' : X'.basicOpen b' ≤ rightStabilizerLocus (φ ≫ h) U := by
    rw [rightStabilizerLocus_comp]
    exact hb'le.trans (m.preimage_mono hbW)
  refine rightStabilisesOn_iff_eq_zero (φ ≫ h) hU hV' f b' hb' hbW' _ N ?_
  have hm := congrArg (m.appLE (X.basicOpen b) (X'.basicOpen b') hb'le) hnum
  have e1 : ∀ x : Γ(X, prodOpen U V),
      m.appLE (X.basicOpen b) (X'.basicOpen b') hb'le
        (X.presheaf.map (homOfLE (X.basicOpen_le b)).op x) =
      X'.presheaf.map (homOfLE (X'.basicOpen_le b')).op
        (m.appLE (prodOpen U V) (prodOpen U V') e x) := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]
  rw [map_mul, map_pow, map_sub, e1, e1,
    Scheme.Hom.appLE_appLE_of_comp_eq (congrArg Over.Hom.left
      (stabilizerBaseChange_rightTranslate φ h)) _ _
      (hbW'.trans (rightStabilizerLocus_le_rightTranslate (φ ≫ h) U)),
    Scheme.Hom.appLE_appLE_of_comp_eq (congrArg Over.Hom.left (stabilizerBaseChange_fst φ)) _ _
      (hbW'.trans (rightStabilizerLocus_le_fst (φ ≫ h) U))] at hm
  exact hm

/-! ### The universal chart data and the coordinate ideal -/

/-- **Universal chart data** for the right stabiliser of `f ∈ Γ(U)`: on the chart `U ×_k V` of
`G ×_k G` (the universal point `𝟙 G`), a section `b` with `D(b)` in the stabiliser locus which is
nonzero in every fibre over `V`, and `num = b^N (μ^* f − pr^* f)` on `D(b)`. -/
structure StabilizerChartData (U : G.left.Opens) (V : G.left.Opens) (f : Γ(G.left, U)) where
  /-- The section cutting out the dense open of the chart. -/
  b : Γ((G ⊗ G).left, prodOpen U V)
  /-- Its basic open lies in the stabiliser locus of the universal point. -/
  hbW : (G ⊗ G).left.basicOpen b ≤ rightStabilizerLocus (𝟙 G) U
  /-- The numerator of the translate difference. -/
  num : Γ((G ⊗ G).left, prodOpen U V)
  /-- The power of `b` clearing the denominator. -/
  N : ℕ
  /-- `num` is `b^N (μ^* f − pr^* f)` on `D(b)`. -/
  hnum : (G ⊗ G).left.presheaf.map (homOfLE ((G ⊗ G).left.basicOpen_le b)).op num =
      (G ⊗ G).left.presheaf.map (homOfLE ((G ⊗ G).left.basicOpen_le b)).op b ^ N *
        ((rightTranslate (𝟙 G)).left.appLE U ((G ⊗ G).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_rightTranslate (𝟙 G) U))) f -
          (fst G G).left.appLE U ((G ⊗ G).left.basicOpen b)
            ((hbW.trans (rightStabilizerLocus_le_fst (𝟙 G) U))) f)

variable {U V : G.left.Opens} {f : Γ(G.left, U)}

/-- The coordinate ideal of the chart data, an ideal of `Γ(G, V)`. -/
noncomputable def StabilizerChartData.ideal (D : StabilizerChartData U V f) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : Ideal Γ(G.left, V) :=
  letI := sectionsAlgebra G.hom U
  letI := sectionsAlgebra G.hom V
  TensorProduct.coordIdeal Γ(G.left, U) ((prodOpenTensorIso hU hV).inv D.num)

/-- The coordinate ideal of the chart data is finitely generated. -/
theorem StabilizerChartData.ideal_fg (D : StabilizerChartData U V f) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : (D.ideal hU hV).FG := by
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra G.hom V
  exact TensorProduct.coordIdeal_fg _

/-- **Local representability of the right stabiliser.**  Let `D` be universal chart data on
`U ×_k V` whose `b` is not nilpotent in any fibre over `V`, where every zero divisor of every
`Γ(U) ⊗[k] κ` (`κ` a field over `k`) is nilpotent (the hypothesis of Perrin's content lemma;
automatic when `Γ(U)` is geometrically integral).  Then
for every `φ : T ⟶ G` and every affine `V' ⊆ φ⁻¹ V`, `φ` right-stabilises `f` on the chart
`U ×_k V'` if and only if `φ^* : Γ(V) ⟶ Γ(V')` kills the coordinate ideal of `D`. -/
theorem StabilizerChartData.rightStabilisesOn_iff (D : StabilizerChartData U V f)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    (hfib : letI := sectionsAlgebra G.hom U; letI := sectionsAlgebra G.hom V
      ∀ p : PrimeSpectrum Γ(G.left, V), ¬ IsNilpotent
        (Algebra.TensorProduct.map (AlgHom.id k Γ(G.left, U))
          (IsScalarTower.toAlgHom k Γ(G.left, V) p.asIdeal.ResidueField)
          ((prodOpenTensorIso hU hV).inv D.b)))
    (φ : T ⟶ G) {V' : T.left.Opens} (hV' : IsAffineOpen V') (hφ : V' ≤ φ.left ⁻¹ᵁ V) :
    letI := sectionsAlgebra G.hom V
    letI := sectionsAlgebra T.hom V'
    RightStabilisesOn φ U V' f ↔ D.ideal hU hV ≤ RingHom.ker (sectionsAlgHom φ V V' hφ) := by
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra G.hom V
  let := sectionsAlgebra T.hom V'
  have nat := prodOpenTensorIso_naturality (G := G) φ hU hV hV' hφ
  have hb' : (stabilizerBaseChange φ).left.appLE (prodOpen U V) (prodOpen U V')
      (prodOpen_le_preimage φ U V V' hφ) D.b ∈ nonZeroDivisors _ := by
    have h1 := nat ((prodOpenTensorIso hU hV).inv D.b)
    simp only [Iso.inv_hom_id_apply] at h1
    rw [h1]
    have hz := TensorProduct.map_mem_nonZeroDivisors_of_forall_not_isNilpotent hC
      (sectionsAlgHom φ V V' hφ) _ hfib
    rw [← MulEquivClass.map_nonZeroDivisors (prodOpenTensorIso hU hV').commRingCatIsoToRingEquiv]
    exact ⟨_, hz, rfl⟩
  have key := rightStabilisesOn_comp_iff (𝟙 G) φ hU hV hV' hφ f D.b D.hbW D.num D.N D.hnum hb'
  rw [Category.comp_id] at key
  rw [key, StabilizerChartData.ideal, ← TensorProduct.map_eq_zero_iff_coordIdeal_le_ker]
  have h2 := nat ((prodOpenTensorIso hU hV).inv D.num)
  simp only [Iso.inv_hom_id_apply] at h2
  rw [h2]
  constructor
  · intro h0
    have := congrArg (prodOpenTensorIso hU hV').inv.hom h0
    simpa only [Iso.hom_inv_id_apply, map_zero] using this
  · intro h0
    rw [h0, map_zero]


/-- The basic open of the restriction of `r` along `a : X ⟶ Y` to `V'` is `V' ⊓ a⁻¹ D(r)`. -/
theorem basicOpen_appLE_eq {X Y : Scheme.{u}} (a : X ⟶ Y) {V : Y.Opens} {V' : X.Opens}
    (e : V' ≤ a ⁻¹ᵁ V) (r : Γ(Y, V)) :
    X.basicOpen (a.appLE V V' e r) = V' ⊓ a ⁻¹ᵁ Y.basicOpen r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res,
    ← Scheme.preimage_basicOpen]

omit [GrpObj G] in
/-- The base change `G ×_k T' ⟶ G ×_k T` followed by the second projection is the second
projection followed by `φ`. -/
theorem stabilizerBaseChange_snd (φ : T' ⟶ T) :
    stabilizerBaseChange (G := G) φ ≫ snd G T = snd G T' ≫ φ :=
  lift_snd _ _

omit [GrpObj G] in
/-- **`G ×_k T'` is the base change of `G ×_k T ⟶ T` along `φ : T' ⟶ T`.** -/
theorem isPullback_stabilizerBaseChange (φ : T' ⟶ T) :
    IsPullback (stabilizerBaseChange (G := G) φ).left (snd G T').left (snd G T).left φ.left := by
  have hB : IsPullback (fst G T).left (snd G T).left G.hom T.hom :=
    IsPullback.of_hasPullback G.hom T.hom
  have hA : IsPullback ((stabilizerBaseChange (G := G) φ).left ≫ (fst G T).left) (snd G T').left
      G.hom (φ.left ≫ T.hom) :=
    (IsPullback.of_hasPullback G.hom T'.hom).of_eq
      ((congrArg Over.Hom.left (stabilizerBaseChange_fst φ)).symm.trans
        (Over.comp_left _ _ _ _ _)) rfl rfl (Over.w φ).symm
  refine IsPullback.of_right hA ?_ hB
  exact (Over.comp_left _ _ _ _ _).symm.trans ((congrArg Over.Hom.left
    (stabilizerBaseChange_snd φ)).trans (Over.comp_left _ _ _ _ _))

/-! ### Existence of chart data near every point -/

/-- **Universal chart data exist near every point.**  For a geometrically irreducible group
scheme `G` over `k`, a nonempty affine open `U` and `f ∈ Γ(U)`, every point of `G` has an affine
neighbourhood `V` carrying universal chart data whose `b` is not nilpotent in any fibre over
`V`. -/
theorem exists_stabilizerChartData [GeometricallyIrreducible G.hom] (hU : IsAffineOpen U)
    (hne : (U : Set G.left).Nonempty) (f : Γ(G.left, U)) (v : G.left) :
    ∃ (V : G.left.Opens) (hV : IsAffineOpen V), v ∈ V ∧ ∃ D : StabilizerChartData U V f,
      letI := sectionsAlgebra G.hom U
      letI := sectionsAlgebra G.hom V
      ∀ p : PrimeSpectrum Γ(G.left, V), ¬ IsNilpotent
        (Algebra.TensorProduct.map (AlgHom.id k Γ(G.left, U))
          (IsScalarTower.toAlgHom k Γ(G.left, V) p.asIdeal.ResidueField)
          ((prodOpenTensorIso hU hV).inv D.b)) := by
  let X := (G ⊗ G).left
  let W := rightStabilizerLocus (𝟙 G) U
  -- a point of the locus over `v`
  obtain ⟨a, ha⟩ := (surjective_rightStabilizerLocus (𝟙 G) hne).surj v
  let w : X := W.ι a
  have hwW : w ∈ W := a.2
  have hwv : (snd G G).left w = v := ha
  obtain ⟨V₀, hV₀, hvV₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top v)
  have hY₀ := isAffineOpen_prodOpen hU hV₀
  have hwY₀ : w ∈ prodOpen U V₀ :=
    ⟨rightStabilizerLocus_le_fst (𝟙 G) U hwW, show (snd G G).left w ∈ V₀ from hwv ▸ hvV₀⟩
  obtain ⟨b₀, hb₀, hwb₀⟩ := hY₀.exists_basicOpen_le (V := W ⊓ prodOpen U V₀) ⟨w, hwW, hwY₀⟩ hwY₀
  -- the image of `D(b₀)` in `G` is open
  let O : G.left.Opens := ⟨(snd G G).left '' (X.basicOpen b₀ : Set X),
    (pullback.snd G.hom G.hom).isOpenMap _ (X.basicOpen b₀).isOpen⟩
  have hvO : v ∈ O := ⟨w, hwb₀, hwv⟩
  obtain ⟨a₀, ha₀, hva₀⟩ := hV₀.exists_basicOpen_le (V := O ⊓ V₀) ⟨v, hvO, hvV₀⟩ hvV₀
  let V := G.left.basicOpen a₀
  have hV : IsAffineOpen V := hV₀.basicOpen a₀
  have hVV₀ : V ≤ V₀ := G.left.basicOpen_le a₀
  have hVO : V ≤ O := ha₀.trans inf_le_left
  have hY := isAffineOpen_prodOpen hU hV
  have hYY₀ : prodOpen U V ≤ prodOpen U V₀ := inf_le_inf_left _ (Scheme.Hom.preimage_mono _ hVV₀)
  let b := X.presheaf.map (homOfLE hYY₀).op b₀
  have hbD : X.basicOpen b = prodOpen U V ⊓ X.basicOpen b₀ := Scheme.basicOpen_res _ _ _
  have hbW : X.basicOpen b ≤ rightStabilizerLocus (𝟙 G) U :=
    hbD ▸ inf_le_right.trans (hb₀.trans inf_le_left)
  -- the numerator
  let := hY.isLocalization_basicOpen b
  obtain ⟨⟨num, ⟨_, N, rfl⟩⟩, hnum'⟩ := IsLocalization.surj (Submonoid.powers b)
    ((rightTranslate (𝟙 G)).left.appLE U (X.basicOpen b)
        ((hbW.trans (rightStabilizerLocus_le_rightTranslate (𝟙 G) U))) f -
      (fst G G).left.appLE U (X.basicOpen b) ((hbW.trans (rightStabilizerLocus_le_fst (𝟙 G) U))) f)
  let D : StabilizerChartData U V f :=
    { b := b
      hbW := hbW
      num := num
      N := N
      hnum := by
        have e : (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom num =
            _ * (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom (b ^ N) := hnum'.symm
        rw [e, map_pow, mul_comm] }
  refine ⟨V, hV, hva₀, D, ?_⟩
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra G.hom V
  intro p
  -- a point of `D(b)` over `p`
  let y : V := hV.isoSpec.inv (show Spec Γ(G.left, V) from p)
  have hyp : hV.primeIdealOf y = p := by
    change (hV.isoSpec.inv ≫ hV.isoSpec.hom) (show Spec Γ(G.left, V) from p) = p
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨w', hw'b₀, hw'y⟩ := hVO y.2
  have hw'Y : w' ∈ prodOpen U V :=
    ⟨rightStabilizerLocus_le_fst (𝟙 G) U (hb₀.trans inf_le_left hw'b₀),
      show (snd G G).left w' ∈ V from hw'y ▸ y.2⟩
  have hw'b : w' ∈ X.basicOpen b := hbD ▸ ⟨hw'Y, hw'b₀⟩
  let Q := hY.primeIdealOf ⟨w', hw'Y⟩
  have hQp : (Q.asIdeal.comap ((snd G G).left.appLE V (prodOpen U V)
      (prodOpen_le_snd U V)).hom) = p.asIdeal := by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := (snd G G).left) V hV (prodOpen U V) hY
      (prodOpen_le_snd U V) hw'Y
    rw [← hyp]
    refine (congrArg PrimeSpectrum.asIdeal this).trans ?_
    congr 2
    exact Subtype.ext hw'y
  have hbQ : b ∉ Q.asIdeal := by
    have hmem : hY.fromSpec Q ∈ X.basicOpen b := by
      rw [hY.fromSpec_primeIdealOf]
      exact hw'b
    have := (hY.fromSpec_preimage_basicOpen b).le hmem
    exact this
  refine TensorProduct.not_isNilpotent_map_residueField_of_not_mem
    (prodOpenTensorIso hU hV).commRingCatIsoToRingEquiv
    ((fst G G).left.appLE U (prodOpen U V) (prodOpen_le_fst U V)).hom
    ((snd G G).left.appLE V (prodOpen U V) (prodOpen_le_snd U V)).hom
    (prodOpenTensorIso_tmul hU hV) _ Q.asIdeal p.asIdeal hQp.symm ?_
  change (prodOpenTensorIso hU hV).hom ((prodOpenTensorIso hU hV).inv b) ∉ Q.asIdeal
  rwa [Iso.inv_hom_id_apply]

end AlgebraicGeometry

end
