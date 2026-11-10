module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionVersality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Size.ArtinianLocal
public import StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence
public import StacksFrontier.Deformation.ResidueField.Comparison

/-!
# Versality at a point gives the lifting property

Let `S` be a scheme contained in a big fppf site `B`, `V` an object of the site, `Z ⊆ |V|`,
`W` a formal algebraic space and `g : V_{/Z} ⟶ W` versal at a point `v ∈ Z` in the sense of
Section 07XZ (`AlgebraicGeometry.FormalSpace.IsVersalAtCompletion`): small extensions of Artinian
local `𝒪_{S,s}`-algebras with residue field `k = κ(v)` lift. If `k` is finite over `𝒪_{S,s}`
then `g` has the lifting property `AlgebraicGeometry.FormalSpace.LiftsAtCompletion` for small
extensions of arbitrary Artinian local rings whose residue field is finite over `k`: such a
lifting problem over `D' ⟶ D` with residue field `l` is reduced to one over
`D' ×_l k ⟶ D ×_l k` (Tag 07W8), glued back by condition (RS) of `W`
(`AlgebraicGeometry.FormalSpace.satisfiesRSFunctor_of_isFormalAlgebraicSpace`).

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_comparisonFunctor_map`: the comparison functor
  `C ↦ C ×_l k` turns a morphism `C' ⟶ C` into a cartesian square of rings.
* `AlgebraicGeometry.FormalSpace.liftsAtCompletion_of_isVersalAtCompletion`: the statement
  above.

## References

* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 07W8](https://stacks.math.columbia.edu/tag/07W8)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

section Ring

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})

/-- **The comparison functor turns a morphism into a cartesian square.** For `f : C' ⟶ C` in
`𝒞_{Λ,l}`, the square of rings `C' ×_l k ⟶ C ×_l k`, `C' ×_l k ⟶ C'`, `C' ⟶ C`, `C ×_l k ⟶ C` is
a fibre product: an element of `C' ×_l k` is determined by its images in `C'` and `C ×_l k`. -/
theorem isPullback_comparisonFunctor_map {C' C : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (f : C' ⟶ C) :
    IsPullback
      (CommRingCat.ofHom (Deformation.Artin.changeOfFieldMap T
        (𝟙 ((Deformation.comparisonFunctor T).functor.obj C'))))
      (CommRingCat.ofHom ((Deformation.comparisonFunctor T).functor.map f).hom.toRingHom)
      (CommRingCat.ofHom f.hom.toRingHom)
      (CommRingCat.ofHom (Deformation.Artin.changeOfFieldMap T
        (𝟙 ((Deformation.comparisonFunctor T).functor.obj C)))) := by
  let F := Deformation.comparisonFunctor T
  let fst' := Deformation.Artin.changeOfFieldMap T (𝟙 (F.functor.obj C'))
  let fstC := Deformation.Artin.changeOfFieldMap T (𝟙 (F.functor.obj C))
  have hw : ∀ a' : F.functor.obj C', f.hom (fst' a') = fstC ((F.functor.map f).hom a') :=
    fun a' => (F.map_fst f a').symm
  let e : F.functor.obj C' ≃+* RingHom.pullback f.hom.toRingHom fstC :=
    { toFun := fun a' => ⟨(fst' a', (F.functor.map f).hom a'), hw a'⟩
      invFun := fun x => (F.pullbackEquiv C').symm ⟨(x.val.1, ((F.pullbackEquiv C) x.val.2).val.2),
        by
          calc Deformation.residueMap T C' x.val.1
              = Deformation.residueMap T C (f.hom x.val.1) := (f.residue_comm x.val.1).symm
            _ = Deformation.residueMap T C (fstC x.val.2) := congrArg _ x.property
            _ = _ := ((F.pullbackEquiv C) x.val.2).property⟩
      left_inv := fun a' => by
        apply (F.pullbackEquiv C').injective
        rw [RingEquiv.apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (F.map_snd f a').symm
      right_inv := fun x => by
        apply Subtype.ext
        apply Prod.ext
        · change fst' ((F.pullbackEquiv C').symm _) = x.val.1
          rw [Deformation.Artin.changeOfFieldMap_apply]
          change ((F.pullbackEquiv C') ((F.pullbackEquiv C').symm _)).val.1 = _
          rw [RingEquiv.apply_symm_apply]
        · apply (F.pullbackEquiv C).injective
          apply Subtype.ext
          apply Prod.ext
          · change ((F.pullbackEquiv C) ((F.functor.map f).hom _)).val.1 = fstC x.val.2
            rw [F.map_fst f, RingEquiv.apply_symm_apply]
            exact x.property
          · change ((F.pullbackEquiv C) ((F.functor.map f).hom _)).val.2 = _
            rw [F.map_snd f, RingEquiv.apply_symm_apply]
      map_mul' := fun a b => Subtype.ext (Prod.ext (map_mul fst' a b)
        (map_mul (F.functor.map f).hom a b))
      map_add' := fun a b => Subtype.ext (Prod.ext (map_add fst' a b)
        (map_add (F.functor.map f).hom a b)) }
  have h := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom f.hom.toRingHom) (CommRingCat.ofHom fstC))
  refine h.of_iso e.toCommRingCatIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  · ext x
    change x.val.1 = fst' (e.symm x)
    exact (congrArg (fun y => y.val.1) (e.apply_symm_apply x)).symm
  · ext x
    change x.val.2 = (F.functor.map f).hom (e.symm x)
    exact (congrArg (fun y => y.val.2) (e.apply_symm_apply x)).symm

end Ring

section Geometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism into `V` all of whose points map to a point `v` of the image of `Z` has
point-set image in `Z`. -/
theorem hasImageIn_of_forall_eq {V T : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (a : T ⟶ V)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : ∀ t, (BigFppfOver.toScheme B S hS).map a t = v)
    (hvZ : v ∈ Space.pointsToScheme B S hS V '' Z) :
    Space.HasImageIn B S hS (yoneda.obj V) Z T a := by
  obtain ⟨z, hz, rfl⟩ := hvZ
  intro p
  have h : Space.pointsToScheme B S hS V
      ((⟨p.carrier, p.contained, p.toBase, (yoneda.obj V).map p.value.op a⟩ :
        Space.FieldValuedPoint B S hS (yoneda.obj V)).class B S hS (yoneda.obj V)) =
      Space.pointsToScheme B S hS V z := by
    rw [Space.pointsToScheme_class]
    exact hv _
  rw [Space.injective_pointsToScheme B S hS V h]
  exact hz

/-- **Versality at a point gives the lifting property.** If `g : V_{/Z} ⟶ W` into a formal
algebraic space is versal at `v ∈ Z` (Section 07XZ), the residue field `κ(v)` is finite over the
Noetherian local ring `𝒪_{S,s}` at the image of `v` and `Spec κ(v) ⟶ S` is of finite type, then
`g` has the lifting property at `v` for small extensions of Artinian local rings whose residue
field is finite over `κ(v)`. -/
theorem liftsAtCompletion_of_isVersalAtCompletion (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (W : FppfSheaf B S hS)
    (hW : IsFormalAlgebraicSpace B S hS W)
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (v : ((Over.post B.inclusion).obj V : Over S).left)
    (hvZ : v ∈ Space.pointsToScheme B S hS V '' Z)
    [IsNoetherianRing (S.presheaf.stalk
      (Deformation.Artin.basePoint ((Over.post B.inclusion).obj V) v))]
    (hk : (Scheme.stalkClosedPointTo (Deformation.Artin.residueFieldBasePoint
      ((Over.post B.inclusion).obj V) v)).hom.Finite)
    (hvft : AlgebraicGeometry.LocallyOfFiniteType
        (((Over.post B.inclusion).obj V : Over S).left.fromSpecResidueField v ≫
          ((Over.post B.inclusion).obj V : Over S).hom) ∧
      QuasiCompact (((Over.post B.inclusion).obj V : Over S).left.fromSpecResidueField v ≫
          ((Over.post B.inclusion).obj V : Over S).hom))
    (hvers : IsVersalAtCompletion B S hS V Z W g v) :
    LiftsAtCompletion B S hS V Z W g v := by
  classical
  intro D' D φ hφ hloc hD hD' s α hα hpt hfin ha z hz
  have := hloc
  subst hpt
  let U := (Over.post B.inclusion).obj V
  let s₀ := Deformation.Artin.basePoint U (α (IsLocalRing.closedPoint D))
  let Λ := S.presheaf.stalk s₀
  let k := U.left.residueField (α (IsLocalRing.closedPoint D))
  let algΛk : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U _
  obtain ⟨hlD', -, hArtD', hArtD, hsurj, -⟩ := hφ
  have := hlD'
  have := hArtD'
  have := hArtD
  have : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hsurj
  -- the image of the closed point in `S`
  have hcp : (Spec.map φ) (IsLocalRing.closedPoint D) = IsLocalRing.closedPoint D' :=
    Spec_closedPoint
  have hs0 : s (IsLocalRing.closedPoint D') = s₀ := by
    have h1 : s (IsLocalRing.closedPoint D') =
        (Spec.map φ ≫ s) (IsLocalRing.closedPoint D) := (congrArg s hcp).symm
    have h2 : s₀ = U.hom (α (IsLocalRing.closedPoint D)) :=
      congrArg U.hom (Scheme.fromSpecResidueField_apply _ _)
    exact h1.trans ((congrArg (fun f => f (IsLocalRing.closedPoint D)) hα.symm).trans h2.symm)
  -- the `Λ`-algebra structures
  let ψ' : CommRingCat.of Λ ⟶ D' :=
    S.presheaf.stalkSpecializes (Inseparable.of_eq hs0).specializes ≫ Scheme.stalkClosedPointTo s
  have hsψ : Spec.map ψ' ≫ S.fromSpecStalk s₀ = s := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  let : Algebra Λ D' := ψ'.hom.toAlgebra
  let : Algebra Λ D := (φ.hom.comp ψ'.hom).toAlgebra
  -- the residue field `l` of `D`
  let cpD : (Spec (.of D) : Scheme) := IsLocalRing.closedPoint D
  let l := (Spec (.of D)).residueField cpD
  let ρ : CommRingCat.of D ⟶ l :=
    CommRingCat.ofHom (algebraMap D cpD.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of D) cpD).inv
  have hρ : Spec.map ρ = (Spec (.of D)).fromSpecResidueField cpD := by
    rw [Spec.map_comp]
    exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of D) _
  let κα : k ⟶ l := α.residueFieldMap cpD
  let : Algebra k l := κα.hom.toAlgebra
  let : Algebra Λ l := ((algebraMap k l).comp (algebraMap Λ k)).toAlgebra
  have : IsScalarTower Λ k l := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite k l := hfin
  let iΛ : Spec (.of Λ) ⟶ S := S.fromSpecStalk s₀
  have hkΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      U.left.fromSpecResidueField (α (IsLocalRing.closedPoint D)) ≫ U.hom :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hcompat : ∀ a : Λ, ρ.hom (φ.hom (ψ'.hom a)) = algebraMap Λ l a := by
    have hSpec : Spec.map (ψ' ≫ φ ≫ ρ) = Spec.map (CommRingCat.ofHom (algebraMap Λ k) ≫ κα) := by
      rw [← cancel_mono (S.fromSpecStalk s₀)]
      have hL : Spec.map (ψ' ≫ φ ≫ ρ) ≫ S.fromSpecStalk s₀ =
          (Spec (.of D)).fromSpecResidueField cpD ≫ α ≫ U.hom := by
        rw [Spec.map_comp ψ' (φ ≫ ρ), Spec.map_comp φ ρ, hρ, Category.assoc, Category.assoc, hsψ,
          hα]
      have hR : Spec.map (CommRingCat.ofHom (algebraMap Λ k) ≫ κα) ≫ S.fromSpecStalk s₀ =
          Spec.map κα ≫ U.left.fromSpecResidueField (α (IsLocalRing.closedPoint D)) ≫ U.hom := by
        rw [Spec.map_comp, Category.assoc, hkΛ]
      rw [hL, hR, ← Category.assoc, ← Category.assoc]
      exact (congrArg (· ≫ U.hom)
        (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField α _)).symm
    intro a
    exact congrArg (fun χ => χ.hom a) (Spec.map_injective hSpec)
  -- the objects `D`, `D'` of `𝒞_{Λ,l}` and the morphism between them
  have hρs : Function.Surjective ρ.hom := by
    have : cpD.asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal D
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of D) cpD).inv).2.comp
      (Ideal.algebraMap_residueField_surjective _)
  have hρ's : Function.Surjective (φ ≫ ρ).hom := hρs.comp hsurj
  have : IsLocalHom ρ.hom := IsLocalHom.of_surjective ρ.hom hρs
  have : IsLocalHom (φ ≫ ρ).hom := IsLocalHom.of_surjective (φ ≫ ρ).hom hρ's
  let residueEquivOf : ∀ (E : CommRingCat.{u}) [IsLocalRing E] [Algebra Λ E] (r : E ⟶ l)
      [IsLocalHom r.hom], Function.Surjective r.hom →
      (∀ a : Λ, r.hom (algebraMap Λ E a) = algebraMap Λ l a) →
      IsLocalRing.ResidueField E ≃ₐ[Λ] l := fun E _ _ r _ hr hrΛ =>
    AlgEquiv.ofBijective
      { toRingHom := IsLocalRing.ResidueField.lift r.hom
        commutes' := fun a => by
          rw [IsScalarTower.algebraMap_apply Λ E (IsLocalRing.ResidueField E),
            IsLocalRing.ResidueField.algebraMap_eq]
          change IsLocalRing.ResidueField.lift r.hom (IsLocalRing.residue E _) = _
          rw [IsLocalRing.ResidueField.lift_residue_apply]
          exact hrΛ a }
      ⟨RingHom.injective _, fun y => by
        obtain ⟨x, rfl⟩ := hr y
        exact ⟨IsLocalRing.residue E x, IsLocalRing.ResidueField.lift_residue_apply _ _⟩⟩
  have : Module.Finite Λ k := hk
  let T : Deformation.ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := l }
  let : Algebra T.Λ D := (inferInstance : Algebra Λ D)
  let : Algebra T.Λ D' := (inferInstance : Algebra Λ D')
  let C : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l :=
    { carrier := D, residueEquiv := residueEquivOf D ρ hρs hcompat }
  let C' : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l :=
    { carrier := D', residueEquiv := residueEquivOf D' (φ ≫ ρ) hρ's hcompat }
  let φΛ : C' →ₐ[T.Λ] C := { toRingHom := φ.hom, commutes' := fun _ => rfl }
  let fC : C' ⟶ C :=
    { hom := φΛ
      isLocal := inferInstanceAs (IsLocalHom φ.hom)
      residue_comm := fun a => by
        change IsLocalRing.ResidueField.lift ρ.hom (IsLocalRing.residue D (φ.hom a)) =
          IsLocalRing.ResidueField.lift (φ ≫ ρ).hom (IsLocalRing.residue D' a)
        rw [IsLocalRing.ResidueField.lift_residue_apply,
          IsLocalRing.ResidueField.lift_residue_apply]
        rfl }
  let F := Deformation.comparisonFunctor T
  let A := F.functor.obj C
  let A' := F.functor.obj C'
  let fA : A' ⟶ A := F.functor.map fC
  have hfAs : Function.Surjective fA.hom := Deformation.comparisonFunctor_map_surjective T fC hsurj
  -- `Spec A` is the pushout of `Spec C` and `Spec k` along `Spec l`
  let cof : A →+* C := Deformation.Artin.changeOfFieldMap T (𝟙 A)
  let cof' : A' →+* C' := Deformation.Artin.changeOfFieldMap T (𝟙 A')
  have hresC : Deformation.residueMap T C = ρ.hom := by
    ext a
    exact IsLocalRing.ResidueField.lift_residue_apply ρ.hom a
  have hpo1 := Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (Deformation.Artin.comparisonRing_isPullback T (𝟙 A))
    (Deformation.Artin.residueMap_surjective T C)
  have hcomp1 : Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)) ≫ α =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        U.left.fromSpecResidueField (α cpD) := by
    have e1 : CommRingCat.ofHom (Deformation.residueMap T C) = ρ := by
      rw [hresC]
      rfl
    have e2 : CommRingCat.ofHom (algebraMap T.k T.l) = κα := rfl
    rw [e1, e2, hρ]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField α cpD).symm
  let α₀ : Spec (.of A) ⟶ U.left := hpo1.desc α (U.left.fromSpecResidueField (α cpD)) hcomp1
  have hα₀l : Spec.map (CommRingCat.ofHom cof) ≫ α₀ = α := hpo1.inl_desc _ _ _
  have hα₀r : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ α₀ =
      U.left.fromSpecResidueField (α cpD) := hpo1.inr_desc _ _ _
  -- the objects `Spec A`, `Spec A'` of the site, over `Spec 𝒪_{S,s}`
  have hmk : ∀ E : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.k,
      Cardinal.mk (IsLocalRing.ResidueField E) ≤ (V.left.obj).size := fun E =>
    (Cardinal.mk_congr E.residueEquiv.toEquiv).trans_le
      (Scheme.mk_residueField_le_size U.left (α cpD))
  have hAc : B.Contains (Spec (.of A)) :=
    B.contains_spec_of_isArtinianRing V.left.property (.of A) (hmk A)
  have hA'c : B.Contains (Spec (.of A')) :=
    B.contains_spec_of_isArtinianRing V.left.property (.of A') (hmk A')
  let tA : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ
  let tA' : Spec (.of A') ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap T.Λ A')) ≫ iΛ
  let TA := affineOver B S hS hAc tA
  let TA' := affineOver B S hS hA'c tA'
  -- `Spec` of a `Λ`-algebra map is a morphism over `Spec Λ`
  have hΛ : ∀ {E E' : CommRingCat.{u}} (a : Λ →+* E) (a' : Λ →+* E') (f : E ⟶ E'),
      f.hom.comp a = a' → Spec.map f ≫ Spec.map (CommRingCat.ofHom a) ≫ iΛ =
        Spec.map (CommRingCat.ofHom a') ≫ iΛ := by
    rintro E E' a - f rfl
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have eXD : Spec.map φ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ := by
    rw [← hsψ]
    exact hΛ _ _ φ rfl
  have hj₁ : Spec.map (CommRingCat.ofHom cof) ≫ tA = Spec.map φ ≫ s :=
    (hΛ _ _ _ rfl).trans eXD.symm
  let i : TA ⟶ TA' := affineOverHom B S hS hAc tA (V := TA')
    (Spec.map (CommRingCat.ofHom fA.hom.toRingHom))
    (hΛ _ _ _ rfl)
  -- the morphism `a₀ : Spec A ⟶ V`
  have hα₀ : α₀ ≫ U.hom = tA := by
    refine hpo1.hom_ext ?_ ?_
    · rw [← Category.assoc, hα₀l, hα]
      exact hj₁.symm
    · rw [← Category.assoc, hα₀r]
      change _ = Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Deformation.Artin.residueMap_comp_algebraMap_self]
      exact hkΛ.symm
  let a₀ : TA ⟶ V := affineOverHom B S hS hAc tA (V := V) α₀ hα₀
  have : IsLocalHom (Deformation.Artin.residueMap A) := IsLocalHom.of_surjective _
    (A.residueEquiv.surjective.comp IsLocalRing.residue_surjective)
  have ha₀ : Space.HasImageIn B S hS (yoneda.obj V) Z TA a₀ := by
    refine hasImageIn_of_forall_eq B S hS a₀ (α cpD) (fun t => ?_) hvZ
    have ht : t = (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)))
        (IsLocalRing.closedPoint k) :=
      (eq_closedPoint_of_isArtinianRing (.of A) t).trans Spec_closedPoint.symm
    change α₀ t = _
    rw [ht]
    exact (congrArg (fun f => f (IsLocalRing.closedPoint k)) hα₀r).trans
      (Scheme.fromSpecResidueField_apply _ _)
  -- the pushout `Spec A' = Spec D' ⨿_{Spec D} Spec A` and condition (RS)
  let XD := affineOver B S hS hD (Spec.map φ ≫ s)
  let XD' := affineOver B S hS hD' s
  let i₁ : XD ⟶ XD' := affineOverHom B S hS hD (Spec.map φ ≫ s) (V := XD') (Spec.map φ) rfl
  let j₁ : XD ⟶ TA := affineOverHom B S hS hD _ (V := TA) (Spec.map (CommRingCat.ofHom cof)) hj₁
  let i'₁ : XD' ⟶ TA' := affineOverHom B S hS hD' s (V := TA') (Spec.map (CommRingCat.ofHom cof'))
    ((hΛ _ _ _ rfl).trans hsψ)
  have hsq := isPullback_comparisonFunctor_map T fC
  have hcomm : i₁ ≫ i'₁ = j₁ ≫ i := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map φ ≫ Spec.map (CommRingCat.ofHom cof') =
      Spec.map (CommRingCat.ofHom cof) ≫ Spec.map (CommRingCat.ofHom fA.hom.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map hsq.w
  have hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i₁) ((BigFppfOver.toScheme B S hS).map j₁)
      ((BigFppfOver.toScheme B S hS).map i'₁) ((BigFppfOver.toScheme B S hS).map i) :=
    Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective φ (CommRingCat.ofHom cof)
      (CommRingCat.ofHom fA.hom.toRingHom) (CommRingCat.ofHom cof') hsq.flip hsurj
  have hcl : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i₁) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective φ hsurj
  have hAL : ∀ (E : CommRingCat.{u}) [IsLocalRing E] [IsArtinianRing E]
      (hE : B.Contains (Spec (.of E))) (t : Spec (.of E) ⟶ S),
      Deformation.Artin.IsArtinianLocal B S hS (affineOver B S hS hE t) := by
    intro E _ _ hE t
    refine ⟨inferInstanceAs (IsAffine (Spec (.of E))), ?_, ?_⟩
    · exact (Scheme.ΓSpecIso (CommRingCat.of E)).commRingCatIsoToRingEquiv.symm.isLocalRing
    · exact (Scheme.ΓSpecIso (CommRingCat.of E)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  have hkft : AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) :=
    hkΛ ▸ hvft
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) := by
    have : IsFinite (Spec.map κα) := (IsFinite.SpecMap_iff κα).mpr hfin
    have := hkft.1
    have := hkft.2
    have e : Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ =
        Spec.map κα ≫ Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ := by
      rw [show CommRingCat.ofHom (algebraMap T.Λ T.l) =
        CommRingCat.ofHom (algebraMap T.Λ T.k) ≫ κα from rfl, Spec.map_comp, Category.assoc]
      rfl
    rw [e]
    have h1 : AlgebraicGeometry.LocallyOfFiniteType (Spec.map κα) := inferInstance
    have h2 : QuasiCompact (Spec.map κα) := inferInstance
    exact ⟨MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _ h1 hkft.1,
      MorphismProperty.comp_mem (W := @QuasiCompact) _ _ h2 hkft.2⟩
  have hFT : ∀ (κ : Type u) [Field κ] [Algebra T.Λ κ]
      (E : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ κ) (hE : B.Contains (Spec (.of E))),
      (AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ κ)) ≫ iΛ) ∧
        QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ κ)) ≫ iΛ)) →
      Deformation.Artin.IsFiniteTypeOver B S hS
        (affineOver B S hS hE (Spec.map (CommRingCat.ofHom (algebraMap T.Λ E)) ≫ iΛ)) :=
    fun κ _ _ E hE h => Deformation.Artin.spec_finiteType_of_residueField_point E iΛ h.1 h.2
  have hRS : Deformation.Artin.SatisfiesRSFunctor B S hS W.obj :=
    satisfiesRSFunctor_of_isFormalAlgebraicSpace hW
  -- the section of `W` over `Spec A'` glued from `z` and `g(a₀)`
  have key : ∀ {T₀ : BigFppfOver B S hS} (y y' : T₀ ⟶ V)
      (hy : Space.HasImageIn B S hS (yoneda.obj V) Z T₀ y)
      (hy' : Space.HasImageIn B S hS (yoneda.obj V) Z T₀ y'),
      y = y' → presheafSection (F := yoneda.obj V) B S hS y hy =
        presheafSection (F := yoneda.obj V) B S hS y' hy' := by
    intro T₀ y y' hy hy' hyy
    subst hyy
    rfl
  have hj₁a : j₁ ≫ a₀ = affineOverHom B S hS hD _ α hα := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hα₀l
  have hj₁I : Space.HasImageIn B S hS (yoneda.obj V) Z XD ((yoneda.obj V).map j₁.op a₀) :=
    (Space.completionSubfunctor B S hS (yoneda.obj V) Z).map j₁.op (a := ULift.up a₀) ha₀
  have hab : W.obj.map j₁.op
      (g.hom.app (op TA) (presheafSection (F := yoneda.obj V) B S hS a₀ ha₀)) =
      W.obj.map i₁.op z := by
    rw [hz, ← NatTrans.naturality_apply g.hom j₁.op,
      presheafSection_map (F := yoneda.obj V) (TF := Z) B S hS j₁ a₀ ha₀ hj₁I]
    exact congrArg (g.hom.app _) (key _ _ hj₁I ha hj₁a)
  obtain ⟨z₀, ⟨hz₀a, hz₀b⟩, -⟩ := hRS i₁ j₁ i'₁ i hcomm
    (hAL D hD _) (hAL D' hD' _) (hAL (.of A) hAc _) (hAL (.of A') hA'c _)
    (by
      have h := hFT T.l C hD hlft
      change AlgebraicGeometry.LocallyOfFiniteType (Spec.map φ ≫ s) ∧ QuasiCompact (Spec.map φ ≫ s)
      rw [eXD]
      exact h)
    (by
      have h := hFT T.l C' hD' hlft
      change AlgebraicGeometry.LocallyOfFiniteType s ∧ QuasiCompact s
      rw [← hsψ]
      exact h)
    (hFT T.k A hAc hkft) (hFT T.k A' hA'c hkft) hcl hpo _ z hab
  -- versality over `A' ⟶ A`
  obtain ⟨b, hb, hib, hgb⟩ := hvers A A' fA hfAs TA TA' rfl rfl i
    rfl a₀ ha₀
    hα₀r z₀ hz₀a
  -- the solution over `D'`
  let β : Spec (.of D') ⟶ U.left := ((Over.post B.inclusion).map (i'₁ ≫ b)).left
  have hβ : β ≫ U.hom = s := congrArg B.inclusion.map (Over.w (i'₁ ≫ b))
  have hβI : Space.HasImageIn B S hS (yoneda.obj V) Z XD' ((yoneda.obj V).map i'₁.op b) :=
    (Space.completionSubfunctor B S hS (yoneda.obj V) Z).map i'₁.op (a := ULift.up b) hb
  have hβb : affineOverHom B S hS hD' s β hβ = (yoneda.obj V).map i'₁.op b := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rfl
  refine ⟨β, hβ, hβb ▸ hβI, ?_, ?_⟩
  · have h1 : i₁ ≫ i'₁ ≫ b = affineOverHom B S hS hD _ α hα := by
      rw [← Category.assoc, hcomm, Category.assoc, hib, hj₁a]
    exact congrArg (fun m => ((Over.post B.inclusion).map m).left) h1
  · rw [key _ _ _ hβI hβb, ← presheafSection_map (F := yoneda.obj V) (TF := Z) B S hS i'₁ b hb hβI,
      NatTrans.naturality_apply g.hom i'₁.op, hgb, hz₀b]

end Geometry

end AlgebraicGeometry.FormalSpace
