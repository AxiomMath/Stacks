module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed

/-!
# Galois descent of closed subsets of an algebraic space

Let `K/k` be a Galois extension and let `X` be an algebraic space over `k`. A `k`-algebra
automorphism `σ` of `K` acts on the points of the base change `X_K` by composing the structure
morphism of a field-valued representative with the automorphism of `Spec K` attached to `σ`,
leaving the section itself untouched. A closed subset of `|X_K|` invariant under that action is
the inverse image of a closed subset of `|X|`.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.galoisTwist` is the field-valued point obtained from
  a representative by composing its structure morphism with the automorphism of `Spec K`.
* `AlgebraicGeometry.Space.galoisPointsAction` is the resulting self-map of `|X_K|`.

## Main results

* `CategoryTheory.OverShriek.restrictYonedaIso_hom_naturality`: the identification of the
  restriction of a representable presheaf with the presheaf represented by the base change of
  the representing object is natural in that object.
* `AlgebraicGeometry.Space.exists_closed_subset_with_preimage_eq_of_galois_invariant`:
  **Stacks 0A16**, a Galois-invariant closed subset of `|X_K|` descends.

## Implementation notes

Invariance is written using inverse images under the self-maps
`AlgebraicGeometry.Space.galoisPointsAction`; since the hypothesis ranges over the whole Galois
group this is the same condition as invariance under the corresponding direct action, and it is
the form in which the statement for schemes,
`AlgebraicGeometry.exists_closed_subset_with_preimage_eq_of_galois_invariant`, is available.

The proof follows the source: choose a scheme atlas `U ⟶ X`, base change it to `K` — which by
`CategoryTheory.OverShriek.restrictYonedaIso` is the fibre product `U ×_{Spec k} Spec K` —
descend the closed subset of `U_K` cut out by the given one using the case of schemes, and push
the result forward along the atlas. The atlas is an open continuous surjection on points, hence
a quotient map, so the pushforward is closed as soon as the descended subset is constant on the
fibres of `|U| → |X|`; those fibres are described by the kernel pair of the atlas, whose own
base change to `K` provides the compatible lifts the comparison needs.

## References

* [Stacks Project, Tag 0A16](https://stacks.math.columbia.edu/tag/0A16)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {A A' : C} (g : A ⟶ A')

section Representable

variable [Limits.HasPullbacks C]

/-- The base change of a morphism over `A'` commutes with the projections to the original
objects. -/
private theorem pullback_map_left_comp_fst {Z Z' : Over A'} (w : Z ⟶ Z') :
    ((Over.pullback g).map w).left ≫ pullback.fst Z'.hom g =
      pullback.fst Z.hom g ≫ w.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- `CategoryTheory.OverShriek.restrictYonedaIso` is natural in the representing object. -/
theorem restrictYonedaIso_hom_naturality {Z Z' : Over A'} (w : Z ⟶ Z') :
    yoneda.map ((Over.pullback g).map w) ≫ (restrictYonedaIso g Z').hom =
      (restrictYonedaIso g Z).hom ≫ (relocalizeRestrict g).map (yoneda.map w) := by
  ext W v
  change ((Over.mapPullbackAdj g).homEquiv (unop W) Z').symm (v ≫ (Over.pullback g).map w) =
    ((Over.mapPullbackAdj g).homEquiv (unop W) Z).symm v ≫ w
  exact (Over.mapPullbackAdj g).homEquiv_naturality_right_symm v w

end Representable

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

/-! ### Equality of field-valued points -/

/-- Two field-valued points agreeing on all of their data are equal. -/
private theorem fieldValuedPoint_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p q : FieldValuedPoint B S hS F}
    (hcarrier : p.carrier = q.carrier) (hfield : HEq p.field q.field)
    (htoBase : HEq p.toBase q.toBase) (hvalue : HEq p.value q.value) : p = q := by
  obtain ⟨pc, pm, pb, pv⟩ := p
  obtain ⟨qc, qm, qb, qv⟩ := q
  dsimp only at hcarrier hfield htoBase hvalue
  subst hcarrier
  obtain rfl := eq_of_heq hfield
  obtain rfl := eq_of_heq htoBase
  obtain rfl := eq_of_heq hvalue
  rfl

/-! ### Field-valued points attached to a morphism from a field spectrum -/

section PointOfHom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  (κ : Type u) [Field κ] (hκ : B.Contains (Spec (.of κ)))
  (x : Spec (.of κ) ⟶ (BigFppfOver.toScheme B S hS).obj U)

/-- The field-valued point of a represented presheaf given by a morphism from the spectrum of a
field whose spectrum lies in the chosen big fppf site. -/
private noncomputable def pointOfSchemeHom : FieldValuedPoint B S hS (yoneda.obj U) where
  carrier := κ
  contained := hκ
  toBase := B.inclusion.map (B.inclusion.preimage (X := B.obj hκ) (Y := U.left) x ≫ U.hom)
  value := Over.homMk (B.inclusion.preimage (X := B.obj hκ) (Y := U.left) x) rfl

private theorem pointOfSchemeHom_toBase :
    (pointOfSchemeHom B S hS U κ hκ x).toBase = x ≫ B.inclusion.map U.hom := by
  change B.inclusion.map (B.inclusion.preimage (X := B.obj hκ) (Y := U.left) x ≫ U.hom) = _
  rw [B.inclusion.map_comp, B.inclusion.map_preimage]

private theorem pointOfSchemeHom_value_left :
    B.inclusion.map (pointOfSchemeHom B S hS U κ hκ x).value.left = x := by
  change B.inclusion.map (B.inclusion.preimage (X := B.obj hκ) (Y := U.left) x) = x
  rw [B.inclusion.map_preimage]

private theorem schemePoint_pointOfSchemeHom :
    schemePoint B S hS U (pointOfSchemeHom B S hS U κ hκ x) =
      x (IsLocalRing.closedPoint κ) := by
  change (B.inclusion.map (B.inclusion.preimage (X := B.obj hκ) (Y := U.left) x))
    (IsLocalRing.closedPoint κ) = x (IsLocalRing.closedPoint κ)
  rw [B.inclusion.map_preimage]

end PointOfHom

/-! ### Closed subsets of the points of a represented presheaf -/

section RepresentedClosed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The preimage of a closed subset of the representing scheme is closed in the points. -/
private theorem isClosed_pointsToScheme_preimage
    (V : Set ((BigFppfOver.toScheme B S hS).obj U)) (hV : IsClosed V) :
    @IsClosed _ (pointTopology B S hS (yoneda.obj U)) (pointsToScheme B S hS U ⁻¹' V) := by
  let : TopologicalSpace (points B S hS (yoneda.obj U)) := pointTopology B S hS (yoneda.obj U)
  rw [← isOpen_compl_iff, show (pointsToScheme B S hS U ⁻¹' V)ᶜ =
    pointsToScheme B S hS U ⁻¹' Vᶜ from rfl,
    isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_exists_preimage]
  exact ⟨Vᶜ, hV.isOpen_compl, rfl⟩

/-- Every closed subset of the points of a represented presheaf is the preimage of a closed
subset of the representing scheme. -/
private theorem exists_isClosed_pointsToScheme_preimage
    (W : Set (points B S hS (yoneda.obj U)))
    (hW : @IsClosed _ (pointTopology B S hS (yoneda.obj U)) W) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed V ∧
      pointsToScheme B S hS U ⁻¹' V = W := by
  let : TopologicalSpace (points B S hS (yoneda.obj U)) := pointTopology B S hS (yoneda.obj U)
  obtain ⟨V, hV, hmem⟩ :=
    (isSchemeOpen_iff_exists_preimage B S hS U Wᶜ).mp
      ((isOpen_yoneda_iff_isSchemeOpen B S hS U Wᶜ).mp hW.isOpen_compl)
  refine ⟨Vᶜ, hV.isClosed_compl, ?_⟩
  rw [show pointsToScheme B S hS U ⁻¹' Vᶜ = (pointsToScheme B S hS U ⁻¹' V)ᶜ from rfl,
    hmem, compl_compl]

end RepresentedClosed

/-! ### The Galois action on the points of a base change -/

section GaloisAction

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- Restricting the base change of `X` to `K` along the automorphism of `Spec K` attached to a
`k`-algebra automorphism of `K` recovers that base change: the automorphism lies over
`Spec k`. -/
theorem relocalizeRestrict_siteMapAlgAut_obj (σ : K ≃ₐ[k] K) :
    (OverShriek.relocalizeRestrict (siteMapAlgAut B k K hK σ)).obj
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) =
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X :=
  OverShriek.relocalizeRestrict_twist_eq (fieldExtensionMap B k K hk hK)
    (siteMapAlgAut B k K hK σ) (siteMapAlgAut_comp_fieldExtensionMap B k K hk hK σ) X

/-- **The Galois twist of a field-valued point of a base change.** A `k`-algebra automorphism
`σ` of `K` composes the structure morphism of a representative with the automorphism of
`Spec K` attached to `σ` and leaves its section untouched. -/
noncomputable def FieldValuedPoint.galoisTwist (σ : K ≃ₐ[k] K)
    (p : FieldValuedPoint B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) :
    FieldValuedPoint B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) :=
  FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of K)) (Spec (.of K)) hK hK
    (siteMapAlgAut B k K hK σ) _
    (FieldValuedPoint.map B (Spec (.of K)) hK _
      (eqToHom (relocalizeRestrict_siteMapAlgAut_obj B k K hk hK X σ).symm) p)

variable (σ : K ≃ₐ[k] K)
  (p : FieldValuedPoint B (Spec (.of K)) hK
    ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))

/-- The Galois twist does not change the field of definition of a representative. -/
@[simp]
theorem FieldValuedPoint.galoisTwist_carrier :
    (FieldValuedPoint.galoisTwist B k K hk hK X σ p).carrier = p.carrier := rfl

/-- The Galois twist composes the structure morphism of a representative with the automorphism
of `Spec K`. -/
@[simp]
theorem FieldValuedPoint.galoisTwist_toBase :
    (FieldValuedPoint.galoisTwist B k K hk hK X σ p).toBase =
      p.toBase ≫ specMapAlgAut k K σ := by
  change p.toBase ≫ B.inclusion.map (siteMapAlgAut B k K hK σ) = _
  rw [map_siteMapAlgAut]

/-- The Galois twist leaves the section of a representative untouched. The equality is
heterogeneous because the type of the section is indexed by the structure morphism. -/
theorem FieldValuedPoint.galoisTwist_value_heq :
    HEq (FieldValuedPoint.galoisTwist B k K hk hK X σ p).value p.value :=
  OverShriek.eqToHom_app_heq (relocalizeRestrict_siteMapAlgAut_obj B k K hk hK X σ).symm _ p.value

/-- **The action of the Galois group on the points of a base change.** A `k`-algebra
automorphism of `K` acts on `|X_K|` by the Galois twist of representatives. -/
noncomputable def galoisPointsAction :
    points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) →
      points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) :=
  pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of K)) hK hK
      (siteMapAlgAut B k K hK σ) _ ∘
    pointsMap B (Spec (.of K)) hK _
      (eqToHom (relocalizeRestrict_siteMapAlgAut_obj B k K hk hK X σ).symm)

/-- The Galois action on points is the Galois twist of representatives. -/
@[simp]
theorem galoisPointsAction_class :
    galoisPointsAction B k K hk hK X σ (p.class B (Spec (.of K)) hK _) =
      (FieldValuedPoint.galoisTwist B k K hk hK X σ p).class B (Spec (.of K)) hK _ := rfl

end GaloisAction

/-! ### The twist of a base changed atlas -/

section Twist

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
  (U : BigFppfOver B (Spec (.of k)) hk) (f : yoneda.obj U ⟶ X)
  (Ubar : BigFppfOver B (Spec (.of K)) hK) (pU : Ubar.left ⟶ U.left)
  (iU : yoneda.obj Ubar ≅
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj (yoneda.obj U))

/-- **Precomposing with a twist of the base changed atlas is the Galois twist on points.** If an
endomorphism `γ` of the base change of the atlas fixes the projection to the atlas and composes
the structure morphism with the automorphism of `Spec K` attached to `σ`, then precomposing a
field-valued point with `γ` twists its image in the base change of `X` by `σ`. -/
private theorem map_atlas_pointOfSchemeHom_comp
    (hiU : ∀ (W : BigFppfOver B (Spec (.of K)) hK) (v : W ⟶ Ubar),
      (iU.hom.app (op W) v).left = v.left ≫ pU)
    (σ : K ≃ₐ[k] K)
    (γ : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar ⟶
      (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar)
    (hγfst : γ ≫ B.inclusion.map pU = B.inclusion.map pU)
    (hγsnd : γ ≫ B.inclusion.map Ubar.hom =
      B.inclusion.map Ubar.hom ≫ specMapAlgAut k K σ)
    (κ : Type u) [Field κ] (hκ : B.Contains (Spec (.of κ)))
    (x : Spec (.of κ) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar) :
    FieldValuedPoint.map B (Spec (.of K)) hK _
        (iU.hom ≫ (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f)
        (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)) =
      FieldValuedPoint.galoisTwist B k K hk hK X σ
        (FieldValuedPoint.map B (Spec (.of K)) hK _
          (iU.hom ≫ (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f)
          (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x)) := by
  have hqbase :
      (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).toBase =
        (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).toBase ≫ specMapAlgAut k K σ :=
    (pointOfSchemeHom_toBase B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).trans
      ((Category.assoc x γ (B.inclusion.map Ubar.hom)).trans
        ((congrArg (fun m => x ≫ m) hγsnd).trans
          ((Category.assoc x (B.inclusion.map Ubar.hom) (specMapAlgAut k K σ)).symm.trans
            (congrArg (fun m => m ≫ specMapAlgAut k K σ)
              (pointOfSchemeHom_toBase B (Spec (.of K)) hK Ubar κ hκ x).symm))))
  have hbase :
      (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).toBase ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).toBase ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
    (congrArg (fun m => m ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) hqbase).trans
      ((Category.assoc _ (specMapAlgAut k K σ)
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).trans
        (congrArg (fun m => (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).toBase ≫ m)
          (specMapAlgAut_comp_structureMap k K σ)))
  have hhom :
      ((pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).siteObject B _ hK _).hom ≫
          fieldExtensionMap B k K hk hK =
        ((pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).siteObject B _ hK _).hom ≫
          fieldExtensionMap B k K hk hK := by
    refine B.inclusion.map_injective ?_
    refine (B.inclusion.map_comp _ _).trans ?_
    refine Eq.trans ?_ (B.inclusion.map_comp _ _).symm
    rw [map_fieldExtensionMap]
    exact hbase
  have hsite :
      (Over.map (fieldExtensionMap B k K hk hK)).obj
          ((pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).siteObject B _ hK _) =
        (Over.map (fieldExtensionMap B k K hk hK)).obj
          ((pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).siteObject B _ hK _) :=
    congrArg Over.mk hhom
  have hleftEq :
      (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).value.left ≫ pU =
        (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).value.left ≫ pU := by
    have h1 : B.inclusion.map (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).value.left = x :=
      pointOfSchemeHom_value_left B (Spec (.of K)) hK Ubar κ hκ x
    have h2 : B.inclusion.map
        (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).value.left = x ≫ γ :=
      pointOfSchemeHom_value_left B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)
    refine B.inclusion.map_injective ?_
    change B.inclusion.map (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).value.left ≫
        B.inclusion.map pU =
      B.inclusion.map (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).value.left ≫
        B.inclusion.map pU
    rw [h1, h2]
    exact (Category.assoc x γ (B.inclusion.map pU)).trans
      (congrArg (fun m => x ≫ m) hγfst)
  refine fieldValuedPoint_eq rfl HEq.rfl ?_ ?_
  · rw [FieldValuedPoint.galoisTwist_toBase]
    exact heq_of_eq hqbase
  · refine HEq.trans ?_ (FieldValuedPoint.galoisTwist_value_heq B k K hk hK X σ _).symm
    refine OverShriek.natTrans_app_heq f (congrArg op hsite) ?_
    refine OverShriek.overHom_heq_of_left hsite _ _ (heq_of_eq ?_)
    exact (hiU _ (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ (x ≫ γ)).value).trans
      (hleftEq.trans (hiU _ (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x).value).symm)

/-- **Membership in a closed subset of the base changed atlas is unchanged by a twist.** With
`γ` as above, a closed subset of the base changed atlas cut out by a Galois-invariant subset of
the points of the base change of `X` is invariant under `γ`. -/
private theorem mem_iff_of_comp_twist
    (Tbar : Set (points B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)))
    (hstable : ∀ σ : K ≃ₐ[k] K, galoisPointsAction B k K hk hK X σ ⁻¹' Tbar = Tbar)
    (hiU : ∀ (W : BigFppfOver B (Spec (.of K)) hK) (v : W ⟶ Ubar),
      (iU.hom.app (op W) v).left = v.left ≫ pU)
    (Vbar : Set ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar))
    (hVbar : ∀ a : FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj Ubar),
      (schemePoint B (Spec (.of K)) hK Ubar a ∈ Vbar ↔
        (FieldValuedPoint.map B (Spec (.of K)) hK _
          (iU.hom ≫ (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f)
          a).class B (Spec (.of K)) hK _ ∈ Tbar))
    (σ : K ≃ₐ[k] K)
    (γ : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar ⟶
      (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar)
    (hγfst : γ ≫ B.inclusion.map pU = B.inclusion.map pU)
    (hγsnd : γ ≫ B.inclusion.map Ubar.hom =
      B.inclusion.map Ubar.hom ≫ specMapAlgAut k K σ)
    (κ : Type u) [Field κ] (hκ : B.Contains (Spec (.of κ)))
    (x : Spec (.of κ) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar)
    (y : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar)
    (hxy : x (IsLocalRing.closedPoint κ) = y) :
    (γ y ∈ Vbar ↔ y ∈ Vbar) := by
  subst hxy
  have key : ∀ x' : Spec (.of κ) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Ubar,
      (x' (IsLocalRing.closedPoint κ) ∈ Vbar ↔
        (FieldValuedPoint.map B (Spec (.of K)) hK _
          (iU.hom ≫ (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f)
          (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x')).class B (Spec (.of K)) hK _ ∈
            Tbar) := fun x' => by
    rw [← schemePoint_pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x']
    exact hVbar _
  change (x ≫ γ) (IsLocalRing.closedPoint κ) ∈ Vbar ↔ _
  rw [key, key, map_atlas_pointOfSchemeHom_comp B k K hk hK X U f Ubar pU iU hiU σ γ hγfst hγsnd
    κ hκ x, ← galoisPointsAction_class]
  have hs := Set.ext_iff.mp (hstable σ)
    ((FieldValuedPoint.map B (Spec (.of K)) hK _
      (iU.hom ≫ (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f)
      (pointOfSchemeHom B (Spec (.of K)) hK Ubar κ hκ x)).class B (Spec (.of K)) hK _)
  rw [Set.mem_preimage] at hs
  exact hs

end Twist

/-! ### Base change of an atlas along the extension of base fields -/

section BaseChangeAtlas

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  [HasPullbacks B.Schemes]

/-- The base change to `K` of an object of the big fppf site over `k`. -/
private noncomputable abbrev baseChangeObj (U : BigFppfOver B (Spec (.of k)) hk) :
    BigFppfOver B (Spec (.of K)) hK :=
  (Over.pullback (fieldExtensionMap B k K hk hK)).obj U

/-- The projection of the base change to the original object. -/
private noncomputable abbrev baseChangeProj (U : BigFppfOver B (Spec (.of k)) hk) :
    (baseChangeObj B k K hk hK U).left ⟶ U.left :=
  pullback.fst U.hom (fieldExtensionMap B k K hk hK)

/-- The base change of an object sits in a fibre product square of schemes over the extension of
base fields. -/
private theorem isPullback_baseChangeProj (U : BigFppfOver B (Spec (.of k)) hk) :
    IsPullback (B.inclusion.map (baseChangeProj B k K hk hK U))
      (B.inclusion.map (baseChangeObj B k K hk hK U).hom) (B.inclusion.map U.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have h := IsPullback.map B.inclusion
    (IsPullback.of_hasPullback U.hom (fieldExtensionMap B k K hk hK))
  rwa [map_fieldExtensionMap] at h

variable (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
  (U : BigFppfOver B (Spec (.of k)) hk) (f : yoneda.obj U ⟶ X)

/-- The base change to `K` of a morphism from a represented presheaf to `X`. -/
private noncomputable abbrev baseChangeAtlas :
    yoneda.obj (baseChangeObj B k K hk hK U) ⟶
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X :=
  (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U).hom ≫
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f

/-- Restriction to the base field of a field-valued point of the base changed atlas lies, on
underlying scheme points, above the projection to the atlas. -/
private theorem pointsOfRelocalizeRestrict_baseChangeAtlas
    (a : FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj (baseChangeObj B k K hk hK U))) :
    pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) X
        ((FieldValuedPoint.map B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f)
          a).class B (Spec (.of K)) hK _) =
      pointsMap B (Spec (.of k)) hk (yoneda.obj U) f
        ((FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
          (fieldExtensionMap B k K hk hK) (yoneda.obj U)
          (FieldValuedPoint.map B (Spec (.of K)) hK _
            (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U).hom
            a)).class B (Spec (.of k)) hk (yoneda.obj U)) := rfl

/-- The scheme point underlying the restriction to the base field of a field-valued point of the
base changed atlas is its image under the projection to the atlas. -/
private theorem pointsToScheme_ofRelocalizeRestrict
    (a : FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj (baseChangeObj B k K hk hK U))) :
    pointsToScheme B (Spec (.of k)) hk U
        ((FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
          (fieldExtensionMap B k K hk hK) (yoneda.obj U)
          (FieldValuedPoint.map B (Spec (.of K)) hK _
            (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U).hom
            a)).class B (Spec (.of k)) hk (yoneda.obj U)) =
      B.inclusion.map (baseChangeProj B k K hk hK U)
        (schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK U) a) := by
  change B.inclusion.map
    ((OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U).hom.app
      (op (a.siteObject B (Spec (.of K)) hK _)) a.value).left _ = _
  rw [OverShriek.restrictYonedaIso_hom_app_left, B.inclusion.map_comp]
  rfl

/-- The base change of a morphism to `X` which is surjective after every representable base
change is again surjective after every representable base change. -/
private theorem presheaf_surjective_baseChangeAtlas
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk))) f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of K)) hK)))
      (baseChangeAtlas B k K hk hK X U f) := by
  have _ : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (OverShriek.relative_relocalizeRestrict_map (fieldExtensionMap B k K hk hK)
      (inverseImage_restrictReindexSnd B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) (@Surjective.{u})) hf)

end BaseChangeAtlas

/-! ### Descent of the invariant closed subset along an atlas -/

section Descent

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  [HasPullbacks B.Schemes]
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
  (Tbar : Set (points B (Spec (.of K)) hK
    ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)))
  (U : BigFppfOver B (Spec (.of k)) hk) (f : yoneda.obj U ⟶ X)

/-- **The scheme-level descent of the invariant closed subset.** For a morphism `f : h_U ⟶ X`
from a represented presheaf there is a closed subset of the scheme `U` cutting out, on the
field-valued points of the base change of `U`, the preimage of the given invariant closed
subset. -/
private theorem exists_isClosed_preimage_baseChangeAtlas [IsGalois k K]
    (hTbar : @IsClosed _ (pointTopology B (Spec (.of K)) hK _) Tbar)
    (hstable : ∀ σ : K ≃ₐ[k] K, galoisPointsAction B k K hk hK X σ ⁻¹' Tbar = Tbar) :
    ∃ T : Set ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U), IsClosed T ∧
      ∀ a : FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj (baseChangeObj B k K hk hK U)),
        (B.inclusion.map (baseChangeProj B k K hk hK U)
            (schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK U) a) ∈ T ↔
          (FieldValuedPoint.map B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f)
            a).class B (Spec (.of K)) hK _ ∈ Tbar) := by
  classical
  let : TopologicalSpace (points B (Spec (.of K)) hK
    (yoneda.obj (baseChangeObj B k K hk hK U))) :=
    pointTopology B (Spec (.of K)) hK (yoneda.obj (baseChangeObj B k K hk hK U))
  let : TopologicalSpace (points B (Spec (.of K)) hK
    ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) :=
    pointTopology B (Spec (.of K)) hK _
  obtain ⟨Vbar, hVbar, hVbarmem⟩ := exists_isClosed_pointsToScheme_preimage B (Spec (.of K))
    hK (baseChangeObj B k K hk hK U)
    (pointsMap B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f) ⁻¹' Tbar)
    (hTbar.preimage (continuous_pointsMap B (Spec (.of K)) hK
      (baseChangeAtlas B k K hk hK X U f)))
  have hmemVbar : ∀ a : FieldValuedPoint B (Spec (.of K)) hK
      (yoneda.obj (baseChangeObj B k K hk hK U)),
      (schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK U) a ∈ Vbar ↔
        (FieldValuedPoint.map B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f)
          a).class B (Spec (.of K)) hK _ ∈ Tbar) := by
    intro a
    have h := Set.ext_iff.mp hVbarmem (a.class B (Spec (.of K)) hK _)
    simp only [Set.mem_preimage, pointsMap_class] at h
    exact h
  obtain ⟨e, heFst, heSnd⟩ :
      ∃ e : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj (baseChangeObj B k K hk hK U) ≅
        pullback (B.inclusion.map U.hom) (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        e.hom ≫ pullback.fst (B.inclusion.map U.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          B.inclusion.map (baseChangeProj B k K hk hK U) ∧
        e.hom ≫ pullback.snd (B.inclusion.map U.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          B.inclusion.map (baseChangeObj B k K hk hK U).hom :=
    ⟨(isPullback_baseChangeProj B k K hk hK U).isoPullback,
      (isPullback_baseChangeProj B k K hk hK U).isoPullback_hom_fst,
      (isPullback_baseChangeProj B k K hk hK U).isoPullback_hom_snd⟩
  have hmemA : ∀ w, (w ∈ Scheme.homeoOfIso e '' Vbar ↔ e.inv w ∈ Vbar) := by
    intro w
    constructor
    · rintro ⟨w', hw', rfl⟩
      change e.inv (e.hom w') ∈ Vbar
      rwa [Scheme.hom_inv_apply]
    · exact fun hw => ⟨e.inv w, hw, Scheme.inv_hom_apply e w⟩
  have hAstable : ∀ σ : K ≃ₐ[k] K,
      galoisBaseChangeMap k K ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U)
          (B.inclusion.map U.hom) σ ⁻¹' (Scheme.homeoOfIso e '' Vbar) =
        Scheme.homeoOfIso e '' Vbar := by
    intro σ
    set γ := e.hom ≫ galoisBaseChangeMap k K
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U) (B.inclusion.map U.hom) σ ≫ e.inv with hγ
    have hγfst : γ ≫ B.inclusion.map (baseChangeProj B k K hk hK U) =
        B.inclusion.map (baseChangeProj B k K hk hK U) := by
      rw [hγ, Category.assoc, Category.assoc, e.inv_comp_eq.mpr heFst.symm]
      exact (congrArg (e.hom ≫ ·) (galoisBaseChangeMap_fst k K _ _ σ)).trans heFst
    have hγsnd : γ ≫ B.inclusion.map (baseChangeObj B k K hk hK U).hom =
        B.inclusion.map (baseChangeObj B k K hk hK U).hom ≫ specMapAlgAut k K σ := by
      rw [hγ, Category.assoc, Category.assoc, e.inv_comp_eq.mpr heSnd.symm]
      exact (congrArg (e.hom ≫ ·) (galoisBaseChangeMap_snd k K _ _ σ)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) heSnd))
    have hkey : ∀ y, γ y ∈ Vbar ↔ y ∈ Vbar := fun y => by
      have hκ : B.Contains (Spec
          (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
            (baseChangeObj B k K hk hK U)).residueField y)) :=
        B.residueField_spec_contains (baseChangeObj B k K hk hK U).left.property y
      exact mem_iff_of_comp_twist B k K hk hK X U f (baseChangeObj B k K hk hK U)
        (baseChangeProj B k K hk hK U)
        (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U) Tbar hstable
        (fun W v => OverShriek.restrictYonedaIso_hom_app_left
          (fieldExtensionMap B k K hk hK) U W v)
        Vbar hmemVbar σ _ hγfst hγsnd _ hκ
        (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
          (baseChangeObj B k K hk hK U)).fromSpecResidueField y) y
        (Scheme.fromSpecResidueField_apply y _)
    ext z
    rw [Set.mem_preimage, hmemA, hmemA, ← hkey (e.inv z)]
    simp [hγ]
  obtain ⟨T, hTclosed, hTpre⟩ :=
    _root_.AlgebraicGeometry.exists_closed_subset_with_preimage_eq_of_galois_invariant k K
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U) (B.inclusion.map U.hom)
      (Scheme.homeoOfIso e '' Vbar) ((Scheme.homeoOfIso e).isClosedMap _ hVbar) hAstable
  refine ⟨T, hTclosed, fun a => ?_⟩
  have hmemT : ∀ w, (B.inclusion.map (baseChangeProj B k K hk hK U) w ∈ T ↔ w ∈ Vbar) := by
    intro w
    have h := Set.ext_iff.mp hTpre (e.hom w)
    rw [← heFst, Scheme.Hom.comp_apply]
    rwa [Set.mem_preimage, hmemA, Scheme.hom_inv_apply] at h
  rw [hmemT, hmemVbar]

/-- **The descended subset is constant on the fibres of the atlas.** Two points of the atlas
with the same image in `X` are described by a point of the kernel pair, whose own base change to
`K` provides compatible lifts to the base change of the atlas. -/
private theorem mem_iff_of_pointsMap_eq (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (R : BigFppfOver B (Spec (.of k)) hk) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (T : Set ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U))
    (hT : ∀ a : FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj (baseChangeObj B k K hk hK U)),
      (B.inclusion.map (baseChangeProj B k K hk hK U)
          (schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK U) a) ∈ T ↔
        (FieldValuedPoint.map B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f)
          a).class B (Spec (.of K)) hK _ ∈ Tbar))
    (x y : points B (Spec (.of k)) hk (yoneda.obj U))
    (hxy : pointsMap B (Spec (.of k)) hk (yoneda.obj U) f x =
      pointsMap B (Spec (.of k)) hk (yoneda.obj U) f y) :
    (pointsToScheme B (Spec (.of k)) hk U x ∈ T ↔
      pointsToScheme B (Spec (.of k)) hk U y ∈ T) := by
  classical
  have _ : Subsingleton (Spec (CommRingCat.of k) : Scheme.{u}) := inferInstance
  let RA : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj R, isAlgebraicSpace_yoneda B (Spec (.of k)) hk R⟩
  let UA : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of k)) hk U⟩
  let XA : AlgebraicSpaces B (Spec (.of k)) hk := ⟨X, hX⟩
  let tA : RA ⟶ UA := ObjectProperty.homMk (yoneda.map t)
  let sA : RA ⟶ UA := ObjectProperty.homMk (yoneda.map s)
  let fA : UA ⟶ XA := ObjectProperty.homMk f
  have hsq : IsPullback tA sA fA fA :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B (Spec (.of k)) hk G)) hR
  obtain ⟨r, hrt, hrs⟩ := exists_point_of_isPullback B (Spec (.of k)) hk hsq x y hxy
  obtain ⟨r₀, rfl⟩ := Quot.exists_rep r
  have hrt' : pointsMap B (Spec (.of k)) hk (yoneda.obj R) (yoneda.map t)
      (r₀.class B (Spec (.of k)) hk (yoneda.obj R)) = x := hrt
  have hrs' : pointsMap B (Spec (.of k)) hk (yoneda.obj R) (yoneda.map s)
      (r₀.class B (Spec (.of k)) hk (yoneda.obj R)) = y := hrs
  -- lift the scheme point of the kernel pair to its base change
  have _ : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  obtain ⟨z₁, hz₁⟩ :=
    (AlgebraicGeometry.surjective_iff (pullback.fst (B.inclusion.map R.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).mp inferInstance
      (schemePoint B (Spec (.of k)) hk R r₀)
  obtain ⟨eR, heR⟩ :
      ∃ eR : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj (baseChangeObj B k K hk hK R) ≅
        pullback (B.inclusion.map R.hom) (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        eR.hom ≫ pullback.fst (B.inclusion.map R.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          B.inclusion.map (baseChangeProj B k K hk hK R) :=
    ⟨(isPullback_baseChangeProj B k K hk hK R).isoPullback,
      (isPullback_baseChangeProj B k K hk hK R).isoPullback_hom_fst⟩
  have hzbar : B.inclusion.map (baseChangeProj B k K hk hK R) (eR.inv z₁) =
      schemePoint B (Spec (.of k)) hk R r₀ := by
    rwa [← heR, Scheme.Hom.comp_apply, Scheme.inv_hom_apply]
  have hκ : B.Contains (Spec
      (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
        (baseChangeObj B k K hk hK R)).residueField (eR.inv z₁))) :=
    B.residueField_spec_contains (baseChangeObj B k K hk hK R).left.property (eR.inv z₁)
  have hrbarpt : schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK R)
      (pointOfSchemeHom B (Spec (.of K)) hK (baseChangeObj B k K hk hK R) _ hκ
        (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
          (baseChangeObj B k K hk hK R)).fromSpecResidueField (eR.inv z₁))) = eR.inv z₁ :=
    (schemePoint_pointOfSchemeHom B (Spec (.of K)) hK (baseChangeObj B k K hk hK R) _ hκ
      (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
        (baseChangeObj B k K hk hK R)).fromSpecResidueField (eR.inv z₁))).trans
      (Scheme.fromSpecResidueField_apply (eR.inv z₁) _)
  -- the two images in the base change of `X` coincide
  have hnat : ∀ w : R ⟶ U,
      yoneda.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map w) ≫
          baseChangeAtlas B k K hk hK X U f =
        (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) R).hom ≫
          (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map
            (yoneda.map w ≫ f) := by
    intro w
    rw [show baseChangeAtlas B k K hk hK X U f =
      (OverShriek.restrictYonedaIso (fieldExtensionMap B k K hk hK) U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f from rfl,
      ← Category.assoc, OverShriek.restrictYonedaIso_hom_naturality, Category.assoc,
      ← Functor.map_comp]
  have himage : FieldValuedPoint.map B (Spec (.of K)) hK _
        (baseChangeAtlas B k K hk hK X U f)
        (FieldValuedPoint.map B (Spec (.of K)) hK _
          (yoneda.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map t))
          (pointOfSchemeHom B (Spec (.of K)) hK (baseChangeObj B k K hk hK R) _ hκ
            (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
              (baseChangeObj B k K hk hK R)).fromSpecResidueField (eR.inv z₁)))) =
      FieldValuedPoint.map B (Spec (.of K)) hK _ (baseChangeAtlas B k K hk hK X U f)
        (FieldValuedPoint.map B (Spec (.of K)) hK _
          (yoneda.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map s))
          (pointOfSchemeHom B (Spec (.of K)) hK (baseChangeObj B k K hk hK R) _ hκ
            (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
              (baseChangeObj B k K hk hK R)).fromSpecResidueField (eR.inv z₁)))) := by
    rw [← FieldValuedPoint.map_comp, ← FieldValuedPoint.map_comp, hnat t, hnat s, hR.w]
  -- the two scheme points above `x` and `y`
  have hproj : ∀ w : R ⟶ U, pointsToScheme B (Spec (.of k)) hk U
      (pointsMap B (Spec (.of k)) hk (yoneda.obj R) (yoneda.map w)
        (r₀.class B (Spec (.of k)) hk (yoneda.obj R))) =
      B.inclusion.map (baseChangeProj B k K hk hK U)
        (schemePoint B (Spec (.of K)) hK (baseChangeObj B k K hk hK U)
          (FieldValuedPoint.map B (Spec (.of K)) hK _
            (yoneda.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map w))
            (pointOfSchemeHom B (Spec (.of K)) hK (baseChangeObj B k K hk hK R) _ hκ
              (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
                (baseChangeObj B k K hk hK R)).fromSpecResidueField (eR.inv z₁))))) := by
    intro w
    rw [pointsMap_class]
    change schemePoint B (Spec (.of k)) hk U
      (FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj R) (yoneda.map w) r₀) = _
    rw [schemePoint_map_yoneda, schemePoint_map_yoneda, hrbarpt]
    change B.inclusion.map w.left (schemePoint B (Spec (.of k)) hk R r₀) =
      B.inclusion.map (baseChangeProj B k K hk hK U)
        (B.inclusion.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map w).left
          (eR.inv z₁))
    have hcomm : B.inclusion.map (baseChangeProj B k K hk hK R) ≫ B.inclusion.map w.left =
        B.inclusion.map ((Over.pullback (fieldExtensionMap B k K hk hK)).map w).left ≫
          B.inclusion.map (baseChangeProj B k K hk hK U) := by
      rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, OverShriek.pullback_map_left_comp_fst]
    rw [← hzbar]
    exact congrArg (fun m => m (eR.inv z₁)) hcomm
  rw [← hrt', ← hrs', hproj t, hproj s, hT, hT, himage]

end Descent

/-! ### The descent statement -/

/-- **Stacks 0A16.** Let `K/k` be a Galois extension whose spectra lie in the chosen big fppf
site, and let `X` be an algebraic space over `k`. A closed subset of the points of the base
change `X_K` which is invariant under the action of every `k`-algebra automorphism of `K` is the
inverse image of a closed subset of the points of `X`. -/
@[stacks 0A16]
theorem exists_closed_subset_with_preimage_eq_of_galois_invariant (B : BigFppfSite.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (Tbar : Set (points B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)))
    (hTbar : @IsClosed _ (pointTopology B (Spec (.of K)) hK _) Tbar)
    (hstable : ∀ σ : K ≃ₐ[k] K, galoisPointsAction B k K hk hK X σ ⁻¹' Tbar = Tbar) :
    ∃ T : Set (points B (Spec (.of k)) hk X),
      @IsClosed _ (pointTopology B (Spec (.of k)) hk X) T ∧
      pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
          (fieldExtensionMap B k K hk hK) X ⁻¹' T = Tbar := by
  classical
  have _ : HasPullbacks B.Schemes := inferInstance
  have _ : HasPullbacks (BigFppfOver B (Spec (.of k)) hk) := inferInstance
  have _ : HasBinaryProducts (BigFppfOver B (Spec (.of k)) hk) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : TopologicalSpace (points B (Spec (.of k)) hk X) := pointTopology B (Spec (.of k)) hk X
  obtain ⟨U, f, hfSurj, hfEtale⟩ := hX.exists_atlas
  let : TopologicalSpace (points B (Spec (.of k)) hk (yoneda.obj U)) :=
    pointTopology B (Spec (.of k)) hk (yoneda.obj U)
  obtain ⟨T, hTclosed, hTmem⟩ := exists_isClosed_preimage_baseChangeAtlas B k K hk hK X Tbar
    U f hTbar hstable
  have hrep : yoneda.relativelyRepresentable f :=
    Functor.relativelyRepresentable.of_diag hX.diagonal_representable f
  have hsat := mem_iff_of_pointsMap_eq B k K hk hK X Tbar U f hX (hrep.pullback f)
    (hrep.fst' f) (hrep.snd f) (hrep.isPullback' f) T hTmem
  have hfOpen : @IsOpenMap _ _ (pointTopology B (Spec (.of k)) hk (yoneda.obj U))
      (pointTopology B (Spec (.of k)) hk X)
      (pointsMap B (Spec (.of k)) hk (yoneda.obj U) f) :=
    isOpenMap_pointsMap_of_etale B (Spec (.of k)) hk hX U f hfEtale
  have hfSurjPts : Function.Surjective (pointsMap B (Spec (.of k)) hk (yoneda.obj U) f) :=
    (surjective_iff_surjective_pointsMap B (Spec (.of k)) hk X hX U f).mp hfSurj
  have hquot := hfOpen.isQuotientMap (continuous_pointsMap B (Spec (.of k)) hk f) hfSurjPts
  have hpre : pointsMap B (Spec (.of k)) hk (yoneda.obj U) f ⁻¹'
      (pointsMap B (Spec (.of k)) hk (yoneda.obj U) f ''
        (pointsToScheme B (Spec (.of k)) hk U ⁻¹' T)) =
      pointsToScheme B (Spec (.of k)) hk U ⁻¹' T := by
    ext w
    exact ⟨fun ⟨w', hw', hww'⟩ => (hsat w w' hww'.symm).mpr hw', fun hw => ⟨w, hw, rfl⟩⟩
  refine ⟨pointsMap B (Spec (.of k)) hk (yoneda.obj U) f ''
    (pointsToScheme B (Spec (.of k)) hk U ⁻¹' T), ?_, ?_⟩
  · refine hquot.isCoinducing.isClosed_preimage.mp ?_
    rw [hpre]
    exact isClosed_pointsToScheme_preimage B (Spec (.of k)) hk U T hTclosed
  have hfbarSurj : Function.Surjective (pointsMap B (Spec (.of K)) hK _
      (baseChangeAtlas B k K hk hK X U f)) :=
    (surjective_iff_surjective_pointsMap B (Spec (.of K)) hK _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) X hX) _ (baseChangeAtlas B k K hk hK X U f)).mp
      (presheaf_surjective_baseChangeAtlas B k K hk hK X U f hfSurj)
  ext w
  obtain ⟨z, hz⟩ := hfbarSurj w
  obtain ⟨a, rfl⟩ := Quot.exists_rep z
  rw [← hz, Set.mem_preimage, pointsMap_class, pointsOfRelocalizeRestrict_baseChangeAtlas,
    ← Set.mem_preimage, hpre, Set.mem_preimage, pointsToScheme_ofRelocalizeRestrict]
  exact hTmem a

end AlgebraicGeometry.Space

end
