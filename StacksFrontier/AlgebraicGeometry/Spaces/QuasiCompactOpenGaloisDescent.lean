module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# Quasi-compact opens of a base change along an algebraic extension

Let `X` be an algebraic space over a field `k` and let `K/k` be a possibly infinite algebraic
extension. A quasi-compact open subspace of the base change `X_K` already lives over a finite
subextension: it is the base change of a quasi-compact open subspace of `X_E` for some finite
subextension `E` of `K/k`. When `K/k` is Galois this forces the open subspace to be invariant
under an open subgroup of `Gal(K/k)`, namely the subgroup fixing `E` pointwise.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeRestrictSubfunctor` is the base change of a subfunctor
  along a morphism of the base.
* `AlgebraicGeometry.Space.galoisOpenSubfunctor` is an open subspace of `X_K`, viewed as a
  subfunctor of the presheaf over `k` carrying the action of the automorphism group.

## Main results

* `CategoryTheory.OverShriek.preimage_eqToHom_eq_iff_eq_transport`: a subfunctor is the
  transport of another one along an equality of presheaves exactly when its preimage along the
  induced isomorphism is that subfunctor.
* `AlgebraicGeometry.Space.contains_specIntermediateField`: the spectrum of an intermediate
  field of an extension lying in the chosen big fppf site again lies in that site.
* `AlgebraicGeometry.Space.relocalizeRestrict_fieldExtensionMap_comp`: the base change of `X`
  to `K` is the base change to `K` of its base change to an intermediate field.
* `AlgebraicGeometry.Space.exists_finite_subextension_descending_isQuasiCompact_open`: a
  quasi-compact open subspace of `X_K` is the base change of a quasi-compact open subspace of
  `X_E` for a finite subextension `E` of `K/k`.
* `AlgebraicGeometry.Space.exists_open_subgroup_fixing_isQuasiCompact_open`: for `K/k` Galois, a
  quasi-compact open subspace of `X_K` is fixed by an open subgroup of `Gal(K/k)`.

## References

* [Stacks Project, Tag 0A15](https://stacks.math.columbia.edu/tag/0A15)
* [Stacks Project, Tag 04KU](https://stacks.math.columbia.edu/tag/04KU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C]

/-! ### Base change of a subfunctor -/

/-- The base change of a subfunctor along a morphism of the base. Its sections over an object `W`
of `C/V` are the sections of `G` over the image of `W` in `C/U`. -/
def relocalizeRestrictSubfunctor {U V : C} (f : V ⟶ U) {F : (Over U)ᵒᵖ ⥤ Type v}
    (G : Subfunctor F) : Subfunctor ((relocalizeRestrict f).obj F) where
  obj W := G.obj ((Over.map f).op.obj W)
  map i := G.map ((Over.map f).op.map i)

/-- The presheaf underlying the base change of a subfunctor is the base change of the presheaf
underlying it. -/
theorem toFunctor_relocalizeRestrictSubfunctor {U V : C} (f : V ⟶ U)
    {F : (Over U)ᵒᵖ ⥤ Type v} (G : Subfunctor F) :
    (relocalizeRestrictSubfunctor f G).toFunctor = (relocalizeRestrict f).obj G.toFunctor :=
  rfl

/-- The inclusion of the base change of a subfunctor is the base change of its inclusion. -/
theorem ι_relocalizeRestrictSubfunctor {U V : C} (f : V ⟶ U) {F : (Over U)ᵒᵖ ⥤ Type v}
    (G : Subfunctor F) :
    (relocalizeRestrictSubfunctor f G).ι = (relocalizeRestrict f).map G.ι :=
  rfl

/-- Restriction along a composite is equal, as a presheaf, to the composite of the restrictions. -/
theorem relocalizeRestrict_obj_comp {U₀ U₁ U₂ : C} (g₁ : U₂ ⟶ U₁) (g₂ : U₁ ⟶ U₀) (g : U₂ ⟶ U₀)
    (h : g₁ ≫ g₂ = g) (F : (Over U₀)ᵒᵖ ⥤ Type v) :
    (relocalizeRestrict g₁).obj ((relocalizeRestrict g₂).obj F) =
      (relocalizeRestrict g).obj F := by
  subst h
  change (Over.map g₁).op ⋙ (Over.map g₂).op ⋙ F = (Over.map (g₁ ≫ g₂)).op ⋙ F
  rw [Over.mapComp_eq]
  rfl

/-! ### Transport along an equality of presheaves -/

/-- Applying the morphism of presheaves given by an equality does not change a section. -/
theorem eqToHom_app_heq {D : Type*} [Category D] {F G : Dᵒᵖ ⥤ Type u} (e : F = G)
    (W : Dᵒᵖ) (x : F.obj W) : HEq ((eqToHom e).app W x) x := by
  cases e
  rfl

/-- A subfunctor of the right-hand presheaf is the transport of a subfunctor of the left-hand one
exactly when its preimage along the induced isomorphism is that subfunctor. -/
theorem preimage_eqToHom_eq_iff_eq_transport {D : Type u} [Category.{v} D]
    {F G : Dᵒᵖ ⥤ Type v} (e : F = G) (A : Subfunctor F) (V : Subfunctor G) :
    Subfunctor.preimage V (eqToHom e) = A ↔ V = e ▸ A := by
  cases e
  simp

/-- A natural transformation sends heterogeneously equal sections over equal objects to
heterogeneously equal sections. -/
theorem natTrans_app_heq {D : Type*} [Category D] {F G : D ⥤ Type u} (f : F ⟶ G)
    {T T' : D} (h : T = T') {x : F.obj T} {y : F.obj T'} (hxy : HEq x y) :
    HEq (f.app T x) (f.app T' y) := by
  cases h
  cases hxy
  rfl

/-- Two morphisms of a slice category out of equal objects agree as soon as their underlying
morphisms do. -/
theorem overHom_heq_of_left {D : Type*} [Category D] {S : D} {T T' A : Over S}
    (h : T = T') (f : T ⟶ A) (f' : T' ⟶ A) (hf : HEq f.left f'.left) : HEq f f' := by
  cases h
  exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq hf))

/-- Two morphisms out of a representable presheaf, one of them transported along an equality of
presheaves, agree as soon as the sections they name do. -/
private theorem natTrans_eq_of_app_id_heq {D : Type u} [Category.{v} D] {F G : Dᵒᵖ ⥤ Type v}
    {T : D} (e : F = G) (f : yoneda.obj T ⟶ F) (g : yoneda.obj T ⟶ G)
    (h : HEq (f.app (op T) (𝟙 T)) (g.app (op T) (𝟙 T))) : f ≫ eqToHom e = g :=
  yonedaEquiv.injective (eq_of_heq ((eqToHom_app_heq e _ _).trans h))

/-- The section named by a morphism out of a representable presheaf precomposed with the Yoneda
image of a morphism. -/
theorem yoneda_map_comp_app_id {D : Type u} [Category.{v} D] {G : Dᵒᵖ ⥤ Type v} {T W : D}
    (m : T ⟶ W) (β : yoneda.obj W ⟶ G) :
    (yoneda.map m ≫ β).app (op T) (𝟙 T) = β.app (op T) m := by
  change β.app (op T) (𝟙 T ≫ m) = _
  rw [Category.id_comp]

/-! ### Membership in the image of a relocalized subfunctor -/

/-- A section of the relocalization of a presheaf lies in the image of the relocalization of a
subfunctor exactly when its own section lies in that subfunctor. -/
theorem mem_range_relocalizePresheafFunctor_map_ι {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type v} (G : Subfunctor F) (W : (Over U)ᵒᵖ)
    (x : ((relocalizePresheafFunctor g).obj F).obj W) :
    x ∈ (Subfunctor.range ((relocalizePresheafFunctor g).map G.ι)).obj W ↔
      x.val.snd ∈ G.obj (op (Over.mk x.val.fst)) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.snd.property
  · intro hx
    exact ⟨⟨⟨x.val.fst, ⟨x.val.snd, hx⟩⟩, x.property⟩, rfl⟩

/-- Membership in a subfunctor is insensitive to heterogeneous equality of sections over equal
objects. -/
private theorem mem_heq {D : Type u} [Category.{v} D] {F : D ⥤ Type v} (G : Subfunctor F)
    {T T' : D} (h : T = T') {x : F.obj T} {y : F.obj T'} (hxy : HEq x y) :
    x ∈ G.obj T ↔ y ∈ G.obj T' := by
  cases h
  cases hxy
  rfl

/-- Two sections of a relocalized presheaf whose factorizations agree after composition with a
further morphism of the base, and whose own sections agree, lie together in the image of the
relocalization of a base-changed subfunctor. -/
private theorem mem_range_relocalize_congr {S T U : C} (g : U ⟶ S) (p : U ⟶ T)
    {F : (Over T)ᵒᵖ ⥤ Type v} {G : (Over U)ᵒᵖ ⥤ Type v}
    (e : (relocalizeRestrict p).obj F = G) (A : Subfunctor F) (V : Subfunctor G)
    (hV : Subfunctor.preimage V (eqToHom e) = relocalizeRestrictSubfunctor p A)
    (W : (Over S)ᵒᵖ) (x y : ((relocalizePresheafFunctor g).obj G).obj W)
    (hbase : x.val.fst ≫ p = y.val.fst ≫ p) (hsection : HEq x.val.snd y.val.snd) :
    x ∈ (Subfunctor.range ((relocalizePresheafFunctor g).map V.ι)).obj W ↔
      y ∈ (Subfunctor.range ((relocalizePresheafFunctor g).map V.ι)).obj W := by
  cases e
  simp only [eqToHom_refl, Subfunctor.preimage_id] at hV
  subst hV
  rw [mem_range_relocalizePresheafFunctor_map_ι, mem_range_relocalizePresheafFunctor_map_ι]
  change x.val.snd ∈ A.obj (op (Over.mk (x.val.fst ≫ p))) ↔
    y.val.snd ∈ A.obj (op (Over.mk (y.val.fst ≫ p)))
  exact mem_heq A (congrArg (fun q ↦ op (Over.mk q)) hbase) hsection

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

/-! ### Intermediate fields inside the chosen big fppf site -/

/-- The spectrum of an intermediate field of a field extension whose spectrum lies in the chosen
big fppf site again lies in that site. -/
theorem contains_specIntermediateField (B : BigFppfSite.{u}) {k K : Type u} [Field k] [Field K]
    [Algebra k K] (hK : B.Contains (Spec (.of K))) (E : IntermediateField k K) :
    B.Contains (Spec (.of E)) := by
  have hmk : Cardinal.mk E ≤ Cardinal.mk K :=
    Cardinal.mk_le_of_injective (f := (Subtype.val : E → K)) Subtype.val_injective
  have hsize : (Spec (CommRingCat.of E)).size ≤ (Spec (CommRingCat.of K)).size := by
    rw [Scheme.size_Spec, Scheme.size_Spec]
    exact max_le_max le_rfl hmk
  exact lt_of_le_of_lt hsize hK

/-- The base change of a presheaf over `k` to `K` is the base change to `K` of its base change to
an intermediate field `E`. -/
theorem relocalizeRestrict_fieldExtensionMap_comp (B : BigFppfSite.{u}) (k E K : Type u)
    [Field k] [Field E] [Field K] [Algebra k E] [Algebra E K] [Algebra k K]
    [IsScalarTower k E K] (hk : B.Contains (Spec (.of k))) (hE : B.Contains (Spec (.of E)))
    (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizeRestrict (fieldExtensionMap B E K hE hK)).obj
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X) =
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X :=
  OverShriek.relocalizeRestrict_obj_comp _ _ _ (fieldExtensionMap_comp B k E K hk hE hK) X

/-- The automorphism of `Spec K` attached to an automorphism fixing an intermediate field `E` lies
over `Spec E`. -/
theorem siteMapAlgAut_comp_fieldExtensionMap_of_mem_fixingSubgroup (B : BigFppfSite.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K)))
    (E : IntermediateField k K) (hE : B.Contains (Spec (.of E))) (σ : K ≃ₐ[k] K)
    (hσ : σ ∈ E.fixingSubgroup) :
    siteMapAlgAut B k K hK σ ≫ fieldExtensionMap B E K hE hK =
      fieldExtensionMap B E K hE hK := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, map_siteMapAlgAut, map_fieldExtensionMap, specMapAlgAut,
    ← Spec.map_comp, Spec.map_inj]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  refine CommRingCat.hom_ext ?_
  ext x
  exact hσ x.1 x.2

/-- A morphism of the big fppf category over `S` commutes with the structure morphisms to the base,
read on underlying schemes. -/
private theorem toScheme_map_comp_hom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W W' : BigFppfOver B S hS} (m : W ⟶ W') :
    (BigFppfOver.toScheme B S hS).map m ≫ B.inclusion.map W'.hom = B.inclusion.map W.hom := by
  change B.inclusion.map m.left ≫ _ = _
  rw [← B.inclusion.map_comp]
  exact congrArg B.inclusion.map (Over.w m)

section Descent

attribute [local instance] pointTopology

/-! ### Open subspaces with equal point sets -/

/-- The image on points of a composite. -/
private theorem range_pointsMap_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H) :
    Set.range (pointsMap B S hS F (f ≫ g)) =
      pointsMap B S hS G g '' Set.range (pointsMap B S hS F f) := by
  rw [pointsMap_comp, Set.range_comp]

/-- Two open subspaces of an algebraic space over `S` with the same set of points are equal. -/
private theorem subfunctor_eq_of_range_pointsMap_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A A' : Subfunctor F}
    (hA : IsOpenSubspace B S hS A) (hA' : IsOpenSubspace B S hS A')
    (h : Set.range (pointsMap B S hS A.toFunctor A.ι) =
      Set.range (pointsMap B S hS A'.toFunctor A'.ι)) : A = A' :=
  le_antisymm (le_of_range_pointsMap_ι_subset B S hS hA' h.le)
    (le_of_range_pointsMap_ι_subset B S hS hA h.ge)

/-- Transporting an open subspace along an equality of presheaves gives an open subspace. -/
private theorem isOpenSubspace_transport (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F = G) (A : Subfunctor F)
    (hA : IsOpenSubspace B S hS A) : IsOpenSubspace B S hS (e ▸ A) := by
  cases e
  exact hA

/-- The point set of a transported open subspace, read through the transport. -/
private theorem range_pointsMap_transport (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F = G) (A : Subfunctor F) :
    Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ eqToHom e)) =
      Set.range (pointsMap B S hS (e ▸ A).toFunctor (e ▸ A).ι) := by
  cases e
  simp

/-- The comparison homeomorphism of Stacks 03BX is the comparison bijection. -/
private theorem coe_schemePointsHomeomorph (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS) :
    (schemePointsHomeomorph B S hS U :
        points B S hS (yoneda.obj U) → (BigFppfOver.toScheme B S hS).obj U) =
      pointsToScheme B S hS U := rfl

/-! ### Choosing a quasi-compact open of an étale atlas -/

/-- A compact subset of the target of an open continuous surjection whose preimage is the transport
of an open set covered by compact open sets is the image of a compact open set. -/
private theorem exists_isCompact_isOpen_image_eq {A P F : Type*} [TopologicalSpace A]
    [TopologicalSpace P] [TopologicalSpace F] (e : P ≃ₜ A) (m : P → F) {Z : Set F} {O : Set A}
    (hZ : IsCompact Z) (hm : IsOpenMap m) (hsurj : Function.Surjective m)
    (hchar : ∀ p, m p ∈ Z ↔ e p ∈ O)
    (hbasis : ∀ a ∈ O, ∃ W : Set A, IsOpen W ∧ IsCompact W ∧ a ∈ W ∧ W ⊆ O) :
    ∃ W : Set A, IsOpen W ∧ IsCompact W ∧ m '' (e ⁻¹' W) = Z := by
  classical
  have himage (i : {W : Set A // IsOpen W ∧ IsCompact W ∧ W ⊆ O}) :
      IsOpen (m '' (e ⁻¹' i.1)) := hm _ (i.2.1.preimage e.continuous)
  have hcover : Z ⊆ ⋃ i : {W : Set A // IsOpen W ∧ IsCompact W ∧ W ⊆ O}, m '' (e ⁻¹' i.1) := by
    intro y hy
    obtain ⟨p, rfl⟩ := hsurj y
    obtain ⟨W, hWo, hWc, hpW, hWO⟩ := hbasis (e p) ((hchar p).mp hy)
    exact Set.mem_iUnion.mpr ⟨⟨W, hWo, hWc, hWO⟩, p, hpW, rfl⟩
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover _ himage hcover
  refine ⟨⋃ i ∈ (t : Set {W : Set A // IsOpen W ∧ IsCompact W ∧ W ⊆ O}), (i.1 : Set A),
    isOpen_biUnion fun i _ ↦ i.2.1,
    t.finite_toSet.isCompact_biUnion fun i _ ↦ i.2.2.1, Set.Subset.antisymm ?_ ?_⟩
  · rintro y ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hit, hmem⟩ := Set.mem_iUnion.mp hi
    exact (hchar p).mpr (i.2.2.2 hmem)
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hy)
    obtain ⟨hit, q, hq, hqy⟩ := Set.mem_iUnion.mp hi
    exact ⟨q, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hit, hq⟩⟩, hqy⟩

/-- The affine opens of a scheme form a basis of compact open sets. -/
private theorem exists_isOpen_isCompact_mem_subset {Y : Scheme.{u}} {O : Set Y} (hO : IsOpen O)
    {a : Y} (ha : a ∈ O) :
    ∃ W : Set Y, IsOpen W ∧ IsCompact W ∧ a ∈ W ∧ W ⊆ O := by
  obtain ⟨W, hWaff, haW, hWO⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) ha
  exact ⟨(W : Set Y), W.2, hWaff.isCompact, haW, hWO⟩

/-- The underlying set of the preimage of an open set along a morphism of schemes. -/
private theorem coe_preimage_opens {Y Z : Scheme.{u}} (f : Y ⟶ Z) (W : Z.Opens) :
    (f ⁻¹ᵁ W).carrier = f ⁻¹' W.carrier := rfl

/-- The point set of a quasi-compact open subspace of an algebraic space over `S` is the image of
the points of a compact open subset of a surjective étale atlas. -/
private theorem exists_isCompact_isOpen_atlas_image (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hqS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (V : Subfunctor F) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) :
    ∃ W : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen W ∧ IsCompact W ∧
      pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W) =
        Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  classical
  have hZopen : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2
  have hZcompact : IsCompact (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    have _ : CompactSpace (points B S hS V.toFunctor) :=
      (isQuasiCompactSpace_iff_compactSpace_points B S hS V.toFunctor hV.1).mp hVqc
    rw [← Set.image_univ]
    exact isCompact_univ.image (continuous_pointsMap B S hS V.ι)
  have hmopen : IsOpenMap (pointsMap B S hS (yoneda.obj U) q) :=
    isOpenMap_pointsMap_of_etale B S hS hF U q hqE
  have hmsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) q) :=
    (surjective_iff_surjective_pointsMap B S hS F hF U q).mp hqS
  have hOopen : IsOpen (pointsToScheme B S hS U ''
      (pointsMap B S hS (yoneda.obj U) q ⁻¹'
        Set.range (pointsMap B S hS V.toFunctor V.ι))) :=
    (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U _).mp
      (hZopen.preimage (continuous_pointsMap B S hS q))
  obtain ⟨W, hWopen, hWcompact, hWimage⟩ :=
    exists_isCompact_isOpen_image_eq (schemePointsHomeomorph B S hS U)
      (pointsMap B S hS (yoneda.obj U) q) hZcompact hmopen hmsurj
      (fun p ↦ by
        rw [coe_schemePointsHomeomorph, (injective_pointsToScheme B S hS U).mem_set_image]
        exact Iff.rfl)
      (fun a ha ↦ exists_isOpen_isCompact_mem_subset hOopen ha)
  rw [coe_schemePointsHomeomorph] at hWimage
  exact ⟨W, hWopen, hWcompact, hWimage⟩

/-- A compact open of an étale atlas sweeps out a quasi-compact open subspace, which comes with a
surjective chart from the open subobject of the atlas cutting out that compact open. -/
private theorem exists_isOpenSubspace_isQuasiCompact_image (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hqE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    {W : Set ((BigFppfOver.toScheme B S hS).obj U)} (hWopen : IsOpen W)
    (hWcompact : IsCompact W) (UW : BigFppfOver B S hS) (iW : UW ⟶ U)
    (hiWrange : Set.range ((BigFppfOver.toScheme B S hS).map iW) = W) :
    ∃ VE : Subfunctor F, IsOpenSubspace B S hS VE ∧
      IsQuasiCompactSpace B S hS VE.toFunctor ∧
      ∃ factorVE : yoneda.obj UW ⟶ VE.toFunctor, factorVE ≫ VE.ι = yoneda.map iW ≫ q ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf factorVE := by
  classical
  have hWptsOpen : IsOpen (pointsToScheme B S hS U ⁻¹' W) :=
    hWopen.preimage (schemePointsHomeomorph B S hS U).continuous
  have hWptsCompact : IsCompact (pointsToScheme B S hS U ⁻¹' W) := by
    rw [← coe_schemePointsHomeomorph]
    exact (schemePointsHomeomorph B S hS U).isCompact_preimage.mpr hWcompact
  have hiWpts : Set.range (pointsMap B S hS (yoneda.obj UW) (yoneda.map iW)) =
      pointsToScheme B S hS U ⁻¹' W := by
    rw [range_pointsMap_yoneda_eq_preimage, hiWrange]
  have hIopen : IsOpen (pointsMap B S hS (yoneda.obj U) q ''
      (pointsToScheme B S hS U ⁻¹' W)) :=
    isOpenMap_pointsMap_of_etale B S hS hF U q hqE _ hWptsOpen
  have hIcompact : IsCompact (pointsMap B S hS (yoneda.obj U) q ''
      (pointsToScheme B S hS U ⁻¹' W)) :=
    hWptsCompact.image (continuous_pointsMap B S hS q)
  have hVE := isOpenSubspace_openSubspaceOfPoints B S hS hF
    (pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W)) hIopen
  have hVErange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := F) (pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W))
  have hVEimm : IsImmersion B S hS (openSubspaceOfPoints B S hS F
      (pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W))).ι :=
    isImmersion_of_isOpenImmersion B S hS hVE.2
  refine ⟨openSubspaceOfPoints B S hS F
    (pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W)), hVE, ?_, ?_⟩
  · refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hVE.1).mpr ⟨?_⟩
    refine (isEmbedding_pointsMap_of_isImmersion B S hS hF _ hVEimm).isCompact_iff.mpr ?_
    rwa [Set.image_univ, hVErange]
  · obtain ⟨factorVE, hfactorVE⟩ :=
      (factorsThrough_openSubspace_iff_points B S hS hF
        (isAlgebraicSpace_yoneda B S hS UW) _ hVE (yoneda.map iW ≫ q)).2 (by
        rw [range_pointsMap_comp, hiWpts, hVErange])
    refine ⟨factorVE, hfactorVE, ?_⟩
    have hrangeeq : Set.range (pointsMap B S hS (yoneda.obj UW) (yoneda.map iW ≫ q)) =
        pointsMap B S hS (yoneda.obj U) q '' (pointsToScheme B S hS U ⁻¹' W) := by
      rw [range_pointsMap_comp, hiWpts]
    refine (surjective_iff_surjective_pointsMap B S hS _ hVE.1 UW factorVE).2 fun z ↦ ?_
    obtain ⟨y, hy⟩ := hrangeeq.ge (hVErange.le (Set.mem_range_self z))
    refine ⟨y, injective_pointsMap_of_isImmersion B S hS hF _ hVEimm ?_⟩
    rwa [← pointsMap_comp_apply, hfactorVE]

/-! ### Base change of an étale atlas -/

/-- Étaleness of morphisms of schemes is invariant under isomorphisms. -/
private theorem respectsIso_etale :
    MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- The base change of a morphism of presheaves along a morphism of the base inherits any property
of morphisms of schemes invariant under isomorphisms. -/
private theorem presheaf_relocalizeRestrict_atlas (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (Q : MorphismProperty Scheme.{u}) (hQ : Q.RespectsIso)
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (U : BigFppfOver B S' hS')
    (q : yoneda.obj U ⟶ F)
    (hq : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S' hS')).presheaf q)
    (UB : BigFppfOver B S hS)
    (iso : yoneda.obj UB ≅ (OverShriek.relocalizeRestrict g).obj (yoneda.obj U)) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (iso.hom ≫ (OverShriek.relocalizeRestrict g).map q) := by
  have _ : Q.RespectsIso := hQ
  have _ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (OverShriek.relative_relocalizeRestrict_map g
      (inverseImage_restrictReindexSnd B S S' hS hS' g Q) hq)

/-- An étale atlas of a presheaf over `S'` base changes to an étale atlas of its restriction to a
smaller base `S`, represented by an object of the site over `S` sitting in a Cartesian square over
the original atlas. The comparison isomorphism acts on a section by composing with the horizontal
edge of that square. -/
private theorem exists_relocalizeRestrict_atlas (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (U : BigFppfOver B S' hS')
    (q : yoneda.obj U ⟶ F)
    (hqS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf q)
    (hqE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf q) :
    ∃ (UB : BigFppfOver B S hS) (p : UB.left ⟶ U.left)
      (iso : yoneda.obj UB ≅ (OverShriek.relocalizeRestrict g).obj (yoneda.obj U)),
      IsPullback (B.inclusion.map p) (B.inclusion.map UB.hom) (B.inclusion.map U.hom)
          (B.inclusion.map g) ∧
        (∀ (T : BigFppfOver B S hS) (t : T ⟶ UB),
          (iso.hom.app (op T) t).left = t.left ≫ p) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (iso.hom ≫ (OverShriek.relocalizeRestrict g).map q) ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (iso.hom ≫ (OverShriek.relocalizeRestrict g).map q) := by
  have _ : HasPullbacks B.Schemes := inferInstance
  exact ⟨(Over.pullback g).obj U, pullback.fst U.hom g, OverShriek.restrictYonedaIso g U,
    IsPullback.map B.inclusion (IsPullback.of_hasPullback U.hom g),
    fun T t ↦ OverShriek.restrictYonedaIso_hom_app_left g U T t,
    presheaf_relocalizeRestrict_atlas B S S' hS hS' g _
        MorphismProperty.IsStableUnderBaseChange.respectsIso U q hqS _ _,
    presheaf_relocalizeRestrict_atlas B S S' hS hS' g _ respectsIso_etale U q hqE _ _⟩

/-- If an object of the site over `S` sits in a Cartesian square over an object of the site over
`S'`, then the presheaf it represents is the restriction of the presheaf represented by the latter,
and the comparison isomorphism acts by composing with the horizontal edge. -/
private theorem exists_isIso_relocalizeRestrictYoneda (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (U : BigFppfOver B S' hS') (UB : BigFppfOver B S hS) (ρ : UB.left ⟶ U.left)
    (hρ : ρ ≫ U.hom = UB.hom ≫ g)
    (hpb : IsPullback (B.inclusion.map ρ) (B.inclusion.map UB.hom) (B.inclusion.map U.hom)
      (B.inclusion.map g)) :
    ∃ iso : yoneda.obj UB ≅ (OverShriek.relocalizeRestrict g).obj (yoneda.obj U),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ UB),
        (iso.hom.app (op T) t).left = t.left ≫ ρ := by
  have _ : HasPullbacks B.Schemes := inferInstance
  have hpbB : IsPullback (B.inclusion.map (pullback.fst U.hom g))
      (B.inclusion.map (pullback.snd U.hom g)) (B.inclusion.map U.hom) (B.inclusion.map g) :=
    IsPullback.map B.inclusion (IsPullback.of_hasPullback U.hom g)
  set n : UB ⟶ (Over.pullback g).obj U :=
    Over.homMk (pullback.lift ρ UB.hom hρ) (pullback.lift_snd _ _ _)
  have hsnd : n.left ≫ pullback.snd U.hom g = UB.hom := pullback.lift_snd _ _ _
  have hfst : n.left ≫ pullback.fst U.hom g = ρ := pullback.lift_fst _ _ _
  have hmap : B.inclusion.map n.left = (hpb.isoIsPullback _ _ hpbB).hom := by
    refine hpbB.hom_ext ?_ ?_
    · rw [← B.inclusion.map_comp, hfst, hpb.isoIsPullback_hom_fst]
    · rw [← B.inclusion.map_comp, hsnd, hpb.isoIsPullback_hom_snd]
  have _ : IsIso (B.inclusion.map n.left) := by rw [hmap]; infer_instance
  have hleft : IsIso n.left := isIso_of_reflects_iso n.left B.inclusion
  have _ : IsIso ((Over.forget (B.obj hS)).map n) := hleft
  have _ : IsIso n := isIso_of_reflects_iso n (Over.forget (B.obj hS))
  refine ⟨yoneda.mapIso (asIso n) ≪≫ OverShriek.restrictYonedaIso g U, fun T t ↦ ?_⟩
  change ((OverShriek.restrictYonedaIso g U).hom.app (op T) (t ≫ n)).left = _
  rw [OverShriek.restrictYonedaIso_hom_app_left, Over.comp_left, Category.assoc, hfst]

/-! ### The descent criterion -/

/-- Let `SE` and `SK` be objects of a big fppf site over `Sk`, with `SK` over `SE`. An open
subspace `V` of the restriction of `X` to `SK` is the base change of an open subspace `VE` of the
restriction of `X` to `SE` as soon as a surjective chart of `VE` coming from an open subobject of
the base-changed atlas base changes to a chart of `V` with the same point set. -/
private theorem subfunctor_eq_relocalizeRestrictSubfunctor (B : BigFppfSite.{u})
    (Sk SE SK : Scheme.{u}) (hk : B.Contains Sk) (hE : B.Contains SE) (hK : B.Contains SK)
    (gE : B.obj hE ⟶ B.obj hk) (gEK : B.obj hK ⟶ B.obj hE) (gK : B.obj hK ⟶ B.obj hk)
    (hgcomp : gEK ≫ gE = gK) (X : (BigFppfOver B Sk hk)ᵒᵖ ⥤ Type u)
    (he : (OverShriek.relocalizeRestrict gEK).obj ((OverShriek.relocalizeRestrict gE).obj X) =
      (OverShriek.relocalizeRestrict gK).obj X)
    (U0 : BigFppfOver B Sk hk) (q0 : yoneda.obj U0 ⟶ X)
    {UE : BigFppfOver B SE hE} {pE : UE.left ⟶ U0.left}
    {isoE : yoneda.obj UE ≅ (OverShriek.relocalizeRestrict gE).obj (yoneda.obj U0)}
    (hisoE : ∀ (T : BigFppfOver B SE hE) (t : T ⟶ UE),
      (isoE.hom.app (op T) t).left = t.left ≫ pE)
    {UK : BigFppfOver B SK hK} {pK : UK.left ⟶ U0.left}
    {isoK : yoneda.obj UK ≅ (OverShriek.relocalizeRestrict gK).obj (yoneda.obj U0)}
    (hisoK : ∀ (T : BigFppfOver B SK hK) (t : T ⟶ UK),
      (isoK.hom.app (op T) t).left = t.left ≫ pK)
    {VE : Subfunctor ((OverShriek.relocalizeRestrict gE).obj X)}
    (hVE : IsOpenSubspace B SE hE VE)
    {V : Subfunctor ((OverShriek.relocalizeRestrict gK).obj X)}
    (hV : IsOpenSubspace B SK hK V)
    {UW : BigFppfOver B SE hE} (iW : UW ⟶ UE)
    {UWK : BigFppfOver B SK hK} (iWK : UWK ⟶ UK) {ρ : UWK.left ⟶ UW.left}
    {jIso : yoneda.obj UWK ≅ (OverShriek.relocalizeRestrict gEK).obj (yoneda.obj UW)}
    (hjIso : ∀ (T : BigFppfOver B SK hK) (t : T ⟶ UWK),
      (jIso.hom.app (op T) t).left = t.left ≫ ρ)
    (factorVE : yoneda.obj UW ⟶ VE.toFunctor)
    (hfactorVE : factorVE ≫ VE.ι =
      yoneda.map iW ≫ isoE.hom ≫ (OverShriek.relocalizeRestrict gE).map q0)
    (hfactorVEpresheaf : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B SE hE)).presheaf factorVE)
    (hbcleft : ρ ≫ iW.left ≫ pE = iWK.left ≫ pK)
    (hrange : Set.range (pointsMap B SK hK (yoneda.obj UWK)
        (yoneda.map iWK ≫ isoK.hom ≫ (OverShriek.relocalizeRestrict gK).map q0)) =
      Set.range (pointsMap B SK hK V.toFunctor V.ι)) :
    Subfunctor.preimage V (eqToHom he) =
      OverShriek.relocalizeRestrictSubfunctor gEK VE := by
  classical
  set e := he
  set Vbase := OverShriek.relocalizeRestrictSubfunctor gEK VE
  have hVbaseAlg : IsAlgebraicSpace B SK hK Vbase.toFunctor :=
    isAlgebraicSpace_relocalizeRestrict B SK SE hK hE gEK VE.toFunctor hVE.1
  have hVbaseOpen : IsOpenSubspace B SK hK Vbase := by
    refine ⟨hVbaseAlg, ?_⟩
    have _ : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B SK hK)).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage _ _
    exact OverShriek.relative_relocalizeRestrict_map gEK
      (inverseImage_restrictReindexSnd B SK SE hK hE gEK
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})) hVE.2
  set fVK := jIso.hom ≫ (OverShriek.relocalizeRestrict gEK).map factorVE with hfVKdef
  have hfVKsurj : Function.Surjective (pointsMap B SK hK (yoneda.obj UWK) fVK) := by
    exact (surjective_iff_surjective_pointsMap B SK hK Vbase.toFunctor hVbaseAlg UWK fVK).1
      (presheaf_relocalizeRestrict_atlas B SK SE hK hE gEK _
        MorphismProperty.IsStableUnderBaseChange.respectsIso UW factorVE hfactorVEpresheaf _ jIso)
  have hcomparison : fVK ≫ Vbase.ι ≫ eqToHom e =
      yoneda.map iWK ≫ isoK.hom ≫ (OverShriek.relocalizeRestrict gK).map q0 := by
    have hTfun : Over.map gEK ⋙ Over.map gE = Over.map gK := by
      rw [← Over.mapComp_eq, hgcomp]
    have hT : (Over.map gE).obj ((Over.map gEK).obj UWK) = (Over.map gK).obj UWK :=
      congrArg (fun Φ : Over (B.obj hK) ⥤ Over (B.obj hk) ↦ Φ.obj UWK) hTfun
    have hstep : fVK ≫ Vbase.ι = jIso.hom ≫ (OverShriek.relocalizeRestrict gEK).map
        (yoneda.map iW ≫ isoE.hom ≫ (OverShriek.relocalizeRestrict gE).map q0) := by
      change (jIso.hom ≫ (OverShriek.relocalizeRestrict gEK).map factorVE) ≫
        (OverShriek.relocalizeRestrict gEK).map VE.ι = _
      rw [Category.assoc, ← Functor.map_comp, hfactorVE]
    have hkey : (jIso.hom ≫ (OverShriek.relocalizeRestrict gEK).map
        (yoneda.map iW ≫ isoE.hom ≫ (OverShriek.relocalizeRestrict gE).map q0)) ≫ eqToHom e =
        yoneda.map iWK ≫ isoK.hom ≫ (OverShriek.relocalizeRestrict gK).map q0 := by
      refine OverShriek.natTrans_eq_of_app_id_heq e _ _ ?_
      have hLapp : (jIso.hom ≫ (OverShriek.relocalizeRestrict gEK).map
          (yoneda.map iW ≫ isoE.hom ≫
            (OverShriek.relocalizeRestrict gE).map q0)).app (op UWK) (𝟙 UWK) =
          q0.app (op ((Over.map gE).obj ((Over.map gEK).obj UWK)))
            (isoE.hom.app (op ((Over.map gEK).obj UWK))
              (jIso.hom.app (op UWK) (𝟙 UWK) ≫ iW)) := rfl
      have hRapp : (yoneda.map iWK ≫ isoK.hom ≫
          (OverShriek.relocalizeRestrict gK).map q0).app (op UWK) (𝟙 UWK) =
          q0.app (op ((Over.map gK).obj UWK)) (isoK.hom.app (op UWK) iWK) :=
        OverShriek.yoneda_map_comp_app_id iWK _
      rw [hLapp, hRapp]
      refine OverShriek.natTrans_app_heq q0 (congrArg op hT) ?_
      refine OverShriek.overHom_heq_of_left hT _ _ (heq_of_eq ?_)
      rwa [hisoE, hisoK, Over.comp_left, hjIso, Over.id_left, Category.id_comp, Category.assoc]
    exact (Category.assoc _ _ _).symm.trans (hstep ▸ hkey)
  have hfinal : Set.range (pointsMap B SK hK
      ((OverShriek.relocalizeRestrict gEK).obj VE.toFunctor) (Vbase.ι ≫ eqToHom e)) =
      Set.range (pointsMap B SK hK V.toFunctor V.ι) := by
    have h₁ := range_pointsMap_comp B SK hK fVK (Vbase.ι ≫ eqToHom e)
    rw [hfVKsurj.range_eq, Set.image_univ] at h₁
    rwa [← h₁, hcomparison]
  refine (OverShriek.preimage_eqToHom_eq_iff_eq_transport e Vbase V).mpr ?_
  refine subfunctor_eq_of_range_pointsMap_eq B SK hK hV
    (isOpenSubspace_transport B SK hK e Vbase hVbaseOpen) ?_
  rw [← range_pointsMap_transport B SK hK e Vbase]
  exact hfinal.symm

/-! ### Descent to a finite subextension -/

/-- Let `X` be an algebraic space over a field `k` and let `K/k` be an algebraic field extension. A
quasi-compact open subspace of the base change of `X` to `K` is the base change of a quasi-compact
open subspace of the base change of `X` to a finite subextension of `K/k`. -/
@[stacks 0A15 "part (1)"]
theorem exists_finite_subextension_descending_isQuasiCompact_open (B : BigFppfSite.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (V : Subfunctor ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))
    (hV : IsOpenSubspace B (Spec (.of K)) hK V)
    (hVqc : IsQuasiCompactSpace B (Spec (.of K)) hK V.toFunctor) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (hE : B.Contains (Spec (.of E)))
      (V' : Subfunctor
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X)),
      IsOpenSubspace B (Spec (.of E)) hE V' ∧
        IsQuasiCompactSpace B (Spec (.of E)) hE V'.toFunctor ∧
        Subfunctor.preimage V
            (eqToHom (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X)) =
          OverShriek.relocalizeRestrictSubfunctor (fieldExtensionMap B E K hE hK) V' := by
  classical
  revert V
  set gK := fieldExtensionMap B k K hk hK
  intro V hV hVqc
  obtain ⟨U0, q0, hq0S, hq0E⟩ := hX.exists_atlas
  obtain ⟨UK, pK, isoK, hpbK, hisoK, hqKS, hqKE⟩ :=
    exists_relocalizeRestrict_atlas B (Spec (.of K)) (Spec (.of k)) hK hk gK U0 q0 hq0S hq0E
  have hXK : IsAlgebraicSpace B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict gK).obj X) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk gK X hX
  obtain ⟨W, hWopen, hWcompact, hWimage⟩ :=
    exists_isCompact_isOpen_atlas_image B (Spec (.of K)) hK hXK UK
      (isoK.hom ≫ (OverShriek.relocalizeRestrict gK).map q0) hqKS hqKE V hV hVqc
  have hmapK : B.inclusion.map gK = spectrumMap k K := map_fieldExtensionMap B k K hk hK
  have hpbK' : IsPullback (B.inclusion.map pK) (B.inclusion.map UK.hom)
      (B.inclusion.map U0.hom) (spectrumMap k K) := by
    rwa [← hmapK]
  obtain ⟨E, hEfin, W', hW'compact, r, hrFst, hrSnd, hrPre⟩ :=
    exists_finite_subextension_descending_isCompact_open
      (B.inclusion.obj U0.left) (B.inclusion.map U0.hom)
      (hpbK'.isoPullback.inv ⁻¹ᵁ (⟨W, hWopen⟩ :
        ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj UK).Opens))
      (hpbK'.isoPullback.inv.homeomorph.isCompact_preimage.mpr hWcompact)
  have _ : FiniteDimensional k E := hEfin
  have hE : B.Contains (Spec (.of E)) := contains_specIntermediateField B hK E
  refine ⟨E, hEfin, hE, ?_⟩
  set gE := fieldExtensionMap B k E hk hE
  set gEK := fieldExtensionMap B E K hE hK with hgEKdef
  have hgcomp : gEK ≫ gE = gK := fieldExtensionMap_comp B k E K hk hE hK
  obtain ⟨UE, pE, isoE, hpbE, hisoE, hqES, hqEE⟩ :=
    exists_relocalizeRestrict_atlas B (Spec (.of E)) (Spec (.of k)) hE hk gE U0 q0 hq0S hq0E
  have hXE : IsAlgebraicSpace B (Spec (.of E)) hE
      ((OverShriek.relocalizeRestrict gE).obj X) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of E)) (Spec (.of k)) hE hk gE X hX
  have hmapE : B.inclusion.map gE = spectrumMap k E := map_fieldExtensionMap B k E hk hE
  have hpbE' : IsPullback (B.inclusion.map pE) (B.inclusion.map UE.hom)
      (B.inclusion.map U0.hom) (spectrumMap k E) := by
    rwa [← hmapE]
  obtain ⟨rAtlas, hrAtlasdef⟩ :
      ∃ rAtlas : B.inclusion.obj UK.left ⟶ B.inclusion.obj UE.left,
        rAtlas = hpbK'.isoPullback.hom ≫ r ≫ hpbE'.isoPullback.inv := ⟨_, rfl⟩
  obtain ⟨WE, hWEdef⟩ :
      ∃ WE : ((BigFppfOver.toScheme B (Spec (.of E)) hE).obj UE).Opens,
        WE = hpbE'.isoPullback.hom ⁻¹ᵁ W' := ⟨_, rfl⟩
  have hWEcompact : IsCompact WE.carrier := by
    rw [hWEdef]
    exact hpbE'.isoPullback.hom.homeomorph.isCompact_preimage.mpr hW'compact
  have hrAtlasFst : rAtlas ≫ B.inclusion.map pE = B.inclusion.map pK := by
    rw [hrAtlasdef, Category.assoc, Category.assoc, hpbE'.isoPullback_inv_fst, hrFst,
      hpbK'.isoPullback_hom_fst]
  have hrAtlasOver : rAtlas ≫ B.inclusion.map UE.hom =
      B.inclusion.map UK.hom ≫ B.inclusion.map gEK := by
    rw [hrAtlasdef, Category.assoc, Category.assoc, hpbE'.isoPullback_inv_snd, hrSnd,
      ← Category.assoc, hpbK'.isoPullback_hom_snd, hgEKdef, map_fieldExtensionMap]
    rfl
  have hWpull : rAtlas ⁻¹ᵁ WE = (⟨W, hWopen⟩ :
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj UK).Opens) := by
    have h₁ : hpbE'.isoPullback.inv ⁻¹ᵁ WE = W' := by
      rw [hWEdef, ← Scheme.Hom.comp_preimage, Iso.inv_hom_id]
      exact Scheme.Hom.id_preimage _
    rw [hrAtlasdef, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, h₁, ← hrPre,
      ← Scheme.Hom.comp_preimage, Iso.hom_inv_id]
    exact Scheme.Hom.id_preimage _
  have hWpullSet : rAtlas ⁻¹' WE.carrier = W :=
    (coe_preimage_opens rAtlas WE).symm.trans
      (congrArg (fun T : ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj UK).Opens ↦ T.carrier)
        hWpull)
  obtain ⟨UW, iW, hiWoi, hiWrange, hiWuniv⟩ := exists_restrict_bigFppfOver UE WE
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (Spec (.of E)) hE).map iW) := hiWoi
  have hiWrange' : Set.range ((BigFppfOver.toScheme B (Spec (.of E)) hE).map iW) =
    WE.carrier := hiWrange
  obtain ⟨UWK, iWK, hiWKoi, hiWKrange, -⟩ :=
    exists_restrict_bigFppfOver UK (⟨W, hWopen⟩ :
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj UK).Opens)
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK) := hiWKoi
  have hiWKrange' : Set.range ((BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK) = W :=
    hiWKrange
  obtain ⟨VE, hVE, hVEqc, factorVE, hfactorVE, hfactorVEpresheaf⟩ :=
    exists_isOpenSubspace_isQuasiCompact_image B (Spec (.of E)) hE hXE UE
      (isoE.hom ≫ (OverShriek.relocalizeRestrict gE).map q0) hqEE WE.2 hWEcompact UW iW
      hiWrange'
  refine ⟨VE, hVE, hVEqc, ?_⟩
  obtain ⟨rSite, hrSiteScheme⟩ : ∃ rSite : (Over.map gEK).obj UK ⟶ UE,
      (BigFppfOver.toScheme B (Spec (.of E)) hE).map rSite = rAtlas := by
    refine ⟨Over.homMk (B.inclusion.preimage rAtlas) (B.inclusion.map_injective ?_),
      B.inclusion.map_preimage rAtlas⟩
    rwa [B.inclusion.map_comp, B.inclusion.map_preimage]
  have hfWScheme : (BigFppfOver.toScheme B (Spec (.of E)) hE).map
      ((Over.map gEK).map iWK ≫ rSite) =
      (BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK ≫ rAtlas := by
    rw [Functor.map_comp, hrSiteScheme]
    rfl
  have hfWrange : Set.range ((BigFppfOver.toScheme B (Spec (.of E)) hE).map
      ((Over.map gEK).map iWK ≫ rSite)) ⊆ WE.carrier := by
    rw [hfWScheme, Set.range_subset_iff]
    intro x
    have hx : (BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK x ∈ W :=
      hiWKrange' ▸ Set.mem_range_self x
    rw [← hWpullSet] at hx
    rw [Scheme.Hom.comp_apply]
    exact hx
  obtain ⟨rW, hrW⟩ := hiWuniv ((Over.map gEK).map iWK ≫ rSite) hfWrange
  have hpbAtlas : IsPullback rAtlas (B.inclusion.map UK.hom) (B.inclusion.map UE.hom)
      (B.inclusion.map gEK) := by
    refine IsPullback.of_right ?_ hrAtlasOver hpbE
    rwa [hrAtlasFst, ← B.inclusion.map_comp, hgcomp]
  have hpbOpen : IsPullback ((BigFppfOver.toScheme B (Spec (.of E)) hE).map rW)
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK)
      ((BigFppfOver.toScheme B (Spec (.of E)) hE).map iW) rAtlas := by
    refine IsOpenImmersion.isPullback _ _ _ rAtlas ?_ ?_
    · rw [← hfWScheme, ← hrW, Functor.map_comp]
    · have hoW : ((BigFppfOver.toScheme B (Spec (.of E)) hE).map iW).opensRange = WE :=
        TopologicalSpace.Opens.ext hiWrange'
      have hoWK : ((BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK).opensRange =
          (⟨W, hWopen⟩ : ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj UK).Opens) :=
        TopologicalSpace.Opens.ext hiWKrange'
      rw [hoW, hoWK]
      exact hWpull
  have hpbW : IsPullback (B.inclusion.map rW.left) (B.inclusion.map UWK.hom)
      (B.inclusion.map UW.hom) (B.inclusion.map gEK) := by
    have h := hpbOpen.paste_vert hpbAtlas
    rwa [toScheme_map_comp_hom B _ _ iWK, toScheme_map_comp_hom B _ _ iW] at h
  obtain ⟨jIso, hjIso⟩ :=
    exists_isIso_relocalizeRestrictYoneda B (Spec (.of K)) (Spec (.of E)) hK hE gEK UW UWK
      rW.left (Over.w rW) hpbW
  have hbcleft : rW.left ≫ iW.left ≫ pE = iWK.left ≫ pK := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_comp, B.inclusion.map_comp]
    have h₁ : B.inclusion.map rW.left ≫ B.inclusion.map iW.left =
        (BigFppfOver.toScheme B (Spec (.of K)) hK).map iWK ≫ rAtlas := by
      rw [← B.inclusion.map_comp]
      exact (congrArg B.inclusion.map (congrArg Over.Hom.left hrW)).trans hfWScheme
    rw [← Category.assoc, h₁, Category.assoc, hrAtlasFst]
    rfl
  refine subfunctor_eq_relocalizeRestrictSubfunctor B (Spec (.of k)) (Spec (.of E))
    (Spec (.of K)) hk hE hK gE gEK gK hgcomp X
    (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X) U0 q0 hisoE hisoK hVE hV
    iW iWK hjIso factorVE hfactorVE hfactorVEpresheaf hbcleft ?_
  rwa [range_pointsMap_comp, range_pointsMap_yoneda_eq_preimage, hiWKrange']

end Descent

/-! ### Invariance under an open subgroup of the Galois group -/

section GaloisInvariance

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))

/-- An open subspace of the base change `X_K`, viewed as a subfunctor of the presheaf over `k` on
which the opposite automorphism group acts: the image of the subspace under the lower-shriek
extension along `Spec K ⟶ Spec k`. -/
noncomputable def galoisOpenSubfunctor (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (V : Subfunctor ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) :
    Subfunctor ((OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).obj
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) :=
  Subfunctor.range
    ((OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).map V.ι)

/-- Let `X` be an algebraic space over a field `k` and let `K/k` be a Galois extension. A
quasi-compact open subspace of the base change of `X` to `K` is fixed by an open subgroup of
`Gal(K/k)`. -/
@[stacks 0A15 "part (2)"]
theorem exists_open_subgroup_fixing_isQuasiCompact_open [IsGalois k K]
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (V : Subfunctor ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))
    (hV : IsOpenSubspace B (Spec (.of K)) hK V)
    (hVqc : IsQuasiCompactSpace B (Spec (.of K)) hK V.toFunctor) :
    ∃ H : Subgroup Gal(K/k), IsOpen (H : Set Gal(K/k)) ∧
      ∀ σ : Gal(K/k), σ ∈ H →
        Subfunctor.preimage (galoisOpenSubfunctor B k K hk hK X V)
            ((galoisActionOnBaseChange B k K hk hK X).ρ (MulOpposite.op σ)).asHom =
          galoisOpenSubfunctor B k K hk hK X V := by
  classical
  have _ : Algebra.IsAlgebraic k K := inferInstance
  obtain ⟨E, hEfin, hE, V', hV'open, hV'qc, hdesc⟩ :=
    exists_finite_subextension_descending_isQuasiCompact_open B k K hk hK X hX V hV hVqc
  have _ : FiniteDimensional k E := hEfin
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun σ hσ ↦ ?_⟩
  have key := OverShriek.mem_range_relocalize_congr (fieldExtensionMap B k K hk hK)
    (fieldExtensionMap B E K hE hK)
    (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X) V' V hdesc
  refine Subfunctor.ext (funext fun W ↦ ?_)
  change ((galoisActionOnBaseChange B k K hk hK X).ρ (MulOpposite.op σ)).asHom.app W ⁻¹'
      (Subfunctor.range ((OverShriek.relocalizePresheafFunctor
        (fieldExtensionMap B k K hk hK)).map V.ι)).obj W =
    (Subfunctor.range ((OverShriek.relocalizePresheafFunctor
      (fieldExtensionMap B k K hk hK)).map V.ι)).obj W
  refine Set.ext fun x ↦ ?_
  rw [Set.mem_preimage]
  refine key W _ x ?_
    (galoisActionOnBaseChange_ρ_app_snd B k K hk hK X (MulOpposite.op σ) W x)
  rw [galoisActionOnBaseChange_ρ_app_fst B k K hk hK X (MulOpposite.op σ) W x,
    Category.assoc, MulOpposite.unop_op,
    siteMapAlgAut_comp_fieldExtensionMap_of_mem_fixingSubgroup B hK E hE σ hσ]

end GaloisInvariance

end AlgebraicGeometry.Space

end
